//! Shopping Sessions (rules.md). Stages, each parallel over NCPU threads:
//!   0. small tables; links -> union-find -> person names
//!   1. parse events and clicks in chunks. Events are scattered by event_id hash,
//!      clicks (already final, see `Click`) by person hash
//!   2. per event_id bucket: keep the smallest-ingest copy, look up its person,
//!      scatter by person hash
//!   3. per person bucket: sessions, credit, assists, daily rows
//!   4. Parquet, one user_daily file per thread
//!
//! Logs go to stderr only.

mod key;
mod par;
mod parquet;
mod scan;
mod ts;

use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::{Path, PathBuf};
use std::time::Instant;

use key::{Keys, Lookup, Table};
use parquet::{Column, Values};
use ts::DAY;

const GAP: i64 = 30 * ts::MIN;
const REACH: i64 = 7 * DAY;
const LATE: i64 = DAY;

const PURCHASE: u8 = 2;

/// An event copy as parsed. `ok` is the result of validation (rules 3 and 4), done
/// up front; the copy still competes in dedup (rule 2) when it is not ok.
#[derive(Clone, Copy)]
struct Raw {
    eid: u64,
    ingest: i64,
    uid: u64,
    ts: i64,
    price: u32,
    cat: u16,
    kind: u8,
    ok: bool,
}

/// A surviving event, keyed by its person.
#[derive(Clone, Copy)]
struct Ev {
    person: u64,
    ts: i64,
    price: u32,
    cat: u16,
    kind: u8,
}

/// A valid click. Copies of a click are identical, so they are not deduped: an extra
/// copy never changes which campaign credits a session (same ts, same click_id, same
/// campaign) and a campaign assists a session once however many clicks qualify.
#[derive(Clone, Copy)]
struct Click {
    person: u64,
    ts: i64,
    cid: u64,
    camp: u32,
}

struct UserRow {
    person: u64,
    day: u32,
    sessions: u32,
    events: u32,
    revenue: u64,
    top: u32,
}

const NO_TOP: u32 = u32::MAX;

#[inline(always)]
fn bucket(k: u64, nb: usize) -> usize {
    (((k.wrapping_mul(0xd6e8_feb8_6659_fd93) >> 32) * nb as u64) >> 32) as usize
}

fn csv_files(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.extension().is_some_and(|x| x == "csv") && p.is_file())
                .collect()
        })
        .unwrap_or_default();
    v.sort();
    v
}

/// Files cut into chunks of whole lines, header excluded, read with pread.
struct Input {
    files: Vec<File>,
    chunks: Vec<(u32, u64, u64)>,
}

impl Input {
    fn open(dir: &Path, target: u64) -> Input {
        let files: Vec<File> = csv_files(dir).iter().map(|p| File::open(p).expect("open input")).collect();
        let mut chunks = Vec::new();
        for (i, f) in files.iter().enumerate() {
            let len = f.metadata().expect("stat").len();
            let mut start = after_newline(f, 0, len);
            while start < len {
                let end = if len - start <= target + target / 2 { len } else { after_newline(f, start + target, len) };
                chunks.push((i as u32, start, end));
                start = end;
            }
        }
        // Biggest first, so the last tasks to start are short.
        chunks.sort_by_key(|c| std::cmp::Reverse(c.2 - c.1));
        Input { files, chunks }
    }

    /// Reads chunk `i` into `buf`, zero padded for `scan::lines`; returns its length.
    fn read(&self, i: usize, buf: &mut Vec<u8>) -> usize {
        let (f, s, e) = self.chunks[i];
        let n = (e - s) as usize;
        let padded = n.div_ceil(scan::BLOCK) * scan::BLOCK;
        if buf.len() < padded {
            buf.resize(padded, 0);
        }
        self.files[f as usize].read_exact_at(&mut buf[..n], s).expect("read input");
        buf[n..padded].fill(0);
        n
    }
}

/// Offset just past the first '\n' at or after `from`, or `len`.
fn after_newline(f: &File, from: u64, len: u64) -> u64 {
    let mut buf = [0u8; 4096];
    let mut at = from;
    while at < len {
        let n = f.read_at(&mut buf, at).expect("read input");
        if n == 0 {
            break;
        }
        if let Some(i) = buf[..n].iter().position(|&c| c == b'\n') {
            return at + i as u64 + 1;
        }
        at += n as u64;
    }
    len
}

/// `price_cents` of a purchase: digits only, 1 to 10,000,000.
#[inline(always)]
fn price(s: &[u8]) -> Option<u32> {
    let mut v: u32 = 0;
    for &c in s {
        let d = c.wrapping_sub(b'0');
        if d >= 10 || v > 10_000_000 {
            return None;
        }
        v = v * 10 + d as u32;
    }
    if (1..=10_000_000).contains(&v) { Some(v) } else { None }
}

fn manifest_ts(json: &str, key: &str) -> i64 {
    let at = json.find(&format!("\"{key}\"")).unwrap_or_else(|| panic!("manifest has no {key}"));
    let rest = &json[at + key.len() + 2..];
    let a = rest.find('"').expect("manifest value") + 1;
    let b = a + rest[a..].find('"').expect("manifest value");
    ts::parse(rest[a..b].as_bytes()).expect("manifest timestamp")
}

/// Union-find over link endpoints; returns uid -> person name for every linked ID
/// whose name is not itself (anything not in the table is its own person).
fn people(keys: &Keys, pairs: &[(u64, u64)]) -> Table<u64> {
    let mut node: Table<u32> = Table::new(pairs.len() * 2);
    let mut key_of: Vec<u64> = Vec::new();
    let mut parent: Vec<u32> = Vec::new();
    fn find(p: &mut [u32], mut x: u32) -> u32 {
        while p[x as usize] != x {
            let up = p[p[x as usize] as usize];
            p[x as usize] = up;
            x = up;
        }
        x
    }
    let mut id = |k: u64, key_of: &mut Vec<u64>, parent: &mut Vec<u32>| -> u32 {
        if let Some(n) = node.get(k) {
            return n;
        }
        let n = key_of.len() as u32;
        node.insert(k, n);
        key_of.push(k);
        parent.push(n);
        n
    };
    for &(a, b) in pairs {
        let x = id(a, &mut key_of, &mut parent);
        let y = id(b, &mut key_of, &mut parent);
        let (rx, ry) = (find(&mut parent, x), find(&mut parent, y));
        if rx != ry {
            parent[rx.max(ry) as usize] = rx.min(ry);
        }
    }
    let n = key_of.len();
    let root: Vec<u32> = (0..n as u32).map(|x| find(&mut parent, x)).collect();
    let mut name: Vec<u64> = vec![u64::MAX; n];
    for x in 0..n {
        let (r, k) = (root[x] as usize, key_of[x]);
        if name[r] == u64::MAX || keys.cmp(k, name[r]).is_lt() {
            name[r] = k;
        }
    }
    let renamed = (0..n).filter(|&x| name[root[x] as usize] != key_of[x]).count();
    let mut t = Table::new(renamed);
    for x in 0..n {
        let nm = name[root[x] as usize];
        if nm != key_of[x] {
            t.insert(key_of[x], nm);
        }
    }
    t
}

struct Parse {
    buf: Vec<u8>,
    ev: Vec<Vec<Raw>>,
    ck: Vec<Vec<Click>>,
}

fn main() {
    let t0 = Instant::now();
    let lap = |what: &str| eprintln!("{:>8.3}s  {what}", t0.elapsed().as_secs_f64());
    let env = |k: &str, d: &str| std::env::var(k).unwrap_or_else(|_| d.to_string());
    let data = PathBuf::from(env("DATA_DIR", "/data"));
    let out = PathBuf::from(env("OUTPUT_DIR", "/output"));
    let threads: usize = env("NCPU", "8").parse().unwrap_or(8).max(1);

    // ---- 0. small tables ----
    let manifest = std::fs::read_to_string(data.join("manifest.json")).expect("manifest.json");
    let (ws, we) = (manifest_ts(&manifest, "window_start"), manifest_ts(&manifest, "window_end"));
    let first_day = ws.div_euclid(DAY);
    let ndays = ((we - 1).div_euclid(DAY) - first_day + 1).max(1) as usize;

    let prows = scan::rows::<2>(&std::fs::read(data.join("products.csv")).unwrap_or_default());
    let mut cats: Vec<Vec<u8>> = prows.iter().map(|r| r[1].clone()).collect();
    cats.push(b"unknown".to_vec());
    cats.sort_unstable();
    cats.dedup();
    assert!(cats.len() < u16::MAX as usize, "too many categories");
    let cat_of = |c: &[u8]| cats.binary_search_by(|x| x[..].cmp(c)).unwrap() as u16;
    let unknown = cat_of(b"unknown");
    let products: Lookup<u16> = Lookup::new(&prows.iter().map(|r| (&r[0][..], cat_of(&r[1]))).collect::<Vec<_>>());

    let crows = scan::rows::<2>(&std::fs::read(data.join("campaigns.csv")).unwrap_or_default());
    let ncamp = crows.len();
    let campaigns: Lookup<u32> =
        Lookup::new(&crows.iter().enumerate().map(|(i, r)| (&r[0][..], i as u32)).collect::<Vec<_>>());

    let keys = Keys::new();
    let links = Input::open(&data.join("links"), 4 << 20);
    let pairs: Vec<(u64, u64)> = par::run(
        links.chunks.len(),
        threads,
        Vec::new,
        |buf, i| {
            let n = links.read(i, buf);
            let mut v = Vec::new();
            scan::lines::<2, _>(buf, n, |f| {
                if !f[0].is_empty() && !f[1].is_empty() {
                    v.push((keys.key(f[0]), keys.key(f[1])));
                }
            });
            v
        },
    )
    .0
    .concat();
    let persons = people(&keys, &pairs);
    let person = |uid: u64| persons.get(uid).unwrap_or(uid);
    lap("links");

    // ---- 1. parse ----
    let nb = (threads * 32).next_power_of_two();
    let events = Input::open(&data.join("events"), 8 << 20);
    let clicks = Input::open(&data.join("clicks"), 8 << 20);
    let nev = events.chunks.len();
    let (_, parsed) = par::run(
        nev + clicks.chunks.len(),
        threads,
        || Parse { buf: Vec::new(), ev: (0..nb).map(|_| Vec::new()).collect(), ck: (0..nb).map(|_| Vec::new()).collect() },
        |st, i| {
            if i < nev {
                let n = events.read(i, &mut st.buf);
                let Parse { buf, ev, .. } = st;
                scan::lines::<7, _>(buf, n, |f| {
                    if f[0].is_empty() {
                        return;
                    }
                    let mut r = Raw {
                        eid: keys.key(f[0]),
                        ingest: ts::parse(f[3]).unwrap_or(i64::MAX),
                        uid: 0,
                        ts: 0,
                        price: 0,
                        cat: 0,
                        kind: 0,
                        ok: false,
                    };
                    let kind = match f[4] {
                        b"view" => Some(0),
                        b"cart" => Some(1),
                        b"purchase" => Some(PURCHASE),
                        _ => None,
                    };
                    if let (Some(t), Some(kind)) = (ts::parse(f[2]), kind)
                        && t >= ws
                        && t < we
                        && !f[1].is_empty()
                        && !f[5].is_empty()
                        && r.ingest.saturating_sub(t) <= LATE
                    {
                        let p = if kind == PURCHASE { price(f[6]) } else { Some(0) };
                        if let Some(p) = p {
                            r.ok = true;
                            r.ts = t;
                            r.kind = kind;
                            r.price = p;
                            r.uid = keys.key(f[1]);
                            r.cat = products.get(f[5]).unwrap_or(unknown);
                        }
                    }
                    ev[bucket(r.eid, nb)].push(r);
                });
            } else {
                let n = clicks.read(i - nev, &mut st.buf);
                let Parse { buf, ck, .. } = st;
                scan::lines::<4, _>(buf, n, |f| {
                    if f[0].is_empty() || f[1].is_empty() {
                        return;
                    }
                    let Some(t) = ts::parse(f[3]) else { return };
                    if t < ws - REACH || t >= we {
                        return;
                    }
                    let Some(camp) = campaigns.get(f[2]) else { return };
                    let p = person(keys.key(f[1]));
                    ck[bucket(p, nb)].push(Click { person: p, ts: t, cid: keys.key(f[0]), camp });
                });
            }
        },
    );
    lap("parse");

    // ---- 2. dedup on event_id, person lookup, scatter by person ----
    let (_, deduped) = par::run(
        nb,
        threads,
        || (0..nb).map(|_| Vec::<Ev>::new()).collect::<Vec<_>>(),
        |outb, b| {
            let parts: Vec<&[Raw]> = parsed.iter().map(|p| &p.ev[b][..]).collect();
            let n: usize = parts.iter().map(|p| p.len()).sum();
            let cap = (n * 2).next_power_of_two().max(16);
            let shift = 64 - cap.trailing_zeros();
            let mask = cap - 1;
            // Slot -> (part << 32 | index) of the earliest copy so far.
            let mut slots = vec![u64::MAX; cap];
            for (pi, part) in parts.iter().enumerate() {
                for (ri, r) in part.iter().enumerate() {
                    let h = (pi as u64) << 32 | ri as u64;
                    let mut s = (r.eid.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> shift) as usize;
                    loop {
                        let o = slots[s];
                        if o == u64::MAX {
                            slots[s] = h;
                            break;
                        }
                        let q = &parts[(o >> 32) as usize][o as u32 as usize];
                        if q.eid == r.eid {
                            if r.ingest < q.ingest {
                                slots[s] = h;
                            }
                            break;
                        }
                        s = (s + 1) & mask;
                    }
                }
            }
            let mut kept: Vec<Ev> = Vec::with_capacity(n);
            for &o in &slots {
                if o != u64::MAX {
                    let r = &parts[(o >> 32) as usize][o as u32 as usize];
                    if r.ok {
                        kept.push(Ev { person: r.uid, ts: r.ts, price: r.price, cat: r.cat, kind: r.kind });
                    }
                }
            }
            drop(slots);
            const AHEAD: usize = 16;
            for i in 0..kept.len() {
                if i + AHEAD < kept.len() {
                    persons.prefetch(kept[i + AHEAD].person);
                }
                let mut e = kept[i];
                e.person = person(e.person);
                outb[bucket(e.person, nb)].push(e);
            }
        },
    );
    let mut parsed = parsed;
    for p in &mut parsed {
        p.ev = Vec::new();
    }
    lap("dedup");

    // ---- 3. sessions, credit, assists ----
    let interned = keys.any_interned();
    let width = (ncamp + 1) * ndays;
    let organic = ncamp;
    let (rows, accs) = par::run(
        nb,
        threads,
        || vec![[0u64; 4]; width],
        |camp, b| {
            let mut ev: Vec<Ev> = Vec::with_capacity(deduped.iter().map(|d| d[b].len()).sum());
            for d in &deduped {
                ev.extend_from_slice(&d[b]);
            }
            let mut ck: Vec<Click> = Vec::with_capacity(parsed.iter().map(|p| p.ck[b].len()).sum());
            for p in &parsed {
                ck.extend_from_slice(&p.ck[b]);
            }
            ev.sort_unstable_by_key(|e| (e.person, e.ts));
            if interned {
                ck.sort_unstable_by(|x, y| (x.person, x.ts).cmp(&(y.person, y.ts)).then_with(|| keys.cmp(x.cid, y.cid)));
            } else {
                ck.sort_unstable_by_key(|c| (c.person, c.ts, c.cid));
            }

            let mut users: Vec<UserRow> = Vec::new();
            let mut catrev: Vec<u64> = vec![0; cats.len()];
            let mut touched: Vec<u16> = Vec::new();
            let mut starts: Vec<i64> = Vec::new();
            let mut sday: Vec<u32> = Vec::new();
            let mut day_end: Vec<u32> = Vec::new();
            let mut by_camp: Vec<(u32, i64)> = Vec::new();

            let close = |u: UserRow, catrev: &mut [u64], touched: &mut Vec<u16>| -> UserRow {
                let mut best: Option<(u64, u16)> = None;
                for &c in touched.iter() {
                    let v = catrev[c as usize];
                    if v > 0 && best.is_none_or(|(bv, bc)| v > bv || (v == bv && c < bc)) {
                        best = Some((v, c));
                    }
                    catrev[c as usize] = 0;
                }
                touched.clear();
                UserRow { top: best.map_or(NO_TOP, |b| b.1 as u32), ..u }
            };

            let (mut i, mut c) = (0usize, 0usize);
            while i < ev.len() {
                let p = ev[i].person;
                let mut e_end = i + 1;
                while e_end < ev.len() && ev[e_end].person == p {
                    e_end += 1;
                }
                while c < ck.len() && ck[c].person < p {
                    c += 1;
                }
                let c0 = c;
                while c < ck.len() && ck[c].person == p {
                    c += 1;
                }
                let cl = &ck[c0..c];
                let es = &ev[i..e_end];
                i = e_end;

                starts.clear();
                sday.clear();
                let mut row: Option<UserRow> = None;
                let mut hi = 0usize;
                let mut j = 0usize;
                while j < es.len() {
                    let start = es[j].ts;
                    let day = (start.div_euclid(DAY) - first_day) as u32;
                    if let Some(u) = row.take_if(|u| u.day != day) {
                        users.push(close(u, &mut catrev, &mut touched));
                    }
                    let (mut n, mut rev, mut bought) = (0u32, 0u64, false);
                    let mut last = start;
                    while j < es.len() && es[j].ts - last <= GAP {
                        let e = es[j];
                        last = e.ts;
                        n += 1;
                        if e.kind == PURCHASE {
                            rev += e.price as u64;
                            bought = true;
                            if catrev[e.cat as usize] == 0 {
                                touched.push(e.cat);
                            }
                            catrev[e.cat as usize] += e.price as u64;
                        }
                        j += 1;
                    }
                    starts.push(start);
                    sday.push(day);
                    let u = row.get_or_insert(UserRow { person: p, day, sessions: 0, events: 0, revenue: 0, top: NO_TOP });
                    u.sessions += 1;
                    u.events += n;
                    u.revenue += rev;

                    // Credit: the latest click at or before the start, within 7 days;
                    // on a tie the smallest click_id, which sorts first.
                    while hi < cl.len() && cl[hi].ts <= start {
                        hi += 1;
                    }
                    let mut credited = organic;
                    if hi > 0 && start - cl[hi - 1].ts <= REACH {
                        let t = cl[hi - 1].ts;
                        let mut g = hi - 1;
                        while g > 0 && cl[g - 1].ts == t {
                            g -= 1;
                        }
                        credited = cl[g].camp as usize;
                    }
                    let a = &mut camp[credited * ndays + day as usize];
                    a[0] += 1;
                    a[1] += bought as u64;
                    a[2] += rev;
                }
                if let Some(u) = row {
                    users.push(close(u, &mut catrev, &mut touched));
                }

                // Assists: campaign k assists the sessions whose start lies in the union
                // of [click.ts, click.ts + 7d] over k's clicks. Merge those intervals,
                // then count the starts in each, split by day.
                if cl.is_empty() {
                    continue;
                }
                day_end.clear();
                day_end.resize(starts.len(), 0);
                let mut q = starts.len();
                while q > 0 {
                    let mut s = q - 1;
                    while s > 0 && sday[s - 1] == sday[q - 1] {
                        s -= 1;
                    }
                    day_end[s..q].fill(q as u32);
                    q = s;
                }
                by_camp.clear();
                by_camp.extend(cl.iter().map(|x| (x.camp, x.ts)));
                by_camp.sort_unstable();
                let mut g = 0;
                while g < by_camp.len() {
                    let k = by_camp[g].0;
                    let lo = by_camp[g].1;
                    let mut hi_t = lo + REACH;
                    g += 1;
                    while g < by_camp.len() && by_camp[g].0 == k && by_camp[g].1 <= hi_t {
                        hi_t = by_camp[g].1 + REACH;
                        g += 1;
                    }
                    let a = starts.partition_point(|&s| s < lo);
                    let z = starts.partition_point(|&s| s <= hi_t);
                    let mut q = a;
                    while q < z {
                        let e = (day_end[q] as usize).min(z);
                        camp[k as usize * ndays + sday[q] as usize][3] += (e - q) as u64;
                        q = e;
                    }
                }
            }
            users
        },
    );
    lap("sessions");

    write_outputs(&out, threads, &rows, &accs, &keys, &cats, &crows, first_day, ndays).expect("write outputs");
    lap("written");
    // The OS frees everything faster than our destructors would.
    std::process::exit(0);
}

#[allow(clippy::too_many_arguments)]
fn write_outputs(
    out: &Path,
    threads: usize,
    rows: &[Vec<UserRow>],
    accs: &[Vec<[u64; 4]>],
    keys: &Keys,
    cats: &[Vec<u8>],
    campaigns: &[[Vec<u8>; 2]],
    first_day: i64,
    ndays: usize,
) -> std::io::Result<()> {
    let (ud, cd) = (out.join("user_daily"), out.join("campaign_daily"));
    std::fs::create_dir_all(&ud)?;
    std::fs::create_dir_all(&cd)?;

    // user_daily: buckets split into `threads` runs of about equal row counts.
    let total: usize = rows.iter().map(|r| r.len()).sum();
    let parts = threads.min(rows.len()).max(1);
    let mut cuts = vec![0usize];
    let mut acc = 0;
    for (b, r) in rows.iter().enumerate() {
        acc += r.len();
        if acc * parts >= total * cuts.len() && cuts.len() < parts {
            cuts.push(b + 1);
        }
    }
    cuts.push(rows.len());
    cuts.dedup();
    let results = par::map(cuts.len() - 1, threads, |p| {
        let group = &rows[cuts[p]..cuts[p + 1]];
        let n: usize = group.iter().map(|r| r.len()).sum();
        let mut uid = Values::strings(false);
        let mut top = Values::strings(true);
        let (mut day, mut ses, mut evs, mut rev) =
            (Vec::with_capacity(n), Vec::with_capacity(n), Vec::with_capacity(n), Vec::with_capacity(n));
        let mut buf = Vec::new();
        for u in group.iter().flatten() {
            buf.clear();
            keys.bytes(u.person, &mut buf);
            uid.push_str(Some(&buf));
            day.push((first_day + u.day as i64) as i32);
            ses.push(u.sessions as i64);
            evs.push(u.events as i64);
            rev.push(u.revenue as i64);
            top.push_str((u.top != NO_TOP).then(|| &cats[u.top as usize][..]));
        }
        parquet::write(
            &ud.join(format!("part-{p:03}.parquet")),
            &[
                Column { name: "user_id", values: uid },
                Column { name: "day", values: Values::Date(day) },
                Column { name: "sessions", values: Values::I64(ses) },
                Column { name: "events", values: Values::I64(evs) },
                Column { name: "revenue_cents", values: Values::I64(rev) },
                Column { name: "top_category", values: top },
            ],
        )
    });
    results.into_iter().collect::<std::io::Result<()>>()?;

    let width = (campaigns.len() + 1) * ndays;
    let mut tot = vec![[0u64; 4]; width];
    for a in accs {
        for (t, x) in tot.iter_mut().zip(a) {
            for k in 0..4 {
                t[k] += x[k];
            }
        }
    }
    let mut cid = Values::strings(false);
    let mut chan = Values::strings(false);
    let (mut day, mut s, mut ps, mut r, mut asst) = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for c in 0..=campaigns.len() {
        for d in 0..ndays {
            let a = tot[c * ndays + d];
            if a[0] == 0 && a[3] == 0 {
                continue;
            }
            let (id, ch) = match campaigns.get(c) {
                Some([id, ch]) => (&id[..], &ch[..]),
                None => (&b"organic"[..], &b"organic"[..]),
            };
            cid.push_str(Some(id));
            chan.push_str(Some(ch));
            day.push((first_day + d as i64) as i32);
            s.push(a[0] as i64);
            ps.push(a[1] as i64);
            r.push(a[2] as i64);
            asst.push(a[3] as i64);
        }
    }
    parquet::write(
        &cd.join("part-000.parquet"),
        &[
            Column { name: "campaign_id", values: cid },
            Column { name: "channel", values: chan },
            Column { name: "day", values: Values::Date(day) },
            Column { name: "sessions", values: Values::I64(s) },
            Column { name: "purchasing_sessions", values: Values::I64(ps) },
            Column { name: "revenue_cents", values: Values::I64(r) },
            Column { name: "assisted_sessions", values: Values::I64(asst) },
        ],
    )
}
