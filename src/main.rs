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
mod swar;
mod ts;

use std::fs::File;
use std::os::unix::fs::FileExt;
use std::path::{Path, PathBuf};
use std::time::Instant;

use key::{Dense, Keys, Lookup, Table};
use parquet::{Column, Values};
use ts::DAY;

const GAP: i64 = 30 * ts::MIN;
const REACH: i64 = 7 * DAY;
const LATE: i64 = DAY;

const PURCHASE: u8 = 2;

/// How times and price + category are stored. Times are offsets from `window_start -
/// 7 days`, where every valid click and event lies. A price of 0 marks a view or a cart
/// (a purchase costs at least 1), so the price doubles as the type. `Narrow` packs an
/// event into 16 bytes and fits windows up to 42 days and up to 256 categories, every
/// generated dataset; `Wide` takes anything else.
trait Rec: Copy + Send + Sync + 'static {
    type T: Copy + Ord + Send + Sync;
    type P: Copy + Eq + Send + Sync;
    /// `P` of a copy that failed validation.
    const BAD: Self::P;
    fn t(off: i64) -> Self::T;
    fn off(t: Self::T) -> i64;
    fn pc(price: u32, cat: u16) -> Self::P;
    fn price(p: Self::P) -> u32;
    fn cat(p: Self::P) -> usize;
}

/// u32 milliseconds, and `price | cat << 24`: both come back exactly and no real value
/// is BAD (lean/Sessions/Pack.lean, `roundtrip`).
#[derive(Clone, Copy)]
struct Narrow;
impl Rec for Narrow {
    type T = u32;
    type P = u32;
    const BAD: u32 = u32::MAX;
    #[inline(always)]
    fn t(off: i64) -> u32 {
        off as u32
    }
    #[inline(always)]
    fn off(t: u32) -> i64 {
        t as i64
    }
    #[inline(always)]
    fn pc(price: u32, cat: u16) -> u32 {
        price | (cat as u32) << 24
    }
    #[inline(always)]
    fn price(p: u32) -> u32 {
        p & 0xff_ffff
    }
    #[inline(always)]
    fn cat(p: u32) -> usize {
        (p >> 24) as usize
    }
}

#[derive(Clone, Copy)]
struct Wide;
impl Rec for Wide {
    type T = i64;
    type P = (u32, u16);
    const BAD: (u32, u16) = (u32::MAX, 0);
    fn t(off: i64) -> i64 {
        off
    }
    fn off(t: i64) -> i64 {
        t
    }
    fn pc(price: u32, cat: u16) -> (u32, u16) {
        (price, cat)
    }
    fn price(p: (u32, u16)) -> u32 {
        p.0
    }
    fn cat(p: (u32, u16)) -> usize {
        p.1 as usize
    }
}

/// An event copy as parsed. `pc` is BAD unless it passed validation (rules 3 and 4),
/// done up front; the copy still competes in dedup (rule 2) when it is not ok.
#[derive(Clone, Copy)]
struct Raw<R: Rec> {
    eid: u64,
    ingest: i64,
    uid: u64,
    t: R::T,
    pc: R::P,
}

/// A surviving event, keyed by its person.
#[derive(Clone, Copy)]
struct Ev<R: Rec> {
    person: u64,
    t: R::T,
    pc: R::P,
}

/// A valid click. Copies of a click are identical, so they are not deduped: an extra
/// copy never changes which campaign credits a session (same ts, same click_id, same
/// campaign) and a campaign assists a session once however many clicks qualify.
#[derive(Clone, Copy)]
struct Click<R: Rec> {
    person: u64,
    cid: u64,
    t: R::T,
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
    bytes: u64,
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
        let bytes = chunks.iter().map(|c| c.2 - c.1).sum();
        Input { files, chunks, bytes }
    }

    /// Reads chunk `i` into `buf`, zero padded for `scan::lines`; returns its length.
    fn read(&self, i: usize, buf: &mut Vec<u8>) -> usize {
        let (f, s, e) = self.chunks[i];
        let n = (e - s) as usize;
        let padded = n.div_ceil(scan::BLOCK) * scan::BLOCK + scan::SLACK;
        if buf.len() < padded {
            buf.resize(padded, 0);
        }
        self.files[f as usize].read_exact_at(&mut buf[..n], s).expect("read input");
        buf[n..].fill(0);
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
    // At most 2 * pairs IDs, and `Table::new(n)` has room for 2 * n.
    let mut node: Table<u32> = Table::new(pairs.len());
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

struct Parse<R: Rec> {
    buf: Vec<u8>,
    ev: Vec<Vec<Raw<R>>>,
    /// Valid clicks by person bucket, and one chunk's clicks under their user_id.
    ck: Vec<Vec<Click<R>>>,
    pend: Vec<Click<R>>,
}

/// Stage 2, per thread: person buckets of events, and the dedup scratch, reused
/// across event_id buckets so its tables are not faulted in afresh each time.
struct Dedup<R: Rec> {
    ev: Vec<Vec<Ev<R>>>,
    slots: Vec<(u64, u32)>,
    kept: Vec<Ev<R>>,
    ingest: Vec<i64>,
}

/// Stage 3, per thread: credited sessions, purchasing sessions and revenue per
/// (campaign, day) in `camp`; assists apart in `assist`, small enough to stay cached;
/// and each campaign's open assist interval (`NONE` when closed).
struct Acc {
    camp: Vec<[u64; 4]>,
    assist: Vec<u32>,
    open: Vec<(i64, i64)>,
    opened: Vec<u32>,
}

const NONE: i64 = i64::MIN;

/// What `run` needs from the small tables.
struct Ctx {
    t0: Instant,
    data: PathBuf,
    out: PathBuf,
    threads: usize,
    ws: i64,
    we: i64,
    first_day: i64,
    ndays: usize,
    cats: Vec<Vec<u8>>,
    products: Lookup<u16>,
    unknown: u16,
    campaigns: Lookup<u32>,
    crows: Vec<[Vec<u8>; 2]>,
}

fn main() {
    if let Some(p) = std::env::var_os("BENCH_SCAN") {
        let data = std::fs::read(p).unwrap();
        let buf = scan::padded(&data);
        for _ in 0..3 {
            let t = Instant::now();
            let mut c = 0u64;
            scan::events(&buf, data.len(), |r| c += r.len(2) as u64);
            let el = t.elapsed().as_secs_f64();
            eprintln!("scan {:.3}s {:.2} GB/s ({c})", el, data.len() as f64 / el / 1e9);
        }
        return;
    }
    let t0 = Instant::now();
    let env = |k: &str, d: &str| std::env::var(k).unwrap_or_else(|_| d.to_string());
    let data = PathBuf::from(env("DATA_DIR", "/data"));
    let out = PathBuf::from(env("OUTPUT_DIR", "/output"));
    let threads: usize = env("NCPU", "8").parse().unwrap_or(8).clamp(1, 256);

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
    let campaigns: Lookup<u32> =
        Lookup::new(&crows.iter().enumerate().map(|(i, r)| (&r[0][..], i as u32)).collect::<Vec<_>>());

    // SESSIONS_WIDE forces the general layout, for testing it on ordinary data.
    let narrow = cats.len() <= 256 && we - (ws - REACH) <= u32::MAX as i64 && std::env::var_os("SESSIONS_WIDE").is_none();
    let c = Ctx { t0, data, out, threads, ws, we, first_day, ndays, cats, products, unknown, campaigns, crows };
    if narrow { run::<Narrow>(&c) } else { run::<Wide>(&c) }
}

fn run<R: Rec>(c: &Ctx) -> ! {
    let lap = |what: &str| eprintln!("{:>8.3}s  {what}", c.t0.elapsed().as_secs_f64());
    let (data, out, threads, ws, we, first_day, ndays) = (&c.data, &c.out, c.threads, c.ws, c.we, c.first_day, c.ndays);
    let (cats, products, unknown, campaigns, crows) = (&c.cats, &c.products, c.unknown, &c.campaigns, &c.crows);
    let ncamp = crows.len();
    let base = ws - REACH;

    let keys = Keys::new();
    let links = Input::open(&data.join("links"), 4 << 20);
    let pairs: Vec<(u64, u64)> = par::run(
        links.chunks.len(),
        threads,
        Vec::new,
        |buf, i| {
            let n = links.read(i, buf);
            let mut v = Vec::new();
            scan::lines::<2, _>(buf, n, |r| {
                if r.len(0) != 0 && r.len(1) != 0 {
                    v.push((keys.field(r, 0), keys.field(r, 1)));
                }
            });
            v
        },
    )
    .0
    .concat();
    lap("links");

    // ---- 1. parse, while one more thread joins the links into people ----
    let events = Input::open(&data.join("events"), 8 << 20);
    let clicks = Input::open(&data.join("clicks"), 8 << 20);
    // Estimate 75 bytes per event. Smaller event-ID buckets keep dedup tables
    // cache-sized. Larger person buckets reduce spare capacity in the scatter vectors.
    let est = (events.bytes / 75) as usize;
    let nbe = (est / 65_536).next_power_of_two().clamp(threads * 4, 4096);
    let nb = (est / 262_144).next_power_of_two().clamp(threads * 4, 4096);
    let nev = events.chunks.len();
    // Click chunks come after every event chunk has started, by which time the people
    // are usually joined; a click chunk waits for them if not.
    let joined: std::sync::OnceLock<Table<u64>> = std::sync::OnceLock::new();
    const AHEAD: usize = 16;
    let mut parsed = std::thread::scope(|sc| {
        sc.spawn(|| joined.set(people(&keys, &pairs)).ok());
        par::run(
            nev + clicks.chunks.len(),
            threads,
            // Buckets reserved at a little over their expected share, so most never regrow.
            || Parse {
                buf: Vec::new(),
                ev: (0..nbe).map(|_| Vec::with_capacity(est / threads / nbe * 5 / 4)).collect(),
                ck: (0..nb).map(|_| Vec::with_capacity((clicks.bytes / 45) as usize / threads / nb * 5 / 4)).collect(),
                pend: Vec::new(),
            },
            |st, i| {
                if i < nev {
                    let n = events.read(i, &mut st.buf);
                    let Parse { buf, ev, .. } = st;
                    scan::events(buf, n, |f| {
                        if f.len(0) == 0 {
                            return;
                        }
                        let mut r = Raw { eid: keys.field(f, 0), ingest: ts::parse_f1(f.get(3)).unwrap_or(i64::MAX), uid: 0, t: R::t(0), pc: R::BAD };
                        let kind = match f.get(4) {
                            b"view" => Some(0),
                            b"cart" => Some(1),
                            b"purchase" => Some(PURCHASE),
                            _ => None,
                        };
                        if let (Some(t), Some(kind)) = (ts::parse(f.get(2)), kind)
                            && t >= ws
                            && t < we
                            && f.len(1) != 0
                            && f.len(5) != 0
                            && r.ingest.saturating_sub(t) <= LATE
                        {
                            let p = if kind == PURCHASE { price(f.get(6)) } else { Some(0) };
                            if let Some(p) = p {
                                r.t = R::t(t - base);
                                r.pc = R::pc(p, if p != 0 { products.field(f, 5).unwrap_or(unknown) } else { 0 });
                                r.uid = keys.field(f, 1);
                            }
                        }
                        ev[bucket(r.eid, nbe)].push(r);
                    });
                } else {
                    let n = clicks.read(i - nev, &mut st.buf);
                    let Parse { buf, ck, pend, .. } = st;
                    pend.clear();
                    scan::lines::<4, _>(buf, n, |f| {
                        if f.len(0) == 0 || f.len(1) == 0 {
                            return;
                        }
                        let Some(t) = ts::parse(f.get(3)) else { return };
                        if t < ws - REACH || t >= we {
                            return;
                        }
                        let Some(camp) = campaigns.field(f, 2) else { return };
                        pend.push(Click { person: keys.field(f, 1), cid: keys.field(f, 0), t: R::t(t - base), camp });
                    });
                    let persons = joined.wait();
                    for i in 0..pend.len() {
                        if i + AHEAD < pend.len() {
                            persons.prefetch(pend[i + AHEAD].person);
                        }
                        let mut c = pend[i];
                        c.person = persons.get(c.person).unwrap_or(c.person);
                        ck[bucket(c.person, nb)].push(c);
                    }
                }
            },
        )
        .1
    });
    let persons = joined.into_inner().expect("people");
    let person = |uid: u64| persons.get(uid).unwrap_or(uid);
    let clicks_by: Vec<Vec<Vec<Click<R>>>> = parsed.iter_mut().map(|p| std::mem::take(&mut p.ck)).collect();
    lap("parse");

    // ---- 2. dedup on event_id, then person lookup and scatter by person ----
    // Each event_id bucket's parts are taken out and freed once deduped, and the person
    // buckets grow as they fill instead of being reserved up front, so the allocator
    // can hand them the memory the parts leave behind.
    let raws: Vec<Vec<std::sync::Mutex<Vec<Raw<R>>>>> =
        parsed.into_iter().map(|p| p.ev.into_iter().map(std::sync::Mutex::new).collect()).collect();
    let (_, deduped) = par::run(
        nbe,
        threads,
        || Dedup {
            ev: (0..nb).map(|_| Vec::new()).collect(),
            slots: Vec::new(),
            kept: Vec::new(),
            ingest: Vec::new(),
        },
        |st, b| {
            let Dedup { ev: outb, slots, kept, ingest, .. } = st;
            let parts: Vec<Vec<Raw<R>>> = raws.iter().map(|t| std::mem::take(&mut *t[b].lock().unwrap())).collect();
            let n: usize = parts.iter().map(|p| p.len()).sum();
            let cap = (n * 2).next_power_of_two().max(16);
            let shift = 64 - cap.trailing_zeros();
            let mask = cap - 1;
            // One pass: the first copy of an event_id appends its event to `kept` and
            // its slot remembers where; an earlier-ingested copy overwrites it in place.
            // A kept copy that failed validation stays, as BAD, and is dropped below.
            slots.clear();
            slots.resize(cap, (u64::MAX, 0));
            kept.clear();
            ingest.clear();
            let ev = |r: &Raw<R>| Ev { person: r.uid, t: r.t, pc: r.pc };
            let slot = |eid: u64| (eid.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> shift) as usize;
            for part in &parts {
                for (j, r) in part.iter().enumerate() {
                    if let Some(a) = part.get(j + 8) {
                        par::prefetch(&slots[slot(a.eid)]);
                    }
                    let mut s = slot(r.eid);
                    loop {
                        let (k, i) = slots[s];
                        if k == u64::MAX {
                            slots[s] = (r.eid, kept.len() as u32);
                            kept.push(ev(r));
                            ingest.push(r.ingest);
                            break;
                        }
                        if k == r.eid {
                            if r.ingest < ingest[i as usize] {
                                kept[i as usize] = ev(r);
                                ingest[i as usize] = r.ingest;
                            }
                            break;
                        }
                        s = (s + 1) & mask;
                    }
                }
            }
            drop(parts);
            kept.retain(|e| e.pc != R::BAD);
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
    let deduped: Vec<_> = deduped.into_iter().map(|worker| worker.ev).collect();
    lap("dedup");

    // ---- 3. sessions, credit, assists ----
    let interned = keys.any_interned();
    let width = (ncamp + 1) * ndays;
    let organic = ncamp;
    let (rows, accs) = par::run(
        nb,
        threads,
        || Acc { camp: vec![[0u64; 4]; width], assist: vec![0; width], open: vec![(NONE, 0); ncamp], opened: Vec::new() },
        |acc, b| {
            let Acc { camp, assist, open, opened } = acc;
            // Group by person, in no particular person order: number the bucket's people
            // densely, counting-sort events and clicks by that number straight out of the
            // parts, then sort each person's own run by time. Clicks of people with no
            // surviving event credit nothing and are skipped.
            let n_ev: usize = deduped.iter().map(|d| d[b].len()).sum();
            let mut ids = Dense::new(n_ev / 16);
            let mut pid: Vec<u32> = Vec::with_capacity(n_ev);
            for d in &deduped {
                pid.extend(d[b].iter().map(|e| ids.id(e.person)));
            }
            let np = ids.keys.len();
            let mut eoff = vec![0u32; np + 1];
            for &x in &pid {
                eoff[x as usize + 1] += 1;
            }
            for x in 0..np {
                eoff[x + 1] += eoff[x];
            }
            let mut ev: Vec<Ev<R>> = Vec::with_capacity(n_ev);
            {
                let mut at = eoff.clone();
                let out = ev.spare_capacity_mut();
                for (e, &x) in deduped.iter().flat_map(|d| d[b].iter()).zip(&pid) {
                    out[at[x as usize] as usize].write(*e);
                    at[x as usize] += 1;
                }
                // Every slot 0..n_ev was written once: the counts sum to n_ev.
                unsafe { ev.set_len(n_ev) };
            }
            drop(pid);
            let mut cid_of: Vec<u32> = Vec::with_capacity(clicks_by.iter().map(|p| p[b].len()).sum());
            for p in &clicks_by {
                cid_of.extend(p[b].iter().map(|c| ids.get(c.person).unwrap_or(u32::MAX)));
            }
            let mut coff = vec![0u32; np + 1];
            for &x in &cid_of {
                if x != u32::MAX {
                    coff[x as usize + 1] += 1;
                }
            }
            for x in 0..np {
                coff[x + 1] += coff[x];
            }
            let nck = coff[np] as usize;
            let mut ck: Vec<Click<R>> = Vec::with_capacity(nck);
            {
                let mut at = coff.clone();
                let out = ck.spare_capacity_mut();
                for (c, &x) in clicks_by.iter().flat_map(|p| p[b].iter()).zip(&cid_of) {
                    if x != u32::MAX {
                        out[at[x as usize] as usize].write(*c);
                        at[x as usize] += 1;
                    }
                }
                unsafe { ck.set_len(nck) };
            }
            drop(cid_of);
            for x in 0..np {
                let es = &mut ev[eoff[x] as usize..eoff[x + 1] as usize];
                if es.len() > 1 {
                    es.sort_unstable_by_key(|e| e.t);
                }
                let cl = &mut ck[coff[x] as usize..coff[x + 1] as usize];
                if cl.len() > 1 {
                    if interned {
                        cl.sort_unstable_by(|x, y| x.t.cmp(&y.t).then_with(|| keys.cmp(x.cid, y.cid)));
                    } else {
                        cl.sort_unstable_by_key(|c| (c.t, c.cid));
                    }
                }
            }

            let mut users: Vec<UserRow> = Vec::new();
            let mut catrev: Vec<u64> = vec![0; cats.len()];
            let mut touched: Vec<u16> = Vec::new();
            let mut starts: Vec<i64> = Vec::new();
            let mut sday: Vec<u32> = Vec::new();
            let mut day_end: Vec<u32> = Vec::new();

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

            for x in 0..np {
                let p = ids.keys[x];
                let es = &ev[eoff[x] as usize..eoff[x + 1] as usize];
                let cl = &ck[coff[x] as usize..coff[x + 1] as usize];

                starts.clear();
                sday.clear();
                let mut row: Option<UserRow> = None;
                let mut hi = 0usize;
                let mut j = 0usize;
                while j < es.len() {
                    let start = R::off(es[j].t);
                    let day = ((base + start).div_euclid(DAY) - first_day) as u32;
                    if let Some(u) = row.take_if(|u| u.day != day) {
                        users.push(close(u, &mut catrev, &mut touched));
                    }
                    let (mut n, mut rev, mut bought) = (0u32, 0u64, false);
                    let mut last = start;
                    while j < es.len() && R::off(es[j].t) - last <= GAP {
                        let e = es[j];
                        last = R::off(e.t);
                        n += 1;
                        let price = R::price(e.pc);
                        if price != 0 {
                            let c = R::cat(e.pc);
                            rev += price as u64;
                            bought = true;
                            if catrev[c] == 0 {
                                touched.push(c as u16);
                            }
                            catrev[c] += price as u64;
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
                    while hi < cl.len() && R::off(cl[hi].t) <= start {
                        hi += 1;
                    }
                    let mut credited = organic;
                    if hi > 0 && start - R::off(cl[hi - 1].t) <= REACH {
                        let t = cl[hi - 1].t;
                        let mut g = hi - 1;
                        while g > 0 && cl[g - 1].t == t {
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
                // Clicks are in time order, so each campaign's are too: keep one open
                // interval per campaign, extend it while its next click starts inside it,
                // and count it once it is closed.
                let mut flush = |k: u32, lo: i64, hi: i64| {
                    let a = starts.partition_point(|&s| s < lo);
                    let z = starts.partition_point(|&s| s <= hi);
                    let mut q = a;
                    while q < z {
                        let e = (day_end[q] as usize).min(z);
                        assist[k as usize * ndays + sday[q] as usize] += (e - q) as u32;
                        q = e;
                    }
                };
                for x in cl {
                    let (k, t) = (x.camp, R::off(x.t));
                    let o = &mut open[k as usize];
                    if o.0 == NONE {
                        opened.push(k);
                    } else if t <= o.1 {
                        o.1 = t + REACH;
                        continue;
                    } else {
                        flush(k, o.0, o.1);
                    }
                    open[k as usize] = (t, t + REACH);
                }
                for &k in opened.iter() {
                    let (lo, hi) = open[k as usize];
                    flush(k, lo, hi);
                    open[k as usize].0 = NONE;
                }
                opened.clear();
            }
            users
        },
    );
    let accs: Vec<Vec<[u64; 4]>> = accs
        .into_iter()
        .map(|a| {
            let mut c = a.camp;
            for (x, &n) in c.iter_mut().zip(&a.assist) {
                x[3] = n as u64;
            }
            c
        })
        .collect();
    lap("sessions");

    write_outputs(out, threads, &rows, &accs, &keys, cats, crows, first_day, ndays).expect("write outputs");
    lap("written");
    // The OS frees everything faster than our destructors would.
    std::process::exit(0)
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
    // Select widths for the entire table so every part has the same schema.
    let narrow_counts = rows.iter().flatten().all(|u| u.sessions.max(u.events) <= i32::MAX as u32);
    let narrow_revenue = rows.iter().flatten().all(|u| u.revenue <= i32::MAX as u64);
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
                Column { name: "sessions", values: Values::integers(ses, narrow_counts) },
                Column { name: "events", values: Values::integers(evs, narrow_counts) },
                Column { name: "revenue_cents", values: Values::integers(rev, narrow_revenue) },
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
    let narrow = |v: Vec<i64>| {
        let fits = v.iter().all(|&x| i32::try_from(x).is_ok());
        Values::integers(v, fits)
    };
    parquet::write(
        &cd.join("part-000.parquet"),
        &[
            Column { name: "campaign_id", values: cid },
            Column { name: "channel", values: chan },
            Column { name: "day", values: Values::Date(day) },
            Column { name: "sessions", values: narrow(s) },
            Column { name: "purchasing_sessions", values: narrow(ps) },
            Column { name: "revenue_cents", values: narrow(r) },
            Column { name: "assisted_sessions", values: narrow(asst) },
        ],
    )
}
