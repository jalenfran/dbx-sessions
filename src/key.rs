//! IDs as u64 keys whose integer order is the byte order of the ID.
//!
//! An ID of at most 9 bytes, every byte in 0x01..=0x7f, packs 7 bits per byte, first
//! byte most significant, zero padded on the right (`pack`). Zero padding sorts before
//! every real byte, so a prefix sorts first, exactly like a byte-wise compare. Every
//! generator ID packs. `pack_word` is the hot path: one 8-byte load, `swar::compress`
//! (proved equal to the byte-wise packing in lean/Sessions/Key.lean) and a validity mask. Anything else is interned and gets a key with the top bit set; those only
//! compare by looking the bytes back up (`Keys::cmp`).

use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Mutex;

use crate::scan::Row;
use crate::swar;

pub const INTERNED: u64 = 1 << 63;
const SHARDS: usize = 64;

/// The packing, one byte at a time: the definition `pack_word` must match.
#[inline(always)]
pub fn pack(b: &[u8]) -> Option<u64> {
    if b.len() > 9 {
        return None;
    }
    let mut k: u64 = 0;
    let mut bad = false;
    for &c in b {
        bad |= c.wrapping_sub(1) >= 0x7f;
        k = (k << 7) | c as u64;
    }
    if bad { None } else { Some(k << (7 * (9 - b.len()))) }
}

/// `pack` of an ID of `len` bytes, given the big-endian word of its first 8 bytes and
/// its 9th byte, each read from a buffer that continues past the ID (any bytes past
/// `len` are ignored).
#[inline(always)]
pub fn pack_word(w: u64, ninth: u8, len: usize) -> Option<u64> {
    if len > 9 {
        return None;
    }
    let n8 = len.min(8) as u32;
    let keep = u64::MAX.checked_shl(64 - 8 * n8).unwrap_or(0);
    let w = w & keep;
    let ninth = if len == 9 { ninth } else { 1 };
    let bad = (w & swar::HI) | (swar::zero_bytes(w) & keep);
    if bad != 0 || ninth.wrapping_sub(1) >= 0x7f {
        return None;
    }
    Some(swar::compress(w) << 7 | (if len == 9 { ninth as u64 } else { 0 }))
}

pub fn unpack(k: u64, out: &mut Vec<u8>) {
    for i in (0..9).rev() {
        let c = ((k >> (7 * i)) & 0x7f) as u8;
        if c == 0 {
            break;
        }
        out.push(c);
    }
}

#[derive(Default)]
struct Shard {
    map: HashMap<Vec<u8>, u64>,
    strs: Vec<Vec<u8>>,
}

/// Packs what packs; interns the rest, sharded so parser threads rarely contend.
pub struct Keys {
    shards: Vec<Mutex<Shard>>,
}

impl Keys {
    pub fn new() -> Self {
        Keys { shards: (0..SHARDS).map(|_| Mutex::default()).collect() }
    }

    #[cfg(test)]
    pub fn key(&self, b: &[u8]) -> u64 {
        match pack(b) {
            Some(k) => k,
            None => self.intern(b),
        }
    }

    /// `key` of field `i` of a scanned row, by the word path.
    #[inline(always)]
    pub fn field<const N: usize>(&self, row: &Row<N>, i: usize) -> u64 {
        match row.pack(i) {
            Some(k) => k,
            None => self.intern(row.get(i)),
        }
    }

    #[cold]
    #[inline(never)]
    fn intern(&self, b: &[u8]) -> u64 {
        let h = b.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &c| (h ^ c as u64).wrapping_mul(0x100_0000_01b3));
        let s = (h >> 58) as usize;
        let mut sh = self.shards[s].lock().unwrap();
        if let Some(&k) = sh.map.get(b) {
            return k;
        }
        let k = INTERNED | (s as u64) << 40 | sh.strs.len() as u64;
        sh.strs.push(b.to_vec());
        sh.map.insert(b.to_vec(), k);
        k
    }

    pub fn bytes(&self, k: u64, out: &mut Vec<u8>) {
        if k & INTERNED == 0 {
            unpack(k, out);
        } else {
            let sh = self.shards[((k >> 40) & 0x3f) as usize].lock().unwrap();
            out.extend_from_slice(&sh.strs[(k & 0xff_ffff_ffff) as usize]);
        }
    }

    /// True once any ID failed to pack: from then on order needs `cmp`.
    pub fn any_interned(&self) -> bool {
        self.shards.iter().any(|s| !s.lock().unwrap().strs.is_empty())
    }

    pub fn cmp(&self, a: u64, b: u64) -> Ordering {
        if (a | b) & INTERNED == 0 {
            return a.cmp(&b);
        }
        let (mut x, mut y) = (Vec::new(), Vec::new());
        self.bytes(a, &mut x);
        self.bytes(b, &mut y);
        x.cmp(&y)
    }
}

/// Open-addressing u64 -> V table, linear probing, built once and then read-only.
/// `u64::MAX` marks an empty slot; no key can be it (packed keys have the top bit
/// clear, interned keys have bits 46..62 clear).
pub struct Table<V: Copy> {
    slots: Vec<(u64, V)>,
    shift: u32,
}

impl<V: Copy + Default> Table<V> {
    pub fn new(n: usize) -> Self {
        let cap = (n * 2).next_power_of_two().max(16);
        Table { slots: vec![(u64::MAX, V::default()); cap], shift: 64 - cap.trailing_zeros() }
    }

    #[inline(always)]
    pub fn slot(&self, k: u64) -> usize {
        (k.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> self.shift) as usize
    }

    pub fn insert(&mut self, k: u64, v: V) {
        let mask = self.slots.len() - 1;
        let mut i = self.slot(k);
        loop {
            let s = &mut self.slots[i];
            if s.0 == u64::MAX || s.0 == k {
                *s = (k, v);
                return;
            }
            i = (i + 1) & mask;
        }
    }

    #[inline(always)]
    pub fn get(&self, k: u64) -> Option<V> {
        let mask = self.slots.len() - 1;
        let mut i = self.slot(k);
        loop {
            let s = self.slots[i];
            if s.0 == k {
                return Some(s.1);
            }
            if s.0 == u64::MAX {
                return None;
            }
            i = (i + 1) & mask;
        }
    }

    #[inline(always)]
    pub fn prefetch(&self, k: u64) {
        crate::par::prefetch(&self.slots[self.slot(k)]);
    }
}

/// Keys numbered 0, 1, 2, .. in first-seen order: open addressing that grows, so it
/// stays as small as the number of distinct keys.
pub struct Dense {
    slots: Vec<(u64, u32)>,
    shift: u32,
    pub keys: Vec<u64>,
}

impl Dense {
    pub fn new(n: usize) -> Self {
        let cap = (n * 2).next_power_of_two().max(64);
        Dense { slots: vec![(u64::MAX, 0); cap], shift: 64 - cap.trailing_zeros(), keys: Vec::with_capacity(n) }
    }

    #[inline(always)]
    fn find(&self, k: u64) -> usize {
        let mask = self.slots.len() - 1;
        let mut i = (k.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> self.shift) as usize;
        while self.slots[i].0 != k && self.slots[i].0 != u64::MAX {
            i = (i + 1) & mask;
        }
        i
    }

    #[inline(always)]
    pub fn id(&mut self, k: u64) -> u32 {
        let i = self.find(k);
        if self.slots[i].0 == k {
            return self.slots[i].1;
        }
        let n = self.keys.len() as u32;
        self.slots[i] = (k, n);
        self.keys.push(k);
        if self.keys.len() * 2 > self.slots.len() {
            let cap = self.slots.len() * 2;
            *self = Dense { slots: vec![(u64::MAX, 0); cap], shift: 64 - cap.trailing_zeros(), keys: std::mem::take(&mut self.keys) };
            for (j, &k) in self.keys.iter().enumerate() {
                let i = self.find(k);
                self.slots[i] = (k, j as u32);
            }
        }
        n
    }

    #[inline(always)]
    pub fn get(&self, k: u64) -> Option<u32> {
        let s = self.slots[self.find(k)];
        (s.0 == k).then_some(s.1)
    }
}

/// Exact lookup for the small clean tables (products, campaigns) without allocating.
/// IDs of the form `prefix` + a canonical decimal below `NUM_LIMIT` (no leading zero,
/// at most 7 digits), `prefix` taken from the first row, are numbered: their value
/// indexes `num` directly, a small array instead of a hash probe. Every other ID is
/// in `packed` or, if it does not pack, `other`. Which side an ID belongs to depends
/// on its bytes alone, so a lookup only ever searches the side its key would be on,
/// and `number` is injective (lean/Sessions/Lookup.lean, `number_inj`), so no two IDs
/// share a slot.
pub struct Lookup<V: Copy + Default> {
    prefix: Vec<u8>,
    num: Vec<Option<V>>,
    packed: Table<V>,
    other: HashMap<Vec<u8>, V>,
}

const NUM_LIMIT: u32 = 1 << 22;

impl<V: Copy + Default> Lookup<V> {
    pub fn new(rows: &[(&[u8], V)]) -> Self {
        let prefix = rows.first().map_or(&b""[..], |r| {
            let d = r.0.iter().rev().take_while(|c| c.is_ascii_digit()).count();
            &r.0[..r.0.len() - d]
        });
        let mut l = Lookup { prefix: prefix.to_vec(), num: Vec::new(), packed: Table::new(rows.len()), other: HashMap::new() };
        for &(b, v) in rows {
            if let Some(n) = l.number(b) {
                let n = n as usize;
                if l.num.len() <= n {
                    l.num.resize(n + 1, None);
                }
                l.num[n] = Some(v);
                continue;
            }
            match pack(b) {
                Some(k) => l.packed.insert(k, v),
                None => {
                    l.other.insert(b.to_vec(), v);
                }
            }
        }
        l
    }

    /// The number of a numbered ID, None for any other.
    #[inline(always)]
    fn number(&self, b: &[u8]) -> Option<u32> {
        let p = self.prefix.len();
        let d = b.get(p..)?;
        if d.is_empty() || d.len() > 7 || (d[0] == b'0' && d.len() > 1) || b[..p] != self.prefix[..] {
            return None;
        }
        let mut v = 0u32;
        for &c in d {
            let x = c.wrapping_sub(b'0');
            if x >= 10 {
                return None;
            }
            v = v * 10 + x as u32;
        }
        (v < NUM_LIMIT).then_some(v)
    }

    #[inline(always)]
    pub fn field<const N: usize>(&self, row: &Row<N>, i: usize) -> Option<V> {
        if let Some(n) = self.number(row.get(i)) {
            return self.num.get(n as usize).copied().flatten();
        }
        match row.pack(i) {
            Some(k) => self.packed.get(k),
            None => self.other.get(row.get(i)).copied(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order_and_roundtrip() {
        let ids: &[&[u8]] = &[b"", b"u", b"u1", b"u10", b"u2", b"U9", b" u1", b"u1 ", b"uzzzzzzzz", b"\tA", b"\x7f", b"\x01"];
        for a in ids {
            for b in ids {
                assert_eq!(pack(a).unwrap().cmp(&pack(b).unwrap()), a.cmp(b), "{a:?} {b:?}");
            }
            let mut v = Vec::new();
            unpack(pack(a).unwrap(), &mut v);
            assert_eq!(&v[..], *a);
        }
        for bad in [&b"u123456789"[..], b"\x00", b"a\x80", "é".as_bytes()] {
            assert!(pack(bad).is_none(), "{bad:?}");
        }
        let k = Keys::new();
        let (a, b, c) = (k.key(b"u1"), k.key(b"u1234567890"), k.key("ü".as_bytes()));
        assert_eq!(k.key(b"u1234567890"), b);
        assert!(k.cmp(a, b).is_lt() && k.cmp(b, c).is_lt() && k.cmp(c, a).is_gt());
        let mut v = Vec::new();
        k.bytes(b, &mut v);
        assert_eq!(v, b"u1234567890");
    }

    #[test]
    fn word_path_matches() {
        let mut r: u64 = 3;
        let alphabet = b"\x00\x01az09 \x7f\x80\xff\"u";
        for _ in 0..1_000_000 {
            r = r.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let len = (r >> 59) as usize % 12;
            let mut buf = [0u8; 16];
            for (i, c) in buf.iter_mut().enumerate() {
                let x = r.rotate_left(5 * i as u32) ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
                *c = if x & 3 == 0 { alphabet[(x >> 8) as usize % alphabet.len()] } else { b'a' + (x >> 16) as u8 % 26 };
            }
            let w = u64::from_be_bytes(buf[..8].try_into().unwrap());
            assert_eq!(pack_word(w, buf[8], len), pack(&buf[..len]), "{:?}", &buf[..len]);
        }
    }

    #[test]
    fn lookup_matches_hashmap() {
        let mut r: u64 = 7;
        let mut next = || {
            r = r.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            r >> 33
        };
        let alphabet = b"p0123456789_q";
        let mut ids: Vec<Vec<u8>> = vec![b"p".to_vec(), b"p0".to_vec(), b"p00".to_vec(), b"p01".to_vec(), b"".to_vec()];
        for _ in 0..20_000 {
            let len = next() as usize % 10;
            let mut id = if next() % 4 != 0 { b"p".to_vec() } else { Vec::new() };
            id.extend((0..len).map(|_| alphabet[next() as usize % alphabet.len()]));
            ids.push(id);
        }
        let (table, probes) = ids.split_at(ids.len() / 2);
        let mut table = table.to_vec();
        table.sort();
        table.dedup();
        let rows: Vec<(&[u8], u32)> = table.iter().enumerate().map(|(i, b)| (&b[..], i as u32)).collect();
        let want: HashMap<&[u8], u32> = rows.iter().copied().collect();
        let l = Lookup::new(&rows);
        for id in table.iter().chain(probes) {
            let mut buf = id.clone();
            buf.extend_from_slice(b",x\n");
            let buf = crate::scan::padded(&buf);
            let mut got = None;
            crate::scan::lines::<2, _>(&buf, id.len() + 3, |row| got = Some(l.field(row, 0)));
            if let Some(got) = got {
                assert_eq!(got, want.get(&id[..]).copied(), "{:?}", String::from_utf8_lossy(id));
            }
        }
    }

    #[test]
    fn table() {
        let mut t: Table<u32> = Table::new(1000);
        for i in 0..1000u64 {
            t.insert(i * 7919, i as u32);
        }
        for i in 0..1000u64 {
            assert_eq!(t.get(i * 7919), Some(i as u32));
            assert_eq!(t.get(i * 7919 + 1), None);
        }
    }
}
