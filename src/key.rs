//! IDs as u64 keys whose integer order is the byte order of the ID.
//!
//! An ID of at most 9 bytes, every byte in 0x01..=0x7f, packs 7 bits per byte, first
//! byte most significant, zero padded on the right (`pack`). Zero padding sorts before
//! every real byte, so a prefix sorts first, exactly like a byte-wise compare
//! (lean/Sessions/Key.lean proves order preservation and injectivity). Every generator
//! ID packs. Anything else is interned and gets a key with the top bit set; those only
//! compare by looking the bytes back up (`Keys::cmp`).

use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Mutex;

pub const INTERNED: u64 = 1 << 63;
const SHARDS: usize = 64;

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

    #[inline(always)]
    pub fn key(&self, b: &[u8]) -> u64 {
        match pack(b) {
            Some(k) => k,
            None => self.intern(b),
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

/// Exact lookup for the small clean tables (products, campaigns) without allocating:
/// packed keys in a `Table`, unpackable ones by their bytes.
pub struct Lookup<V: Copy + Default> {
    packed: Table<V>,
    other: HashMap<Vec<u8>, V>,
}

impl<V: Copy + Default> Lookup<V> {
    pub fn new(rows: &[(&[u8], V)]) -> Self {
        let mut l = Lookup { packed: Table::new(rows.len()), other: HashMap::new() };
        for &(b, v) in rows {
            match pack(b) {
                Some(k) => l.packed.insert(k, v),
                None => {
                    l.other.insert(b.to_vec(), v);
                }
            }
        }
        l
    }

    #[inline(always)]
    pub fn get(&self, b: &[u8]) -> Option<V> {
        match pack(b) {
            Some(k) => self.packed.get(k),
            None => self.other.get(b).copied(),
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
