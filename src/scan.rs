//! CSV dialect of rules.md in one pass. Each 64-byte block becomes three bitmasks
//! (`,` `"` `\n`). Walking the set bits of `,` and `\n` finds every field; the
//! quotes in a field are counted with popcount, never visited one by one. A field is
//! fine with no quote, or with exactly two, at its first and last byte. A line is
//! passed to `f` only when it has exactly N fields, all fine.

use crate::key;
use crate::swar;

pub const BLOCK: usize = 64;

#[derive(Clone, Copy)]
struct Masks {
    comma: u64,
    quote: u64,
    nl: u64,
}

const ONES: u64 = 0x0101_0101_0101_0101;
/// Bytes a buffer must hold past its data: whole blocks, plus room for 16-byte loads
/// at any field start (`Row::word`).
pub const SLACK: usize = BLOCK + 16;

#[inline(always)]
#[allow(dead_code)]
fn masks_swar(b: &[u8; BLOCK]) -> Masks {
    let mut m = Masks { comma: 0, quote: 0, nl: 0 };
    for i in 0..8 {
        let w = u64::from_le_bytes(b[i * 8..i * 8 + 8].try_into().unwrap());
        m.comma |= swar::gather(swar::zero_bytes(w ^ (ONES * b',' as u64))) << (i * 8);
        m.quote |= swar::gather(swar::zero_bytes(w ^ (ONES * b'"' as u64))) << (i * 8);
        m.nl |= swar::gather(swar::zero_bytes(w ^ (ONES * b'\n' as u64))) << (i * 8);
    }
    m
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[inline(always)]
fn masks(b: &[u8; BLOCK]) -> Masks {
    use std::arch::x86_64::*;
    unsafe {
        let lo = _mm256_loadu_si256(b.as_ptr() as *const __m256i);
        let hi = _mm256_loadu_si256(b.as_ptr().add(32) as *const __m256i);
        let eq = |c: u8| {
            let v = _mm256_set1_epi8(c as i8);
            let l = _mm256_movemask_epi8(_mm256_cmpeq_epi8(lo, v)) as u32 as u64;
            let h = _mm256_movemask_epi8(_mm256_cmpeq_epi8(hi, v)) as u32 as u64;
            l | h << 32
        };
        Masks { comma: eq(b','), quote: eq(b'"'), nl: eq(b'\n') }
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn masks(b: &[u8; BLOCK]) -> Masks {
    use std::arch::aarch64::*;
    unsafe {
        let weights: [u8; 16] = [1, 2, 4, 8, 16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 64, 128];
        let w = vld1q_u8(weights.as_ptr());
        let v = [
            vld1q_u8(b.as_ptr()),
            vld1q_u8(b.as_ptr().add(16)),
            vld1q_u8(b.as_ptr().add(32)),
            vld1q_u8(b.as_ptr().add(48)),
        ];
        let eq = |c: u8| {
            let s = vdupq_n_u8(c);
            let m0 = vandq_u8(vceqq_u8(v[0], s), w);
            let m1 = vandq_u8(vceqq_u8(v[1], s), w);
            let m2 = vandq_u8(vceqq_u8(v[2], s), w);
            let m3 = vandq_u8(vceqq_u8(v[3], s), w);
            let s01 = vpaddq_u8(m0, m1);
            let s23 = vpaddq_u8(m2, m3);
            let s = vpaddq_u8(s01, s23);
            let s = vpaddq_u8(s, s);
            vgetq_lane_u64(vreinterpretq_u64_u8(s), 0)
        };
        Masks { comma: eq(b','), quote: eq(b'"'), nl: eq(b'\n') }
    }
}

#[cfg(not(any(target_arch = "aarch64", all(target_arch = "x86_64", target_feature = "avx2"))))]
#[inline(always)]
fn masks(b: &[u8; BLOCK]) -> Masks {
    masks_swar(b)
}

/// One well-formed line: N fields as spans of the scanned buffer.
pub struct Row<'a, const N: usize> {
    buf: &'a [u8],
    spans: [(u32, u32); N],
}

impl<'a, const N: usize> Row<'a, N> {
    #[inline(always)]
    pub fn get(&self, i: usize) -> &'a [u8] {
        let (s, e) = self.spans[i];
        // The scanner only makes spans inside buf.
        unsafe { self.buf.get_unchecked(s as usize..e as usize) }
    }

    #[inline(always)]
    pub fn len(&self, i: usize) -> usize {
        (self.spans[i].1 - self.spans[i].0) as usize
    }

    /// `key::pack` of field i, from one 8-byte load (the buffer has SLACK past its data).
    #[inline(always)]
    pub fn pack(&self, i: usize) -> Option<u64> {
        let s = self.spans[i].0 as usize;
        let w = u64::from_be_bytes(self.buf[s..s + 8].try_into().unwrap());
        key::pack_word(w, self.buf[s + 8], self.len(i))
    }
}

/// Calls `f` with every well-formed line of `buf[..len]`. Every byte of `buf` from
/// `len` on is zero, and there are at least `SLACK` of them.
///
/// Two stages per window of blocks. Stage 1 writes the position of every `,` and `\n`
/// to `pos`, and for every `\n` the number of quotes before it to `nls`. Stage 2 takes
/// the lines one by one: a line is well-formed iff its N-th delimiter is its own `\n`
/// (exactly N - 1 commas before it) and its quotes are right. For quotes, call a field
/// *wrapped* when it is at least 2 bytes long and starts and ends with `"`. A wrapped
/// field holds at least 2 quotes, so the line holds at least 2 * wrapped, with equality
/// iff every wrapped field holds exactly its 2 and every other field none: exactly the
/// dialect's rule. So one popcount difference checks the whole line.
#[inline(always)]
pub fn lines<'a, const N: usize, F: FnMut(&Row<'a, N>)>(buf: &'a [u8], len: usize, mut f: F) {
    assert!(N >= 2 && buf.len() >= len + SLACK && len < u32::MAX as usize - 1);
    const WINDOW: usize = 64;
    let mut row = Row { buf, spans: [(0, 0); N] };
    let mut pos: Vec<u32> = Vec::with_capacity(WINDOW * BLOCK / 2);
    let mut nls: Vec<(u32, u32)> = Vec::with_capacity(WINDOW * BLOCK / 8);
    let mut qblock = 0u32;
    // The current line: its start, the quotes before it, and its first delimiter in pos.
    let mut start = 0u32;
    let mut qstart = 0u32;

    let mut line = |pos: &[u32], j: &mut usize, nl: u32, q: u32, start: &mut u32, qstart: &mut u32| {
        let ok = *j + N <= pos.len() && pos[*j + N - 1] == nl;
        if ok {
            let mut s = *start;
            let mut wrapped = 0u32;
            for k in 0..N {
                let e = pos[*j + k];
                // Branch-free: fields are quoted at random, so `&&` would mispredict.
                // s <= e < buf.len(), and e - 1 is only read when e >= 1.
                let (a, z) = unsafe { (*buf.get_unchecked(s as usize), *buf.get_unchecked((e.max(1) - 1) as usize)) };
                let w = (e >= s + 2) & (a == b'"') & (z == b'"');
                wrapped += w as u32;
                row.spans[k] = (s + w as u32, e - w as u32);
                s = e + 1;
            }
            if q - *qstart == 2 * wrapped {
                f(&row);
            }
            *j += N;
        } else {
            while pos[*j] != nl {
                *j += 1;
            }
            *j += 1;
        }
        *start = nl + 1;
        *qstart = q;
    };

    let mut base = 0usize;
    while base < len {
        let end = (base + WINDOW * BLOCK).min(len.div_ceil(BLOCK) * BLOCK);
        while base < end {
            let m = masks(buf[base..base + BLOCK].try_into().unwrap());
            // Positions of the set bits, 8 at a time with unconditional writes (simdjson's
            // flatten): the spare entries past `n` are garbage, overwritten next block.
            let mut bits = m.comma | m.nl;
            let n = bits.count_ones() as usize;
            let at = pos.len();
            // A block has at most 64 delimiters, so 64 slots past `at` cover every round.
            pos.reserve(BLOCK);
            unsafe {
                let p = pos.as_mut_ptr().add(at);
                let mut k = 0;
                while k < n {
                    for i in 0..8 {
                        *p.add(k + i) = base as u32 + bits.trailing_zeros();
                        bits &= bits.wrapping_sub(1);
                    }
                    k += 8;
                }
                pos.set_len(at + n);
            }
            let mut nlb = m.nl;
            while nlb != 0 {
                let t = nlb.trailing_zeros();
                nlb &= nlb - 1;
                nls.push((base as u32 + t, qblock + (m.quote & ((1u64 << t) - 1)).count_ones()));
            }
            qblock += m.quote.count_ones();
            base += BLOCK;
        }
        let mut j = 0usize;
        for &(nl, q) in &nls {
            line(&pos, &mut j, nl, q, &mut start, &mut qstart);
        }
        nls.clear();
        pos.drain(..j);
    }
    // A last line with no '\n': end it at len.
    if (start as usize) < len || !pos.is_empty() {
        pos.push(len as u32);
        let mut j = 0;
        line(&pos, &mut j, len as u32, qblock, &mut start, &mut qstart);
    }
}

/// `data` copied into a zero-padded buffer that `lines` accepts.
pub fn padded(data: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(data.len().div_ceil(BLOCK) * BLOCK + SLACK);
    v.extend_from_slice(data);
    v.resize(data.len().div_ceil(BLOCK) * BLOCK + SLACK, 0);
    v
}

/// Body lines (header dropped) of a small file, collected.
pub fn rows<const N: usize>(data: &[u8]) -> Vec<[Vec<u8>; N]> {
    let body = match data.iter().position(|&c| c == b'\n') {
        Some(i) => &data[i + 1..],
        None => &[],
    };
    let buf = padded(body);
    let mut out = Vec::new();
    lines::<N, _>(&buf, body.len(), |r| out.push(std::array::from_fn(|i| r.get(i).to_vec())));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The dialect read straight off rules.md, line by line.
    fn reference<const N: usize>(data: &[u8]) -> Vec<Vec<Vec<u8>>> {
        let body = data.strip_suffix(b"\n").unwrap_or(data);
        if data.is_empty() {
            return vec![];
        }
        let mut out = Vec::new();
        'line: for line in body.split(|&c| c == b'\n') {
            let parts: Vec<&[u8]> = line.split(|&c| c == b',').collect();
            if parts.len() != N {
                continue;
            }
            let mut row = Vec::new();
            for p in parts {
                let q = p.iter().filter(|&&c| c == b'"').count();
                if q == 0 {
                    row.push(p.to_vec());
                } else if q == 2 && p.len() >= 2 && p[0] == b'"' && p[p.len() - 1] == b'"' {
                    row.push(p[1..p.len() - 1].to_vec());
                } else {
                    continue 'line;
                }
            }
            out.push(row);
        }
        out
    }

    fn fast<const N: usize>(data: &[u8]) -> Vec<Vec<Vec<u8>>> {
        let buf = padded(data);
        let mut out = Vec::new();
        lines::<N, _>(&buf, data.len(), |r| out.push((0..N).map(|i| r.get(i).to_vec()).collect()));
        out
    }

    #[test]
    fn swar_matches_simd() {
        let mut s: u64 = 99;
        for _ in 0..2000 {
            let mut b = [0u8; BLOCK];
            for c in b.iter_mut() {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                *c = if s >> 62 == 0 { b",\"\n"[(s >> 40) as usize % 3] } else { (s >> 33) as u8 };
            }
            let (x, y) = (masks(&b), masks_swar(&b));
            assert_eq!((x.comma, x.quote, x.nl), (y.comma, y.quote, y.nl));
        }
    }

    #[test]
    fn matches_reference() {
        let cases: &[&[u8]] = &[
            b"\"u4\",\"u1\"\n\"\",x\nu1,u5\"\nu1,u2,u3\n\nu1\n\"A\tB\",c\n\",x\n\"a\"b\",c\nlast,line",
            b"x,y\n",
            b"",
            b"\n",
            b"\n\n",
            b",",
            b",\n",
            b"a,\"\"\"\n,\n\"\",\"\"",
            b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,b\r\n\"q\"q,b\nz,\"y\"",
        ];
        for c in cases {
            assert_eq!(fast::<2>(c), reference::<2>(c), "{:?}", String::from_utf8_lossy(c));
        }
        let mut s: u64 = 12345;
        for round in 0..30000 {
            let mut buf = Vec::new();
            let n = if round % 10 == 0 { s % 300 } else { s % 40 };
            for _ in 0..n {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                buf.push(b"ab,\"\n\r"[(s >> 33) as usize % 6]);
            }
            assert_eq!(fast::<2>(&buf), reference::<2>(&buf), "{:?}", String::from_utf8_lossy(&buf));
            assert_eq!(fast::<3>(&buf), reference::<3>(&buf), "{:?}", String::from_utf8_lossy(&buf));
            assert_eq!(fast::<7>(&buf), reference::<7>(&buf), "{:?}", String::from_utf8_lossy(&buf));
        }
    }
}
