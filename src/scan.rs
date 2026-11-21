//! CSV dialect of rules.md in one pass. Each 64-byte block becomes three bitmasks
//! (`,` `"` `\n`); walking their set bits finds every field and checks its quoting.
//! A field is fine with no quote, or with exactly two, at its first and last byte.
//! A line is passed to `f` only when it has exactly N fields, all fine.

pub const BLOCK: usize = 64;

#[derive(Clone, Copy)]
struct Masks {
    comma: u64,
    quote: u64,
    nl: u64,
}

const LO7: u64 = 0x7f7f_7f7f_7f7f_7f7f;
const ONES: u64 = 0x0101_0101_0101_0101;

/// High bit of every byte of `x` that is zero; exact, no false positives
/// (lean/Sessions/Swar.lean).
#[inline(always)]
fn zero_bytes(x: u64) -> u64 {
    !(((x & LO7).wrapping_add(LO7)) | x | LO7)
}

/// The 8 high bits of `hb` gathered into one byte, byte i to bit i. The partial
/// products of the multiply never overlap, so there are no carries.
#[inline(always)]
fn gather(hb: u64) -> u64 {
    ((hb >> 7).wrapping_mul(0x0102_0408_1020_4080)) >> 56
}

#[inline(always)]
#[allow(dead_code)]
fn masks_swar(b: &[u8; BLOCK]) -> Masks {
    let mut m = Masks { comma: 0, quote: 0, nl: 0 };
    for i in 0..8 {
        let w = u64::from_le_bytes(b[i * 8..i * 8 + 8].try_into().unwrap());
        m.comma |= gather(zero_bytes(w ^ (ONES * b',' as u64))) << (i * 8);
        m.quote |= gather(zero_bytes(w ^ (ONES * b'"' as u64))) << (i * 8);
        m.nl |= gather(zero_bytes(w ^ (ONES * b'\n' as u64))) << (i * 8);
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

/// Calls `f` with the N unquoted fields of every well-formed line of `buf[..len]`.
/// `buf.len()` is a multiple of `BLOCK` and every byte from `len` on is zero.
#[inline(always)]
#[allow(unused_assignments)]
pub fn lines<'a, const N: usize, F: FnMut(&[&'a [u8]; N])>(buf: &'a [u8], len: usize, mut f: F) {
    debug_assert!(N >= 2 && buf.len() % BLOCK == 0 && buf.len() >= len);
    let mut fields: [&'a [u8]; N] = [&[]; N];
    let mut nf = 0usize;
    let mut bad = false;
    let mut fstart = 0usize;
    let mut nq = 0u32;
    let mut qfirst = 0usize;
    let mut qlast = 0usize;

    macro_rules! close {
        ($end:expr) => {{
            let end = $end;
            if nf < N {
                if nq == 0 {
                    fields[nf] = unsafe { buf.get_unchecked(fstart..end) };
                } else if nq == 2 && qfirst == fstart && qlast + 1 == end {
                    fields[nf] = unsafe { buf.get_unchecked(fstart + 1..end - 1) };
                } else {
                    bad = true;
                }
            } else {
                bad = true;
            }
            nf += 1;
            nq = 0;
            fstart = end + 1;
        }};
    }

    let mut base = 0;
    while base < len {
        let m = masks(buf[base..base + BLOCK].try_into().unwrap());
        let mut bits = m.comma | m.quote | m.nl;
        while bits != 0 {
            let t = bits.trailing_zeros();
            let i = base + t as usize;
            let bit = 1u64 << t;
            bits &= bits - 1;
            if m.comma & bit != 0 {
                close!(i);
            } else if m.quote & bit != 0 {
                if nq == 0 {
                    qfirst = i;
                }
                nq += 1;
                qlast = i;
            } else {
                close!(i);
                // An empty line is one empty field, so it fails nf == N (N >= 2).
                if !bad && nf == N {
                    f(&fields);
                }
                nf = 0;
                bad = false;
            }
        }
        base += BLOCK;
    }
    // A last line with no '\n'.
    if fstart < len || nf > 0 {
        close!(len);
        if !bad && nf == N {
            f(&fields);
        }
    }
}

/// `data` copied into a zero-padded buffer that `lines` accepts.
pub fn padded(data: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(data.len().div_ceil(BLOCK) * BLOCK + BLOCK);
    v.extend_from_slice(data);
    v.resize(data.len().div_ceil(BLOCK) * BLOCK, 0);
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
    lines::<N, _>(&buf, body.len(), |f| out.push(f.map(|x| x.to_vec())));
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
        lines::<N, _>(&buf, data.len(), |f| out.push(f.iter().map(|x| x.to_vec()).collect()));
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
