//! Word-at-a-time bit tricks. Each one has a Lean twin, proved for all inputs:
//! `zero_bytes` and `gather` in lean/Sessions/Swar.lean, `compress` in Key.lean.

pub const LO7: u64 = 0x7f7f_7f7f_7f7f_7f7f;
pub const HI: u64 = 0x8080_8080_8080_8080;

/// High bit of every byte of `x` that is zero, nothing else.
#[inline(always)]
pub fn zero_bytes(x: u64) -> u64 {
    !(((x & LO7).wrapping_add(LO7)) | x | LO7)
}

/// The 8 byte-high bits of `hb` moved to bits 0..8, byte i to bit i.
#[inline(always)]
pub fn gather(hb: u64) -> u64 {
    ((hb >> 7).wrapping_mul(0x0102_0408_1020_4080)) >> 56
}

/// Eight 7-bit bytes (high bits clear), most significant first, as one 56-bit number.
#[inline(always)]
pub fn compress(w: u64) -> u64 {
    let t = (w & 0x007f_007f_007f_007f) | ((w & 0x7f00_7f00_7f00_7f00) >> 1);
    let t = (t & 0x0000_3fff_0000_3fff) | ((t & 0x3fff_0000_3fff_0000) >> 2);
    (t & 0x0000_0000_0fff_ffff) | ((t & 0x0fff_ffff_0000_0000) >> 4)
}
