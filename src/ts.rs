//! `ts` to epoch milliseconds (rules.md, Timestamps). `None` is a bad timestamp.
//! F1 `YYYY-MM-DDTHH:MM:SSZ` (20 bytes), F2 `...SS+HH:MM` (25 bytes), F3 digits.

pub const SEC: i64 = 1_000;
pub const MIN: i64 = 60 * SEC;
pub const HOUR: i64 = 60 * MIN;
pub const DAY: i64 = 24 * HOUR;

/// Days since 1970-01-01 of a proleptic Gregorian date (Hinnant's algorithm).
pub fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

fn month_days(y: i64, m: i64) -> i64 {
    match m {
        2 if y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) => 29,
        2 => 28,
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}

#[inline]
pub fn parse(s: &[u8]) -> Option<i64> {
    match s.len() {
        20 | 25 if s[4] == b'-' => civil(s),
        0 => None,
        _ => epoch(s),
    }
}

/// F3. Leading zeros are fine; a value past i64 is outside every window, so bad.
#[inline]
fn epoch(s: &[u8]) -> Option<i64> {
    let mut v: u64 = 0;
    for &c in s {
        let d = c.wrapping_sub(b'0');
        if d >= 10 {
            return None;
        }
        v = v.checked_mul(10)?.checked_add(d as u64)?;
    }
    i64::try_from(v).ok()
}

// SWAR: F1 and F2 are checked and split 8 bytes at a time against templates.
// lean/Sessions/Ts.lean defines `check` and `pairs` with these exact operations and
// constants and proves, for every 64-bit word, that `check` accepts exactly the words
// with digits and separators in place and that `pairs` then reads each 2-digit field.
const LO7: u64 = 0x7f7f_7f7f_7f7f_7f7f;
const H: u64 = 0x8080_8080_8080_8080;
const ADJ: u64 = 0x7676_7676_7676_7676;
/// bytes 0..8, `YYYY-MM-`: century at pair byte 1, year 3, month 6
const T_DATE: u64 = 0x2d30_302d_3030_3030;
const D_DATE: u64 = 0x00ff_ff00_ffff_ffff;
/// bytes 8..16, `DDTHH:MM`: day 1, hour 4, minute 7
const T_DAY: u64 = 0x3030_3a30_3054_3030;
const D_DAY: u64 = 0xffff_00ff_ff00_ffff;
/// F1 bytes 12..20, `H:MM:SSZ`: second 6
const T_F1: u64 = 0x5a30_303a_3030_3a30;
const D_F1: u64 = 0x00ff_ff00_ffff_00ff;
/// F2 bytes 11..19, `HH:MM:SS`: second 7
const T_CLOCK: u64 = 0x3030_3a30_303a_3030;
const D_CLOCK: u64 = 0xffff_00ff_ff00_ffff;
/// F2 bytes 17..25, `SS±HH:MM`, sign ignored: offset hour 4, offset minute 7
const T_OFF: u64 = 0x3030_3a30_3000_3030;
const D_OFF: u64 = 0xffff_00ff_ff00_ffff;
const I_OFF: u64 = 0x0000_0000_00ff_0000;

#[inline(always)]
fn word(s: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(s[at..at + 8].try_into().unwrap())
}

#[inline(always)]
fn check(w: u64, t: u64, d: u64, i: u64) -> bool {
    let x = w ^ t;
    let sep = x & !d & !i;
    let dig = (((x & LO7).wrapping_add(ADJ)) | x) & H & d;
    (sep | dig) == 0
}

#[inline(always)]
fn pairs(w: u64, t: u64, d: u64) -> u64 {
    ((w ^ t) & d).wrapping_mul(0xa01)
}

#[inline(always)]
fn at(p: u64, k: u32) -> i64 {
    ((p >> (8 * k)) & 0xff) as i64
}

/// Days from 1970-01-01 to January 1 of 1900 + i, for the fast path.
const YEAR0: i64 = 1900;
static YEARS: [i32; 301] = {
    let mut t = [0i32; 301];
    let mut i = 0;
    while i < 301 {
        let y = YEAR0 + i as i64 - 1;
        // days_from_civil(y + 1, 1, 1), in a const context
        let era = y.div_euclid(400);
        let yoe = y - era * 400;
        let doe = yoe * 365 + yoe / 4 - yoe / 100 + 306;
        t[i] = (era * 146_097 + doe - 719_468) as i32;
        i += 1;
    }
    t
};
/// Days before each month, common and leap years.
const BEFORE: [[i16; 12]; 2] = [
    [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334],
    [0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335],
];

#[inline(always)]
fn days(y: i64, mo: i64, d: i64) -> i64 {
    let leap = (y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)) as usize;
    match YEARS.get((y - YEAR0) as usize) {
        Some(&t) => t as i64 + BEFORE[leap][mo as usize - 1] as i64 + d - 1,
        None => days_from_civil(y, mo, d),
    }
}

#[inline]
fn civil(s: &[u8]) -> Option<i64> {
    let f2 = s.len() == 25;
    let (w0, w1) = (word(s, 0), word(s, 8));
    let (wc, tc, dc) = if f2 { (word(s, 11), T_CLOCK, D_CLOCK) } else { (word(s, 12), T_F1, D_F1) };
    if !(check(w0, T_DATE, D_DATE, 0) & check(w1, T_DAY, D_DAY, 0) & check(wc, tc, dc, 0)) {
        return None;
    }
    let (p0, p1, pc) = (pairs(w0, T_DATE, D_DATE), pairs(w1, T_DAY, D_DAY), pairs(wc, tc, dc));
    let (y, mo, d) = (at(p0, 1) * 100 + at(p0, 3), at(p0, 6), at(p1, 1));
    let (h, mi, se) = (at(p1, 4), at(p1, 7), if f2 { at(pc, 7) } else { at(pc, 6) });
    if !(1..=12).contains(&mo) || d == 0 || d > month_days(y, mo) || h > 23 || mi > 59 || se > 59 {
        return None;
    }
    let off = if f2 {
        let wo = word(s, 17);
        let sign = match s[19] {
            b'+' => 1,
            b'-' => -1,
            _ => return None,
        };
        if !check(wo, T_OFF, D_OFF, I_OFF) {
            return None;
        }
        let po = pairs(wo, T_OFF, D_OFF);
        let (oh, om) = (at(po, 4), at(po, 7));
        if oh > 23 || om > 59 {
            return None;
        }
        sign * (oh * HOUR + om * MIN)
    } else {
        0
    };
    Some(days(y, mo, d) * DAY + h * HOUR + mi * MIN + se * SEC - off)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The byte-at-a-time parser the SWAR one replaced, kept as a reference.
    fn civil_ref(s: &[u8]) -> Option<i64> {
        fn d2(s: &[u8], i: usize) -> Option<i64> {
            let (a, b) = (s[i].wrapping_sub(b'0'), s[i + 1].wrapping_sub(b'0'));
            if a < 10 && b < 10 { Some((a * 10 + b) as i64) } else { None }
        }
        if s[4] != b'-' || s[7] != b'-' || s[10] != b'T' || s[13] != b':' || s[16] != b':' {
            return None;
        }
        let y = d2(s, 0)? * 100 + d2(s, 2)?;
        let (mo, d) = (d2(s, 5)?, d2(s, 8)?);
        let (h, mi, se) = (d2(s, 11)?, d2(s, 14)?, d2(s, 17)?);
        if !(1..=12).contains(&mo) || d == 0 || d > month_days(y, mo) || h > 23 || mi > 59 || se > 59 {
            return None;
        }
        let off = if s.len() == 20 {
            if s[19] != b'Z' {
                return None;
            }
            0
        } else {
            let sign = match s[19] {
                b'+' => 1,
                b'-' => -1,
                _ => return None,
            };
            let (oh, om) = (d2(s, 20)?, d2(s, 23)?);
            if s[22] != b':' || oh > 23 || om > 59 {
                return None;
            }
            sign * (oh * HOUR + om * MIN)
        };
        Some(days_from_civil(y, mo, d) * DAY + h * HOUR + mi * MIN + se * SEC - off)
    }

    #[test]
    fn swar_matches_reference() {
        let seeds: [&[u8]; 6] = [
            b"2026-10-03T23:58:10Z", b"2028-02-29T00:00:00Z", b"1899-12-31T23:59:59Z",
            b"2026-10-03T19:58:10-04:00", b"2201-01-01T00:00:00+23:59", b"0000-01-01T00:00:00-00:00",
        ];
        let alphabet = b"0123456789-:TZtz+ \x00\xff/;9";
        let mut r: u64 = 7;
        let mut next = || {
            r = r.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            r >> 33
        };
        for _ in 0..2_000_000 {
            let mut s = seeds[next() as usize % seeds.len()].to_vec();
            for _ in 0..1 + next() % 3 {
                let i = next() as usize % s.len();
                s[i] = if next() % 2 == 0 { alphabet[next() as usize % alphabet.len()] } else { b'0' + (next() % 10) as u8 };
            }
            assert_eq!(civil(&s), civil_ref(&s), "{:?}", String::from_utf8_lossy(&s));
        }
        for y in [1600, 1899, 1900, 1970, 2000, 2024, 2100, 2199, 2200, 2400, 9999] {
            for m in 1..=12 {
                for d in [1, 28, month_days(y, m)] {
                    assert_eq!(days(y, m, d), days_from_civil(y, m, d), "{y}-{m}-{d}");
                }
            }
        }
    }

    #[test]
    fn forms() {
        let f1 = parse(b"2026-10-03T23:58:10Z").unwrap();
        assert_eq!(f1, 1_791_071_890_000);
        assert_eq!(parse(b"2026-10-03T19:58:10-04:00"), Some(f1));
        assert_eq!(parse(b"2026-10-04T01:30:00+02:00"), parse(b"2026-10-03T23:30:00Z"));
        assert_eq!(parse(b"2026-10-03T23:58:10-00:00"), Some(f1));
        assert_eq!(parse(b"2026-10-03T23:58:10+23:59"), Some(f1 - 23 * HOUR - 59 * MIN));
        assert_eq!(parse(b"1791071890000"), Some(f1));
        assert_eq!(parse(b"0001791071890000"), Some(f1));
        assert_eq!(parse(b"000000000000000000000001791071890000"), Some(f1));
        assert_eq!(parse(b"86400000"), Some(DAY));
        assert!(parse(b"2028-02-29T00:00:00Z").is_some());
        assert!(parse(b"2000-02-29T00:00:00Z").is_some());
        assert_eq!(parse(b"1970-01-01T00:00:00Z"), Some(0));
        assert_eq!(parse(b"1969-12-31T23:59:59Z"), Some(-1000));
        for bad in [
            &b""[..], b"2026-10-03T23:58:10z", b"2026-10-03t23:58:10Z", b"2026-10-03 23:58:10Z",
            b"2026-10-03T23:58:10", b"1791071890000.0", b"1.79e12", b"-5", b"+5", b"2026-13-03T23:58:10Z",
            b"2026-00-03T23:58:10Z", b"2026-10-00T23:58:10Z", b"2026-02-30T23:58:10Z",
            b"2027-02-29T00:00:00Z", b"1900-02-29T00:00:00Z", b"2026-10-03T24:00:00Z",
            b"2026-10-03T23:60:10Z", b"2026-10-03T23:58:60Z", b"2026-10-03T23:58:10+24:00",
            b"2026-10-03T23:58:10+05:60", b"2026-10-03T23:58:10+0200", b"2026-10-03T23:58:10.000Z",
            b"99999999999999999999999", b"9223372036854775808", "２026-10-03T23:58:10Z".as_bytes(),
            "٢٥٠".as_bytes(), b"2026-10-03T23:58:10Z\r", b"2026-1a-03T23:58:10Z",
            b"2026-10-03T23:58:10*02:00", b"2026-10-03T23:58:10+02-00",
        ] {
            assert_eq!(parse(bad), None, "{:?}", String::from_utf8_lossy(bad));
        }
        // Every day of 1999..2031 against a day-by-day count.
        let mut n = days_from_civil(1999, 1, 1);
        for y in 1999..2031 {
            for m in 1..=12 {
                for d in 1..=month_days(y, m) {
                    assert_eq!(days_from_civil(y, m, d), n);
                    n += 1;
                }
            }
        }
    }
}
