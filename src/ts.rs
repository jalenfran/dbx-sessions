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

/// Two ASCII digits at `s[i..i + 2]` as a number, or `None`.
#[inline(always)]
fn d2(s: &[u8], i: usize) -> Option<i64> {
    let (a, b) = (s[i].wrapping_sub(b'0'), s[i + 1].wrapping_sub(b'0'));
    if a < 10 && b < 10 { Some((a * 10 + b) as i64) } else { None }
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

#[inline]
fn civil(s: &[u8]) -> Option<i64> {
    if s[7] != b'-' || s[10] != b'T' || s[13] != b':' || s[16] != b':' {
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

#[cfg(test)]
mod tests {
    use super::*;

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
