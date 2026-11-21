//! Uncompressed Parquet with one row group per file. Each column uses PLAIN or
//! a PLAIN dictionary and a bit-packed RLE_DICTIONARY data page.

use std::io::Write;

pub enum Values {
    I32(Vec<i32>),
    I64(Vec<i64>),
    Date(Vec<i32>),
    /// Strings as concatenated bytes and end offsets; `None` entries are nulls.
    Str {
        bytes: Vec<u8>,
        ends: Vec<u32>,
        nulls: Option<Vec<bool>>,
    },
}

impl Values {
    pub fn integers(values: Vec<i64>, narrow: bool) -> Self {
        if narrow {
            Self::I32(
                values
                    .into_iter()
                    .map(|x| i32::try_from(x).unwrap())
                    .collect(),
            )
        } else {
            Self::I64(values)
        }
    }

    pub fn strings(nullable: bool) -> Self {
        Values::Str {
            bytes: Vec::new(),
            ends: Vec::new(),
            nulls: nullable.then(Vec::new),
        }
    }

    pub fn push_str(&mut self, s: Option<&[u8]>) {
        let Values::Str { bytes, ends, nulls } = self else {
            unreachable!()
        };
        match (s, nulls) {
            (Some(s), n) => {
                bytes.extend_from_slice(s);
                ends.push(bytes.len() as u32);
                if let Some(n) = n {
                    n.push(false);
                }
            }
            (None, Some(n)) => n.push(true),
            (None, None) => panic!("null in a required column"),
        }
    }

    fn len(&self) -> usize {
        match self {
            Values::Date(v) | Values::I32(v) => v.len(),
            Values::I64(v) => v.len(),
            Values::Str { ends, nulls, .. } => nulls.as_ref().map_or(ends.len(), |n| n.len()),
        }
    }

    /// Parquet physical type: INT32 = 1, INT64 = 2, BYTE_ARRAY = 6.
    fn physical(&self) -> i32 {
        match self {
            Values::Date(_) | Values::I32(_) => 1,
            Values::I64(_) => 2,
            Values::Str { .. } => 6,
        }
    }

    fn optional(&self) -> bool {
        matches!(self, Values::Str { nulls: Some(_), .. })
    }

    fn levels(&self, out: &mut Vec<u8>) {
        if let Values::Str { nulls: Some(n), .. } = self {
            // RLE/bit-packed hybrid, bit width 1, one bit-packed run; 4-byte length prefix.
            let groups = n.len().div_ceil(8);
            let mut lv = Vec::with_capacity(groups + 10);
            varint(&mut lv, ((groups as u64) << 1) | 1);
            for g in n.chunks(8) {
                lv.push(
                    g.iter()
                        .enumerate()
                        .fold(0u8, |b, (i, &null)| b | ((!null as u8) << i)),
                );
            }
            out.extend_from_slice(&(lv.len() as u32).to_le_bytes());
            out.extend_from_slice(&lv);
        }
    }

    fn dictionary(&self) -> Option<Dictionary> {
        match self {
            Values::I32(v) | Values::Date(v) => {
                dictionary(v.iter().copied(), v.len() * 4, |out, value| {
                    out.extend_from_slice(&value.to_le_bytes())
                })
            }
            Values::I64(v) => dictionary(v.iter().copied(), v.len() * 8, |out, value| {
                out.extend_from_slice(&value.to_le_bytes())
            }),
            Values::Str { bytes, ends, .. } => {
                let mut start = 0;
                let strings = ends.iter().map(|&end| {
                    let value = &bytes[start..end as usize];
                    start = end as usize;
                    value
                });
                dictionary(strings, bytes.len() + 4 * ends.len(), |out, value| {
                    out.extend_from_slice(&(value.len() as u32).to_le_bytes());
                    out.extend_from_slice(value);
                })
            }
        }
    }

    /// Page body: definition levels (optional columns only), then PLAIN values.
    fn page(&self) -> Vec<u8> {
        let mut out = Vec::new();
        match self {
            Values::Date(v) | Values::I32(v) => v
                .iter()
                .for_each(|x| out.extend_from_slice(&x.to_le_bytes())),
            Values::I64(v) => v
                .iter()
                .for_each(|x| out.extend_from_slice(&x.to_le_bytes())),
            Values::Str { bytes, ends, .. } => {
                self.levels(&mut out);
                let mut start = 0usize;
                out.reserve(bytes.len() + 4 * ends.len());
                for &e in ends {
                    let e = e as usize;
                    out.extend_from_slice(&((e - start) as u32).to_le_bytes());
                    out.extend_from_slice(&bytes[start..e]);
                    start = e;
                }
            }
        }
        out
    }
}

struct Dictionary {
    entries: Vec<u8>,
    count: i32,
    indices: Vec<u8>,
}

fn dictionary<K: Copy + Eq + std::hash::Hash>(
    values: impl ExactSizeIterator<Item = K>,
    plain_bytes: usize,
    mut append: impl FnMut(&mut Vec<u8>, K),
) -> Option<Dictionary> {
    if values.len() < 64 {
        return None;
    }
    let groups = values.len().div_ceil(8);
    let mut lookup = std::collections::HashMap::new();
    let mut entries = Vec::new();
    let mut indices = Vec::with_capacity(values.len());
    let mut previous = None;
    let mut index = 0u32;
    for value in values {
        if previous != Some(value) {
            let next = lookup.len() as u32;
            index = *lookup.entry(value).or_insert_with(|| {
                append(&mut entries, value);
                next
            });
            previous = Some(value);
        }
        indices.push(index);
    }
    let count = lookup.len();
    let width = (u32::BITS - (count as u32 - 1).leading_zeros()).max(1);
    let packed_bytes = groups * width as usize;
    if entries.len() + packed_bytes + 32 >= plain_bytes {
        return None;
    }
    let mut packed = Vec::with_capacity(packed_bytes + 10);
    packed.push(width as u8);
    varint(&mut packed, (groups as u64) * 2 + 1);
    let header_len = packed.len();
    let mut word = 0u64;
    let mut bits = 0;
    for id in indices {
        word |= (id as u64) << bits;
        bits += width;
        while bits >= 8 {
            packed.push(word as u8);
            word >>= 8;
            bits -= 8;
        }
    }
    if bits > 0 {
        packed.push(word as u8);
    }
    packed.resize(header_len + packed_bytes, 0);
    Some(Dictionary {
        entries,
        count: count as i32,
        indices: packed,
    })
}

pub struct Column {
    pub name: &'static str,
    pub values: Values,
}

fn varint(out: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        out.push(v as u8 | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

/// Thrift compact protocol writer, just the parts the footer uses.
struct Thrift {
    out: Vec<u8>,
    last: Vec<i16>,
}

const I32: u8 = 5;
const I64: u8 = 6;
const BINARY: u8 = 8;
const LIST: u8 = 9;
const STRUCT: u8 = 12;

impl Thrift {
    fn field(&mut self, id: i16, ty: u8) {
        let last = self.last.last_mut().unwrap();
        let d = id - *last;
        if (1..=15).contains(&d) {
            self.out.push((d as u8) << 4 | ty);
        } else {
            self.out.push(ty);
            varint(&mut self.out, ((id << 1) ^ (id >> 15)) as u16 as u64);
        }
        *last = id;
    }
    fn i32(&mut self, id: i16, v: i32) {
        self.field(id, I32);
        varint(&mut self.out, ((v << 1) ^ (v >> 31)) as u32 as u64);
    }
    fn i64(&mut self, id: i16, v: i64) {
        self.field(id, I64);
        varint(&mut self.out, ((v << 1) ^ (v >> 63)) as u64);
    }
    fn str(&mut self, id: i16, s: &str) {
        self.field(id, BINARY);
        varint(&mut self.out, s.len() as u64);
        self.out.extend_from_slice(s.as_bytes());
    }
    fn list(&mut self, id: i16, ty: u8, n: usize) {
        self.field(id, LIST);
        if n < 15 {
            self.out.push((n as u8) << 4 | ty);
        } else {
            self.out.push(0xf0 | ty);
            varint(&mut self.out, n as u64);
        }
    }
    fn begin(&mut self, id: i16) {
        self.field(id, STRUCT);
        self.last.push(0);
    }
    /// A struct that is a list element: no field header.
    fn begin_elem(&mut self) {
        self.last.push(0);
    }
    fn end(&mut self) {
        self.out.push(0);
        self.last.pop();
    }
}

pub fn write(path: &std::path::Path, cols: &[Column]) -> std::io::Result<()> {
    let rows = cols.first().map_or(0, |c| c.values.len());
    let mut file = Vec::new();
    file.extend_from_slice(b"PAR1");
    let mut chunks = Vec::new(); // (offset, size)
    for c in cols {
        assert_eq!(c.values.len(), rows, "column {}", c.name);
        let off = file.len();
        let dictionary = c.values.dictionary();
        let encoded = dictionary.is_some();
        let body = if let Some(dict) = dictionary {
            let mut header = Thrift {
                out: Vec::new(),
                last: vec![0],
            };
            header.i32(1, 2); // DICTIONARY_PAGE
            header.i32(2, dict.entries.len() as i32);
            header.i32(3, dict.entries.len() as i32);
            header.begin(7);
            header.i32(1, dict.count);
            header.i32(2, 0); // PLAIN
            header.end();
            header.end();
            file.extend_from_slice(&header.out);
            file.extend_from_slice(&dict.entries);
            let mut body = Vec::new();
            c.values.levels(&mut body);
            body.extend_from_slice(&dict.indices);
            body
        } else {
            c.values.page()
        };
        let data_offset = file.len();
        let mut h = Thrift {
            out: Vec::new(),
            last: vec![0],
        };
        h.i32(1, 0); // DATA_PAGE
        h.i32(2, body.len() as i32);
        h.i32(3, body.len() as i32);
        h.begin(5);
        h.i32(1, rows as i32);
        h.i32(2, if encoded { 8 } else { 0 }); // RLE_DICTIONARY or PLAIN
        h.i32(3, 3); // RLE definition levels
        h.i32(4, 3); // RLE repetition levels
        h.end();
        h.out.push(0);
        file.extend_from_slice(&h.out);
        file.extend_from_slice(&body);
        chunks.push((off, file.len() - off, data_offset));
    }

    let mut t = Thrift {
        out: Vec::new(),
        last: vec![0],
    };
    t.i32(1, 1); // version
    t.list(2, STRUCT, cols.len() + 1);
    t.begin_elem();
    t.str(4, "schema");
    t.i32(5, cols.len() as i32);
    t.end();
    for c in cols {
        t.begin_elem();
        t.i32(1, c.values.physical());
        t.i32(3, c.values.optional() as i32); // REQUIRED = 0, OPTIONAL = 1
        t.str(4, c.name);
        match c.values {
            Values::Str { .. } => {
                t.i32(6, 0); // converted type UTF8
                t.begin(10); // logical type
                t.begin(1); // STRING
                t.end();
                t.end();
            }
            Values::Date(_) => {
                t.i32(6, 6); // converted type DATE
                t.begin(10);
                t.begin(6); // DATE
                t.end();
                t.end();
            }
            _ => {}
        }
        t.end();
    }
    t.i64(3, rows as i64);
    t.list(4, STRUCT, 1);
    t.begin_elem();
    t.list(1, STRUCT, cols.len());
    for (c, &(off, size, data_offset)) in cols.iter().zip(&chunks) {
        t.begin_elem();
        t.i64(2, off as i64);
        t.begin(3);
        t.i32(1, c.values.physical());
        t.list(2, I32, if off == data_offset { 2 } else { 3 });
        varint(&mut t.out, 0); // PLAIN (zigzag 0)
        varint(&mut t.out, 6); // RLE (zigzag 3)
        if off != data_offset {
            varint(&mut t.out, 16);
        } // RLE_DICTIONARY
        t.list(3, BINARY, 1);
        varint(&mut t.out, c.name.len() as u64);
        t.out.extend_from_slice(c.name.as_bytes());
        t.i32(4, 0); // UNCOMPRESSED
        t.i64(5, rows as i64);
        t.i64(6, size as i64);
        t.i64(7, size as i64);
        t.i64(9, data_offset as i64);
        if off != data_offset {
            t.i64(11, off as i64);
        }
        t.end();
        t.end();
    }
    t.i64(2, chunks.iter().map(|c| c.1 as i64).sum());
    t.i64(3, rows as i64);
    t.end();
    t.str(6, "dbx-sessions");
    t.out.push(0);

    file.extend_from_slice(&t.out);
    file.extend_from_slice(&(t.out.len() as u32).to_le_bytes());
    file.extend_from_slice(b"PAR1");
    std::fs::File::create(path)?.write_all(&file)
}
