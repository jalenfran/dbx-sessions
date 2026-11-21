//! Minimal Parquet writer: one row group, one uncompressed PLAIN v1 data page per
//! column, footer in Thrift compact protocol. Column types: INT64, DATE (INT32), and required or optional UTF8 strings.

use std::io::Write;

pub enum Values {
    I64(Vec<i64>),
    Date(Vec<i32>),
    /// Strings as concatenated bytes and end offsets; `None` entries are nulls.
    Str { bytes: Vec<u8>, ends: Vec<u32>, nulls: Option<Vec<bool>> },
}

impl Values {
    pub fn strings(nullable: bool) -> Self {
        Values::Str { bytes: Vec::new(), ends: Vec::new(), nulls: nullable.then(Vec::new) }
    }

    pub fn push_str(&mut self, s: Option<&[u8]>) {
        let Values::Str { bytes, ends, nulls } = self else { unreachable!() };
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
            Values::Date(v) => v.len(),
            Values::I64(v) => v.len(),
            Values::Str { ends, nulls, .. } => nulls.as_ref().map_or(ends.len(), |n| n.len()),
        }
    }

    /// Parquet physical type: INT32 = 1, INT64 = 2, BYTE_ARRAY = 6.
    fn physical(&self) -> i32 {
        match self {
            Values::Date(_) => 1,
            Values::I64(_) => 2,
            Values::Str { .. } => 6,
        }
    }

    fn optional(&self) -> bool {
        matches!(self, Values::Str { nulls: Some(_), .. })
    }

    /// Page body: definition levels (optional columns only), then PLAIN values.
    fn page(&self) -> Vec<u8> {
        let mut out = Vec::new();
        match self {
            Values::Date(v) => v.iter().for_each(|x| out.extend_from_slice(&x.to_le_bytes())),
            Values::I64(v) => v.iter().for_each(|x| out.extend_from_slice(&x.to_le_bytes())),
            Values::Str { bytes, ends, nulls } => {
                if let Some(n) = nulls {
                    // RLE/bit-packed hybrid, bit width 1, one bit-packed run; 4-byte length prefix.
                    let groups = n.len().div_ceil(8);
                    let mut lv = Vec::with_capacity(groups + 10);
                    varint(&mut lv, ((groups as u64) << 1) | 1);
                    for g in n.chunks(8) {
                        lv.push(g.iter().enumerate().fold(0u8, |b, (i, &null)| b | ((!null as u8) << i)));
                    }
                    out.extend_from_slice(&(lv.len() as u32).to_le_bytes());
                    out.extend_from_slice(&lv);
                }
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
        let body = c.values.page();
        let mut h = Thrift { out: Vec::new(), last: vec![0] };
        h.i32(1, 0); // DATA_PAGE
        h.i32(2, body.len() as i32);
        h.i32(3, body.len() as i32);
        h.begin(5);
        h.i32(1, rows as i32);
        h.i32(2, 0); // PLAIN
        h.i32(3, 3); // RLE definition levels
        h.i32(4, 3); // RLE repetition levels
        h.end();
        h.out.push(0);
        let off = file.len();
        file.extend_from_slice(&h.out);
        file.extend_from_slice(&body);
        chunks.push((off, file.len() - off));
    }

    let mut t = Thrift { out: Vec::new(), last: vec![0] };
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
    for (c, &(off, size)) in cols.iter().zip(&chunks) {
        t.begin_elem();
        t.i64(2, off as i64);
        t.begin(3);
        t.i32(1, c.values.physical());
        t.list(2, I32, 2);
        varint(&mut t.out, 0); // PLAIN (zigzag 0)
        varint(&mut t.out, 6); // RLE (zigzag 3)
        t.list(3, BINARY, 1);
        varint(&mut t.out, c.name.len() as u64);
        t.out.extend_from_slice(c.name.as_bytes());
        t.i32(4, 0); // UNCOMPRESSED
        t.i64(5, rows as i64);
        t.i64(6, size as i64);
        t.i64(7, size as i64);
        t.i64(9, off as i64);
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
