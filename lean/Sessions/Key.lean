import Std.Tactic.BVDecide
import Sessions.Swar

/-!
# Packing 8 ID bytes into 56 bits (`src/key.rs`, `compress`)

An ID's bytes, loaded big-endian into a word, are 7-bit values when every high bit is
clear. `compress` squeezes out the 8 zero high bits in three shift-and-mask steps
(pairs, then quads, then halves). It equals the byte-by-byte definition
`b0 << 49 | b1 << 42 | ... | b7` for every such word.
-/
namespace Sessions.Key

/-- Byte `i` counted from the most significant end (big-endian position `i`). -/
def be (w : BitVec 64) (i : Nat) : BitVec 64 := (w >>> (8 * (7 - i))) &&& 0xff

def compress (w : BitVec 64) : BitVec 64 :=
  let t := (w &&& 0x007f007f007f007f) ||| ((w &&& 0x7f007f007f007f00) >>> 1)
  let t := (t &&& 0x00003fff00003fff) ||| ((t &&& 0x3fff00003fff0000) >>> 2)
  (t &&& 0x000000000fffffff) ||| ((t &&& 0x0fffffff00000000) >>> 4)

def compressSpec (w : BitVec 64) : BitVec 64 :=
  (be w 0 <<< 49) ||| (be w 1 <<< 42) ||| (be w 2 <<< 35) ||| (be w 3 <<< 28) |||
  (be w 4 <<< 21) ||| (be w 5 <<< 14) ||| (be w 6 <<< 7) ||| be w 7

theorem compress_exact (w : BitVec 64) (h : w &&& 0x8080808080808080 = 0) :
    compress w = compressSpec w := by
  simp only [compress, compressSpec, be] at *
  bv_decide

/-- The packed key keeps the order of the words it came from: `compress` is monotone on
words with clear high bits, so (with `be` order = byte-wise order on equal-length,
zero-padded IDs) the integer order of keys is the byte order of the IDs. -/
theorem compress_mono (a b : BitVec 64) (ha : a &&& 0x8080808080808080 = 0)
    (hb : b &&& 0x8080808080808080 = 0) : (compress a ≤ compress b) = (a ≤ b) := by
  simp only [compress] at *
  bv_decide

end Sessions.Key
