import Std.Tactic.BVDecide

/-!
# Eight digits at a time (`src/ts.rs`, `digits8` and `value8`)

An F3 timestamp's digits are loaded 8 at a time into a little-endian word, most
significant digit in byte 0. `check` (the two mask tests of `digits8`) accepts exactly
the words whose 8 bytes are all ASCII `0`..`9`, and on those `value8`'s three
multiply-and-mask steps give the decimal value `d0 * 10^7 + ... + d7`.
-/
namespace Sessions.Epoch

/-- Byte `i` of the word, little-endian. -/
def byte (w : BitVec 64) (i : Nat) : BitVec 64 := (w >>> (8 * i)) &&& 0xff

def isDigit (b : BitVec 64) : Bool := 0x30 ≤ b && b ≤ 0x39

def check (w : BitVec 64) : Bool :=
  (w &&& 0xf0f0f0f0f0f0f0f0) == 0x3030303030303030 &&
  ((w + 0x0606060606060606) &&& 0xf0f0f0f0f0f0f0f0) == 0x3030303030303030

def value8 (w : BitVec 64) : BitVec 64 :=
  let v := w &&& 0x0f0f0f0f0f0f0f0f
  let v := (v * 10 + (v >>> 8)) &&& 0x00ff00ff00ff00ff
  let v := (v * 100 + (v >>> 16)) &&& 0x0000ffff0000ffff
  (v * 10000 + (v >>> 32)) &&& 0xffffffff

def spec (w : BitVec 64) : BitVec 64 :=
  (byte w 0 - 0x30) * 10000000 + (byte w 1 - 0x30) * 1000000 + (byte w 2 - 0x30) * 100000 +
  (byte w 3 - 0x30) * 10000 + (byte w 4 - 0x30) * 1000 + (byte w 5 - 0x30) * 100 +
  (byte w 6 - 0x30) * 10 + (byte w 7 - 0x30)

theorem check_exact (w : BitVec 64) :
    check w = (isDigit (byte w 0) && isDigit (byte w 1) && isDigit (byte w 2) && isDigit (byte w 3) &&
      isDigit (byte w 4) && isDigit (byte w 5) && isDigit (byte w 6) && isDigit (byte w 7)) := by
  simp only [check, isDigit, byte]
  bv_decide

theorem value8_exact (w : BitVec 64) (h : check w = true) : value8 w = spec w := by
  simp only [check, value8, spec, byte] at *
  bv_decide

end Sessions.Epoch
