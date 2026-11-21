import Std.Tactic.BVDecide

/-!
# The SWAR byte tricks in `src/scan.rs`

`zeroBytes` and `gather` mirror the Rust functions `zero_bytes` and `gather` operation for
operation. `bv_decide` checks each statement for all 2^64 inputs.
-/
namespace Sessions.Swar

def LO7 : BitVec 64 := 0x7f7f7f7f7f7f7f7f

/-- `!(((x & LO7) + LO7) | x | LO7)` -/
def zeroBytes (x : BitVec 64) : BitVec 64 := ~~~(((x &&& LO7) + LO7) ||| x ||| LO7)

/-- Byte `i` of `x` (little-endian). -/
def byte (x : BitVec 64) (i : Nat) : BitVec 8 := x.extractLsb' (8 * i) 8

/-- The specification: bit 8i+7 is set iff byte i is zero, and no other bit is set. -/
def zeroBytesSpec (x : BitVec 64) : BitVec 64 :=
  (if byte x 0 = 0 then 0x80 else 0) |||
  (if byte x 1 = 0 then 0x8000 else 0) |||
  (if byte x 2 = 0 then 0x800000 else 0) |||
  (if byte x 3 = 0 then 0x80000000 else 0) |||
  (if byte x 4 = 0 then 0x8000000000 else 0) |||
  (if byte x 5 = 0 then 0x800000000000 else 0) |||
  (if byte x 6 = 0 then 0x80000000000000 else 0) |||
  (if byte x 7 = 0 then 0x8000000000000000 else 0)

theorem zeroBytes_exact (x : BitVec 64) : zeroBytes x = zeroBytesSpec x := by
  simp only [zeroBytes, zeroBytesSpec, byte, LO7]
  bv_decide

end Sessions.Swar

namespace Sessions.Swar

/-- `((hb >> 7) * 0x0102040810204080) >> 56` -/
def gather (hb : BitVec 64) : BitVec 64 := ((hb >>> 7) * 0x0102040810204080) >>> 56

/-- For a word with only byte-high bits set (what `zeroBytes` returns), `gather` moves the
high bit of byte i to bit i and clears everything else: no partial products overlap, so
the multiply has no carries. -/
theorem gather_exact (x : BitVec 64) :
    gather (x &&& 0x8080808080808080) =
      ((x >>> 7) &&& 1) ||| ((x >>> 14) &&& 2) ||| ((x >>> 21) &&& 4) ||| ((x >>> 28) &&& 8) |||
      ((x >>> 35) &&& 16) ||| ((x >>> 42) &&& 32) ||| ((x >>> 49) &&& 64) ||| ((x >>> 56) &&& 128) := by
  simp only [gather]
  bv_decide

end Sessions.Swar
