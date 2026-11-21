import Std.Tactic.BVDecide
import Sessions.Swar

/-!
# SWAR timestamp fields (`src/ts.rs`, `civil`)

An F1/F2 timestamp is checked and split 8 bytes at a time. A word `w` (8 bytes of the
timestamp, little-endian) is compared against a *template*:

* `T`: the expected byte at each separator position, `'0'` at each digit position,
* `D`: `0xff` at each digit position,
* `I`: `0xff` at each position to ignore (the F2 offset sign, checked on its own).

`check` accepts the word iff every digit position holds an ASCII digit and every
separator position holds its exact byte. `pairs` then holds, in byte `k`, the two-digit
number written at bytes `k - 1, k`. Both are proved here against byte-level
specifications for every word and for each template the parser uses; the Rust
functions `check` and `pairs` are the same operations on `u64`.
-/
namespace Sessions.Ts

open Sessions.Swar (byte LO7)

def H : BitVec 64 := 0x8080808080808080
def ADJ : BitVec 64 := 0x7676767676767676

def check (T D I w : BitVec 64) : Bool :=
  let x := w ^^^ T
  let sep := x &&& ~~~D &&& ~~~I
  let dig := (((x &&& LO7) + ADJ) ||| x) &&& H &&& D
  (sep ||| dig) == 0

def pairs (T D w : BitVec 64) : BitVec 64 := ((w ^^^ T) &&& D) * 0xA01

def isDigit (b : BitVec 8) : Bool := 0x30#8 ≤ b && b ≤ 0x39#8

/-- What `check` must mean at byte `i`. -/
def byteSpec (T D I w : BitVec 64) (i : Nat) : Bool :=
  if byte I i = 0xff then true
  else if byte D i = 0xff then isDigit (byte w i)
  else byte w i == byte T i

def spec (T D I w : BitVec 64) : Bool :=
  byteSpec T D I w 0 && byteSpec T D I w 1 && byteSpec T D I w 2 && byteSpec T D I w 3 &&
  byteSpec T D I w 4 && byteSpec T D I w 5 && byteSpec T D I w 6 && byteSpec T D I w 7

/-- The two-digit number at bytes `k - 1, k`. -/
def pairSpec (w : BitVec 64) (k : Nat) : BitVec 8 :=
  10 * (byte w (k - 1) - 0x30) + (byte w k - 0x30)

/-! ## The templates, little-endian (`src/ts.rs` uses the same constants) -/

/-- bytes 0..8 of F1 and F2, `YYYY-MM-` -/
def T_DATE : BitVec 64 := 0x2d30302d30303030
def D_DATE : BitVec 64 := 0x00ffff00ffffffff
/-- bytes 8..16 of F1 and F2, `DDTHH:MM` -/
def T_DAY : BitVec 64 := 0x30303a3030543030
def D_DAY : BitVec 64 := 0xffff00ffff00ffff
/-- bytes 12..20 of F1, `H:MM:SSZ` -/
def T_F1 : BitVec 64 := 0x5a30303a30303a30
def D_F1 : BitVec 64 := 0x00ffff00ffff00ff
/-- bytes 11..19 of F2, `HH:MM:SS` -/
def T_CLOCK : BitVec 64 := 0x30303a30303a3030
def D_CLOCK : BitVec 64 := 0xffff00ffff00ffff
/-- bytes 17..25 of F2, `SS±HH:MM`, the sign ignored -/
def T_OFF : BitVec 64 := 0x30303a3030003030
def D_OFF : BitVec 64 := 0xffff00ffff00ffff
def I_OFF : BitVec 64 := 0x0000000000ff0000

/-! ## `check` is exact -/

theorem check_date (w : BitVec 64) : check T_DATE D_DATE 0 w = spec T_DATE D_DATE 0 w := by
  simp only [check, spec, byteSpec, isDigit, byte, T_DATE, D_DATE, H, ADJ, LO7]
  bv_decide

theorem check_day (w : BitVec 64) : check T_DAY D_DAY 0 w = spec T_DAY D_DAY 0 w := by
  simp only [check, spec, byteSpec, isDigit, byte, T_DAY, D_DAY, H, ADJ, LO7]
  bv_decide

theorem check_f1 (w : BitVec 64) : check T_F1 D_F1 0 w = spec T_F1 D_F1 0 w := by
  simp only [check, spec, byteSpec, isDigit, byte, T_F1, D_F1, H, ADJ, LO7]
  bv_decide

theorem check_clock (w : BitVec 64) : check T_CLOCK D_CLOCK 0 w = spec T_CLOCK D_CLOCK 0 w := by
  simp only [check, spec, byteSpec, isDigit, byte, T_CLOCK, D_CLOCK, H, ADJ, LO7]
  bv_decide

theorem check_off (w : BitVec 64) : check T_OFF D_OFF I_OFF w = spec T_OFF D_OFF I_OFF w := by
  simp only [check, spec, byteSpec, isDigit, byte, T_OFF, D_OFF, I_OFF, H, ADJ, LO7]
  bv_decide

/-! ## Once checked, `pairs` reads every two-digit field exactly -/

/-- `YYYY-MM-`: century at byte 1, year in century at 3, month at 6. -/
theorem pairs_date (w : BitVec 64) (h : check T_DATE D_DATE 0 w = true) :
    byte (pairs T_DATE D_DATE w) 1 = pairSpec w 1 ∧
    byte (pairs T_DATE D_DATE w) 3 = pairSpec w 3 ∧
    byte (pairs T_DATE D_DATE w) 6 = pairSpec w 6 := by
  simp only [check, pairs, pairSpec, byte, T_DATE, D_DATE, H, ADJ, LO7] at *
  bv_decide

/-- `DDTHH:MM`: day at byte 1, hour at 4, minute at 7. -/
theorem pairs_day (w : BitVec 64) (h : check T_DAY D_DAY 0 w = true) :
    byte (pairs T_DAY D_DAY w) 1 = pairSpec w 1 ∧
    byte (pairs T_DAY D_DAY w) 4 = pairSpec w 4 ∧
    byte (pairs T_DAY D_DAY w) 7 = pairSpec w 7 := by
  simp only [check, pairs, pairSpec, byte, T_DAY, D_DAY, H, ADJ, LO7] at *
  bv_decide

/-- `H:MM:SSZ`: second at byte 6. -/
theorem pairs_f1 (w : BitVec 64) (h : check T_F1 D_F1 0 w = true) :
    byte (pairs T_F1 D_F1 w) 6 = pairSpec w 6 := by
  simp only [check, pairs, pairSpec, byte, T_F1, D_F1, H, ADJ, LO7] at *
  bv_decide

/-- `HH:MM:SS`: hour at byte 1, minute at 4, second at 7. -/
theorem pairs_clock (w : BitVec 64) (h : check T_CLOCK D_CLOCK 0 w = true) :
    byte (pairs T_CLOCK D_CLOCK w) 1 = pairSpec w 1 ∧
    byte (pairs T_CLOCK D_CLOCK w) 4 = pairSpec w 4 ∧
    byte (pairs T_CLOCK D_CLOCK w) 7 = pairSpec w 7 := by
  simp only [check, pairs, pairSpec, byte, T_CLOCK, D_CLOCK, H, ADJ, LO7] at *
  bv_decide

/-- `SS±HH:MM`: offset hour at byte 4, offset minute at 7, whatever the sign byte. -/
theorem pairs_off (w : BitVec 64) (h : check T_OFF D_OFF I_OFF w = true) :
    byte (pairs T_OFF D_OFF w) 4 = pairSpec w 4 ∧
    byte (pairs T_OFF D_OFF w) 7 = pairSpec w 7 := by
  simp only [check, pairs, pairSpec, byte, T_OFF, D_OFF, I_OFF, H, ADJ, LO7] at *
  bv_decide

end Sessions.Ts
