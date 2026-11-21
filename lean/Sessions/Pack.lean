import Std.Tactic.BVDecide

/-!
# Price and category in one word (`src/main.rs`, `Narrow`)

`Narrow` stores a purchase as `price | cat << 24`. For every price the rules accept
(at most 10,000,000) and every category index below 256, both come back exactly, and
the word is never `BAD` (all ones), the mark of a copy that failed validation.
-/
namespace Sessions.Pack

def pc (price cat : BitVec 32) : BitVec 32 := price ||| (cat <<< 24)
def price (p : BitVec 32) : BitVec 32 := p &&& 0xffffff
def cat (p : BitVec 32) : BitVec 32 := p >>> 24

theorem roundtrip (p c : BitVec 32) (hp : p ≤ 10000000) (hc : c < 256) :
    price (pc p c) = p ∧ cat (pc p c) = c ∧ pc p c ≠ 0xffffffff := by
  simp only [pc, price, cat]
  bv_decide

end Sessions.Pack
