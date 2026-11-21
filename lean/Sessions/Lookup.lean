/-!
# Numbered IDs (`src/key.rs`, `Lookup::number`)

`Lookup` stores IDs of the form `prefix ++ digits` in an array indexed by the value of
`digits`, when the digits are canonical: non-empty, at most 7 of them, ASCII `0`..`9`,
no leading `0` unless the whole number is `0`. Insertion and lookup both classify an ID
with the same `number`, so the array is an exact map from IDs as long as `number` is
injective: two IDs with the same number are the same ID. That is `number_inj`.
`number_fits` shows the 7-digit accumulator never leaves `u32`.

Bytes are `Nat`s here; `number` reads the digits most significant first, exactly as the
Rust loop `v = v * 10 + (c - b'0')` does.
-/
namespace Sessions.Lookup

def isDigit (c : Nat) : Bool := 48 ≤ c && c < 58

/-- The Rust loop: most significant digit first. -/
def valBE (d : List Nat) : Nat := d.foldl (fun v c => v * 10 + (c - 48)) 0

/-- The same value, least significant digit first, for induction. -/
def valLE : List Nat → Nat
  | [] => 0
  | c :: r => (c - 48) + 10 * valLE r

theorem valBE_eq (d : List Nat) : valBE d = valLE d.reverse := by
  unfold valBE
  rw [← List.reverse_reverse d, List.foldl_reverse, List.reverse_reverse]
  generalize d.reverse = r
  induction r with
  | nil => rfl
  | cons c r ih => simp only [List.foldr, valLE, ih]; omega

/-- Canonical digits: non-empty, all digits, no leading zero unless just `0`. -/
def canon (d : List Nat) : Prop :=
  d ≠ [] ∧ d.all isDigit = true ∧ ¬(d.head? = some 48 ∧ d.length > 1)

instance (d : List Nat) : Decidable (canon d) := by unfold canon; infer_instance

/-- `Lookup::number`, given the table's prefix and an ID's bytes. -/
def number (pre b : List Nat) : Option Nat :=
  let d := b.drop pre.length
  if b.take pre.length = pre ∧ canon d ∧ d.length ≤ 7 ∧ valBE d < 2 ^ 22 then some (valBE d) else none

theorem digit (c : Nat) (h : isDigit c = true) : 48 ≤ c ∧ c < 58 := by
  simp [isDigit] at h; omega

theorem lt_pow (r : List Nat) (h : r.all isDigit = true) : valLE r < 10 ^ r.length := by
  induction r with
  | nil => simp [valLE]
  | cons c r ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have := digit c h.1
    have := ih h.2
    simp only [valLE, List.length_cons, Nat.pow_succ]
    omega

/-- With its most significant digit (the last, least-significant-first) not `0`, a
number of n + 1 digits is at least 10 ^ n. -/
theorem pow_le (r : List Nat) (h : r.all isDigit = true) (ne : r ≠ []) (top : r.getLast? ≠ some 48) :
    10 ^ (r.length - 1) ≤ valLE r := by
  induction r with
  | nil => contradiction
  | cons c r ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have := digit c h.1
    cases r with
    | nil => simp [valLE] at *; omega
    | cons c' r' =>
      have := ih h.2 (by simp) (by simpa [List.getLast?_cons_cons] using top)
      simp only [valLE, List.length_cons, Nat.add_sub_cancel, Nat.pow_succ] at *
      omega

theorem same_length (r s : List Nat) (hr : r.all isDigit = true) (hs : s.all isDigit = true)
    (len : r.length = s.length) (v : valLE r = valLE s) : r = s := by
  induction r generalizing s with
  | nil => cases s <;> simp_all
  | cons c r ih =>
    cases s with
    | nil => simp at len
    | cons c' s =>
      simp only [List.all_cons, Bool.and_eq_true] at hr hs
      have := digit c hr.1
      have := digit c' hs.1
      simp only [valLE] at v
      have hc : c = c' := by omega
      have := ih s hr.2 hs.2 (by simpa using len) (by omega)
      rw [hc, this]

theorem canon_rev (d : List Nat) (h : canon d) :
    d.reverse.all isDigit = true ∧ d.reverse ≠ [] ∧ (d.length > 1 → d.reverse.getLast? ≠ some 48) := by
  obtain ⟨ne, dig, lead⟩ := h
  refine ⟨by simpa using dig, by simpa using ne, fun l => ?_⟩
  rw [List.getLast?_reverse]
  exact fun e => lead ⟨e, l⟩

/-- Canonical digit strings with the same value are the same string. -/
theorem canon_inj (a b : List Nat) (ha : canon a) (hb : canon b) (v : valBE a = valBE b) : a = b := by
  rw [valBE_eq, valBE_eq] at v
  obtain ⟨da, na, ta⟩ := canon_rev a ha
  obtain ⟨db, nb, tb⟩ := canon_rev b hb
  have la := lt_pow _ da
  have lb := lt_pow _ db
  simp only [List.length_reverse] at la lb ta tb
  have len : a.length = b.length := by
    have : a.length ≠ 0 := by simpa using ha.1
    have : b.length ≠ 0 := by simpa using hb.1
    rcases Nat.lt_trichotomy a.length b.length with h | h | h
    · have := pow_le _ db nb (tb (by omega))
      have := Nat.pow_le_pow_right (by decide : 10 > 0) (show a.length ≤ b.length - 1 by omega)
      simp only [List.length_reverse] at *
      omega
    · exact h
    · have := pow_le _ da na (ta (by omega))
      have := Nat.pow_le_pow_right (by decide : 10 > 0) (show b.length ≤ a.length - 1 by omega)
      simp only [List.length_reverse] at *
      omega
  have := same_length _ _ da db (by simpa using len) v
  simpa using this

/-- Two IDs given the same number by `number` are the same ID. -/
theorem number_inj (pre a b : List Nat) (n : Nat) (ha : number pre a = some n) (hb : number pre b = some n) :
    a = b := by
  simp only [number] at ha hb
  split at ha
  · split at hb
    · rename_i h1 h2
      simp only [Option.some.injEq] at ha hb
      have e := canon_inj _ _ h1.2.1 h2.2.1 (by omega)
      rw [← List.take_append_drop pre.length a, ← List.take_append_drop pre.length b, h1.1, h2.1, e]
    · contradiction
  · contradiction

/-- Seven digits never overflow the `u32` accumulator: every partial value is below 10 ^ 7. -/
theorem number_fits (d : List Nat) (h : d.all isDigit = true) (l : d.length ≤ 7) : valBE d < 2 ^ 32 := by
  rw [valBE_eq]
  have := lt_pow d.reverse (by simpa using h)
  have := Nat.pow_le_pow_right (by decide : 10 > 0) (show d.reverse.length ≤ 7 by simpa using l)
  have : (10 : Nat) ^ 7 < 2 ^ 32 := by decide
  omega

end Sessions.Lookup
