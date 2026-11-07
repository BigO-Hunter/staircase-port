import StaircasePort.D2Chunks
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Stage 2 — the packed-code core (width-parametric), ported from the platform's Proved r6
`Thm_IntMul_Kappa_R6_Bit_NB_sc_prog` (2436 ln, 0 sorry) — the reusable HALF of label port #2

`NB_sc_prog` is not one statement: it is the packed-representation layer (bit lemmas,
`fieldOf`, `Good` trees, `pget`/`ltSet`, `fieldOf_catB`, then the stage-word consumer
proofs `foldl_mvP_eq`/`genP_eq`/`segChk_sound`). The GENERIC half — the lemmas that hold at
any field width `B` — is what ports cleanly and what this module carries:

* `testBit_fieldOf` — bit `t` of field `i` is bit `w*i + t` of the state (for `t < w`);
* `fieldOf_lt` — every field is `< 2^w`;
* `testBit_ge_of_lt` — a value `< 2^n` has no bits at or above `n`;
* `fieldOf_catB` — **decoding a packed list returns the list** (the round-trip law);
* `fieldOf_packCodes` — its wire-level corollary for `QT.packCodes`.

Why this matters for the D2 retarget: the d2 word needs 17-bit fields (16 cannot hold code
65815 — `QT.width16_fails`), and every packing lemma in the platform file is stated at a
fixed 16. Proving them at parametric `B` is what lets the 17-bit seed be reasoned about at
all; `fieldOf_packCodes` turns the Python-side round-trip certificate into a Lean theorem.

Still platform-side (NOT ported here — they consume the stage-word packs, which need the
absent R6 Loc/GenData encoder): `Good`/`LT` tree layer (`ltGet_ltSet`, `good_mkTree`,
`pget_pset`), `foldl_mvP_eq`, `genP_eq`, `segChk_sound`, and the `supG`/`gs` table checks.
-/

namespace StaircasePort.QP

open StaircasePort.QT

/-- Bit `t` of field `i` is bit `w*i + t` of the state. -/
theorem testBit_fieldOf (X w i t : ℕ) :
    (fieldOf X w i).testBit t = (decide (t < w) && X.testBit (w * i + t)) := by
  rw [fieldOf, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Bool.and_comm]

/-- Every field is `< 2^w`. -/
theorem fieldOf_lt (X w i : ℕ) : fieldOf X w i < 2 ^ w := by
  rw [fieldOf]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

/-- A value `< 2^n` has no bits at or above `n`. -/
theorem testBit_ge_of_lt {x n m : ℕ} (hx : x < 2 ^ n) (hm : n ≤ m) : x.testBit m = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have : x / 2 ^ m = 0 := by
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hm)
  rw [this]
  simp

/-- **The round-trip law**: decoding field `k` of the packed list returns element `k`. -/
theorem fieldOf_catB (B : ℕ) : ∀ (l : List ℕ), (∀ x ∈ l, x < 2 ^ B) → ∀ k,
    fieldOf (catB B l) B k = l.getD k 0
  | [], _, k => by
    simp only [catB, List.foldr_nil]
    apply Nat.eq_of_testBit_eq
    intro t
    simp [fieldOf]
  | x :: l, hl, k => by
    have hx : x < 2 ^ B := hl x (by simp)
    have ih := fieldOf_catB B l (fun y hy => hl y (by simp [hy]))
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_fieldOf]
    show (decide (t < B) && (x ||| (catB B l <<< B)).testBit (B * k + t)) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      by_cases ht : t < B
      · simp [ht]
      · simp only [ht, decide_false, Bool.false_and]
        exact (testBit_ge_of_lt hx (by omega)).symm
    | succ k =>
      simp only [List.getD_cons_succ]
      rw [← ih k, testBit_fieldOf, testBit_ge_of_lt hx (by nlinarith)]
      by_cases ht : t < B
      · have h1 : B ≤ B * (k + 1) + t := by nlinarith
        simp only [ht, h1, decide_true, Bool.true_and, Bool.false_or]
        congr 1
        rw [Nat.mul_add, Nat.mul_one]; omega
      · simp [ht]

/-- Wire-level corollary: `packCodes` at width `w` decodes back to `f` on every wire. -/
theorem fieldOf_packCodes {w : ℕ} (f : ℕ → ℕ) (hf : ∀ i < QT.NL, f i < 2 ^ w)
    (k : ℕ) (hk : k < QT.NL) :
    fieldOf (catB w ((List.range QT.NL).map f)) w k = f k := by
  rw [fieldOf_catB]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    rfl
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hf i (List.mem_range.1 hi)

/-- The D2 slot-band seed decodes to the code it was packed from: `codeOf SG_slots0 w`
is the value in `SG_slots0`'s field `w` (the field/orientation convention pinned by
`D2Chunks`). -/
theorem slots0_decode (w : ℕ) :
    codeOf SG_slots0 w = fieldOf SG_slots0 17 w := rfl

end StaircasePort.QP
