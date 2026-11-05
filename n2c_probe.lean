/-
N2c probe: generic rank lemmas for the rightmost-pivot lower bound.
-/
import StaircasePort.Pivot

set_option maxHeartbeats 0

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

section generic
variable {K : Type*} [Field K] {a b : ℕ}

/-- NE-block rank is monotone in the row cut. -/
lemma rk_rows_mono (q : Matrix (Fin a) (Fin b) K) {X X' Y : ℕ} (h : X ≤ X') :
    rk q X Y ≤ rk q X' Y := by
  rw [rk, rk]
  refine (Matrix.rank_submatrix_le _ (fun r : {r : Fin a // r.val < X} =>
    (⟨r.1, by have := r.2; omega⟩ : {r : Fin a // r.val < X'}))
    (fun c => c)).trans_eq ?_
  congr 1
  ext i j
  rfl

/-- NE-block rank is monotone in the column cut (larger `Y` = smaller block). -/
lemma rk_cols_mono (q : Matrix (Fin a) (Fin b) K) {X Y Y' : ℕ} (h : Y' ≤ Y) :
    rk q X Y ≤ rk q X Y' := by
  rw [rk, rk]
  refine (Matrix.rank_submatrix_le _ (fun r => r)
    (fun c : {c : Fin b // Y ≤ c.val} =>
      (⟨c.1, by have := c.2; omega⟩ : {c : Fin b // Y' ≤ c.val}))).trans_eq ?_
  congr 1
  ext i j
  rfl

/-- Trivial height bound: the NE block has `X` rows. -/
lemma rk_le_height (q : Matrix (Fin a) (Fin b) K) (X Y : ℕ) : rk q X Y ≤ X := by
  rw [rk]
  refine (Matrix.rank_le_card_height _).trans ?_
  have hc : Fintype.card {r : Fin a // r.val < X} = X := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun r : Fin a => r.val < X) = Finset.range X := by
      ext r; simp [Finset.mem_range]
    rw [this, Finset.card_range]
  rw [hc]

/-- Trivial width bound: the NE block has `b - Y` columns (for `Y ≤ b`). -/
lemma rk_le_width (q : Matrix (Fin a) (Fin b) K) (X Y : ℕ) (hY : Y ≤ b) :
    rk q X Y ≤ b - Y := by
  rw [rk]
  refine (Matrix.rank_le_card_width _).trans ?_
  have hc : Fintype.card {c : Fin b // Y ≤ c.val} = b - Y := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun c : Fin b => Y ≤ c.val) =
        (Finset.range (b - Y)).map ⟨fun v => (⟨b - Y - 1 - v, by omega⟩ : Fin b), by
          intro u v huv
          simp only [Fin.mk.injEq] at huv
          omega⟩ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_range, Fin.mk.injEq]
      constructor
      · intro hc
        exact ⟨b - Y - 1 - c.val, by omega, by omega⟩
      · rintro ⟨v, hv, rfl⟩
        simp only; omega
    rw [this, Finset.card_map, Finset.card_range]
  rw [hc]

/-- A nonzero `n × n` minor forces `n ≤` the NE-block rank. -/
lemma rk_ge_of_det (q : Matrix (Fin a) (Fin b) K) (X Y : ℕ) {n : ℕ}
    (R : Fin n → {r : Fin a // r.val < X}) (C : Fin n → {c : Fin b // Y ≤ c.val})
    (hdet : (Matrix.of fun i j => q (R i).1 (C j).1).det ≠ 0) : n ≤ rk q X Y := by
  have h1 : (Matrix.of fun i j => q (R i).1 (C j).1).rank = n := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
  rw [← h1, rk]
  exact Matrix.rank_submatrix_le _ R C

end generic

section ispiv
variable {a b : ℕ}

/-- IsPiv from four exact rank values. -/
lemma isPiv_of_exact (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j = k) (hB : rk q (i+1) j = k+1)
    (hC : rk q i (j+1) = k) (hD : rk q (i+1) (j+1) = k) : IsPiv q i j := by
  unfold IsPiv
  rw [hA, hB, hC, hD]
  omega

/-- IsPiv from two-sided bounds: uppers on all four blocks + lower bounds on the
`(i+1,j)` block (size `k+1`) and the `(i,j+1)` block (size `k`). -/
lemma isPiv_of_bounds (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j ≤ k) (hB : rk q (i+1) j ≤ k+1)
    (hC : rk q i (j+1) ≤ k) (hD : rk q (i+1) (j+1) ≤ k)
    (hBlo : k+1 ≤ rk q (i+1) j) (hClo : k ≤ rk q i (j+1)) : IsPiv q i j := by
  have hAe : rk q i j = k :=
    le_antisymm hA (hClo.trans (rk_cols_mono q (by omega : j + 1 ≥ j)))
  have hCe : rk q i (j+1) = k := le_antisymm hC hClo
  have hDe : rk q (i+1) (j+1) = k := le_antisymm hD (hClo.trans (rk_rows_mono q (by omega)))
  exact isPiv_of_exact q i j k hAe (le_antisymm hB hBlo) hCe hDe

end ispiv

end StaircasePort.Stair
