/- N2b probe P2: definitions, disjointness pin, coherence pins, vanishing lemmas. -/
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxHeartbeats 0

/-! ## Definitions -/

/-- The pair matrix of the four label vectors (N2b's honest hypothesis shape). -/
noncomputable def stairPairM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) : Matrix (Pr 23) (Pr 23) ℚ :=
  (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂)

/-- Label-free Nat coordinate lists of the family cells. -/
def stairLfstN (i : ℕ) : List ℕ := (LtermsStair i).map fun s => (s.2.1 : ℕ)
def stairLsndN (i : ℕ) : List ℕ := (LtermsStair i).map fun s => (s.2.2 : ℕ)
def stairRfstN (j : ℕ) : List ℕ := (RtermsStair j).map fun s => (s.2.1 : ℕ)
def stairRsndN (j : ℕ) : List ℕ := (RtermsStair j).map fun s => (s.2.2 : ℕ)
def stairLcellN (i : ℕ) : List (ℕ × ℕ) :=
  (LtermsStair i).map fun s => ((s.2.1 : ℕ), (s.2.2 : ℕ))
def stairRcellN (j : ℕ) : List (ℕ × ℕ) :=
  (RtermsStair j).map fun s => ((s.2.1 : ℕ), (s.2.2 : ℕ))

/-- The l-group factors (shared SECOND coordinate l): U from L-cells, V from R-cells. -/
noncomputable def stairUl (x₁ : Fin 23 → ℚ) (l : Fin 23) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if s.2.2 = l then s.1 * x₁ s.2.1 else 0).sum
noncomputable def stairVl (y₁ : Fin 23 → ℚ) (l : Fin 23) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if s.2.2 = l then s.1 * y₁ s.2.1 else 0).sum

/-- The k-group factors (shared FIRST coordinate k). -/
noncomputable def stairUk (x₂ : Fin 23 → ℚ) (k : Fin 23) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if s.2.1 = k then s.1 * x₂ s.2.2 else 0).sum
noncomputable def stairVk (y₂ : Fin 23 → ℚ) (k : Fin 23) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if s.2.1 = k then s.1 * y₂ s.2.2 else 0).sum

/-- The whole-term factors. -/
noncomputable def stairPw (x₁ x₂ : Fin 23 → ℚ) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => s.1 * x₁ s.2.1 * x₂ s.2.2).sum
noncomputable def stairQw (y₁ y₂ : Fin 23 → ℚ) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => s.1 * y₁ s.2.1 * y₂ s.2.2).sum

/-- The 47-term family: t < 23 = l-groups (second coordinate), 23 ≤ t < 46 = k-groups
(first coordinate), t = 46 = the whole term. Every member is a vecMulVec (rank ≤ 1). -/
noncomputable def stairTermM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    Fin 47 → Matrix (Fin 45) (Fin 45) ℚ :=
  fun t =>
    if h : t.val < 23 then
      vecMulVec (fun i : Fin 45 => -stairUl x₁ ⟨t.val, h⟩ i.val)
        (fun j : Fin 45 => stairVl y₁ ⟨t.val, h⟩ j.val)
    else if h2 : t.val < 46 then
      vecMulVec (fun i : Fin 45 => -stairUk x₂ ⟨t.val - 23, by omega⟩ i.val)
        (fun j : Fin 45 => stairVk y₂ ⟨t.val - 23, by omega⟩ j.val)
    else
      vecMulVec (fun i : Fin 45 => stairPw x₁ x₂ i.val)
        (fun j : Fin 45 => stairQw y₁ y₂ j.val)

/-! ## Disjointness pin: L-cells ∩ R-cells = ∅ everywhere (the design() assert) -/

theorem stairLR_disjoint_pin :
    ((List.range 45).all fun i => (List.range 45).all fun j =>
      decide (∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q)) = true := by decide

lemma mem_stairLcellN {i : ℕ} {s : ℚ × Pr 23} (hs : s ∈ LtermsStair i) :
    ((s.2.1 : ℕ), (s.2.2 : ℕ)) ∈ stairLcellN i := by
  unfold LtermsStair stairLcellN at hs ⊢
  rw [List.mem_map] at hs
  obtain ⟨z, hz, hzs⟩ := hs
  exact List.mem_map.mpr ⟨z, hz, by simp [hzs]⟩

lemma mem_stairRcellN {j : ℕ} {t : ℚ × Pr 23} (ht : t ∈ RtermsStair j) :
    ((t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ stairRcellN j := by
  unfold RtermsStair stairRcellN at ht ⊢
  rw [List.mem_map] at ht
  obtain ⟨z, hz, hzt⟩ := ht
  exact List.mem_map.mpr ⟨z, hz, by simp [hzt]⟩

lemma stairLR_disjoint (i j : ℕ) (hi : i < 45) (hj : j < 45)
    (s : ℚ × Pr 23) (hs : s ∈ LtermsStair i)
    (t : ℚ × Pr 23) (ht : t ∈ RtermsStair j) : s.2 ≠ t.2 := by
  have hp := (List.all_eq_true.mp stairLR_disjoint_pin i (List.mem_range.mpr hi))
    j (List.mem_range.mpr hj)
  have hcert : ∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q := Decidable.eq_true hp
  intro hst
  exact hcert _ (mem_stairLcellN hs) _ (mem_stairRcellN ht)
    (Prod.ext (congrArg (fun c : Pr 23 => (c.1 : ℕ)) hst)
      (congrArg (fun c : Pr 23 => (c.2 : ℕ)) hst))

/-! ## Coherence pins: the raw stairNESr/Sc data of NEBlocks.lean are exactly the
coordinate-membership sets of the Lean family definitions. -/

theorem stairNESr_coh :
    ((List.range 47).all fun t => (List.range 45).all fun i =>
      decide ((i ∈ stairNESr.getD t [] ↔
        ((t < 23 ∧ t ∈ stairLsndN i) ∨ (23 ≤ t ∧ t < 46 ∧ t - 23 ∈ stairLfstN i) ∨ 46 ≤ t))))
      = true := by decide

theorem stairNESc_coh :
    ((List.range 47).all fun t => (List.range 45).all fun j =>
      decide ((j ∈ stairNESc.getD t [] ↔
        ((t < 23 ∧ t ∈ stairRsndN j) ∨ (23 ≤ t ∧ t < 46 ∧ t - 23 ∈ stairRfstN j) ∨ 46 ≤ t))))
      = true := by decide

/-! ## Vanishing lemmas: a factor sum is 0 when the coordinate is not referenced. -/

lemma stairUl_eq_zero (x₁ : Fin 23 → ℚ) (l : Fin 23) (i : ℕ)
    (h : l ∉ (LtermsStair i).map fun s => s.2.2) : stairUl x₁ l i = 0 :=
  List.sum_map_ite_eq_zero (LtermsStair i) (fun s => s.2.2) (fun s => s.1 * x₁ s.2.1) l h

lemma stairVl_eq_zero (y₁ : Fin 23 → ℚ) (l : Fin 23) (j : ℕ)
    (h : l ∉ (RtermsStair j).map fun s => s.2.2) : stairVl y₁ l j = 0 :=
  List.sum_map_ite_eq_zero (RtermsStair j) (fun s => s.2.2) (fun s => s.1 * y₁ s.2.1) l h

lemma stairUk_eq_zero (x₂ : Fin 23 → ℚ) (k : Fin 23) (i : ℕ)
    (h : k ∉ (LtermsStair i).map fun s => s.2.1) : stairUk x₂ k i = 0 :=
  List.sum_map_ite_eq_zero (LtermsStair i) (fun s => s.2.1) (fun s => s.1 * x₂ s.2.2) k h

lemma stairVk_eq_zero (y₂ : Fin 23 → ℚ) (k : Fin 23) (j : ℕ)
    (h : k ∉ (RtermsStair j).map fun s => s.2.1) : stairVk y₂ k j = 0 :=
  List.sum_map_ite_eq_zero (RtermsStair j) (fun s => s.2.1) (fun s => s.1 * y₂ s.2.2) k h

/-- Nat-level non-membership (the pinned data form) lifts to Fin-level non-membership. -/
lemma not_mem_map_coord {coord : Pr 23 → Fin 23} {l : List (ℚ × Pr 23)} {n : ℕ} {v : Fin 23}
    (hv : (v : ℕ) = n) (h : n ∉ l.map fun s => (coord s.2 : ℕ)) :
    v ∉ l.map fun s => coord s.2 := by
  intro hm
  obtain ⟨s, hs, hsl⟩ := List.mem_map.mp hm
  exact h (List.mem_map.mpr ⟨s, hs, (congrArg (fun c : Fin 23 => (c : ℕ)) hsl).trans hv⟩)

end StaircasePort.Stair
