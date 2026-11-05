/- N2b work file: the 47-term decomposition of the staircase corner.

`corStairQ M i j` is a BILINEAR function of `M`, so the NE-rank bound cannot hold for an
arbitrary `M` (verified in extract/verify_n2b_statement.py check (A): a random `M` violates the
pinned bound on many blocks).  The honest hypothesis shape is the PAIR MATRIX
`stairPairM x₁ y₁ x₂ y₂ = (1 - x₁y₁) ⊗ₖ (1 - x₂y₂)` -- exactly the matrix N2d consumes.  Its
corner expands into 47 rank-1 terms grouped by shared coordinate (check_stair.structure),
which is what `rank_le_support_cut` consumes. -/
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxHeartbeats 0

/-! ## 1. List-sum helpers (ℚ-valued) -/

namespace N2bKit

variable {α β γ : Type*}

lemma sum_map_add (l : List α) (f g : α → ℚ) :
    (l.map fun s => f s + g s).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma sum_map_sub (l : List α) (f g : α → ℚ) :
    (l.map fun s => f s - g s).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma sum_map_four (l : List α) (f₁ f₂ f₃ f₄ : α → ℚ) :
    (l.map fun s => f₁ s - f₂ s - f₃ s + f₄ s).sum
      = (l.map f₁).sum - (l.map f₂).sum - (l.map f₃).sum + (l.map f₄).sum := by
  simp only [sum_map_add, sum_map_sub]; ring

lemma sum_map_mul_right (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map fun s => f s * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma sum_map_congr (l : List α) {f g : α → ℚ} (h : ∀ s ∈ l, f s = g s) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h s (by simp), ih (fun x hx => h x (by simp [hx]))]

lemma sum_sum_mul (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) :
    (lR.map fun t => (lL.map fun s => f s * g t).sum).sum
      = (lL.map f).sum * (lR.map g).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_mul_right, ih, mul_add]

/-- Regrouping by shared coordinate: `Σ_t Σ_s [k₁ s = k₂ t] f s g t` is the sum over the
finitely many coordinate values of the products of the two partial sums. -/
lemma sum_sum_ite_eq_group [Fintype γ] [DecidableEq γ]
    (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) (k₁ : α → γ) (k₂ : β → γ) :
    (lR.map fun t => (lL.map fun s => if k₁ s = k₂ t then f s * g t else (0 : ℚ)).sum).sum
      = ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
          (lR.map fun t => if k₂ t = c then g t else 0).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [ih]
    congr 1
    have hH : (lL.map fun s => if k₁ s = k₂ t then f s * g t else (0 : ℚ)).sum
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      rw [← sum_map_mul_right (lL) (fun s => if k₁ s = k₂ t then f s else 0) (g t)]
      exact sum_map_congr lL (fun s _ => by split_ifs <;> ring)
    have hR : (∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
          (if k₂ t = c then g t else 0))
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      have hpt : ∀ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
            (if k₂ t = c then g t else 0)
          = (if k₂ t = c then (lL.map fun s => if k₁ s = c then f s else 0).sum * g t else 0) := by
        intro c; split_ifs <;> ring
      simp only [hpt]
      rw [Finset.sum_eq_single (k₂ t)]
      · simp
      · intro c _ hc; simp [show k₂ t ≠ c from Ne.symm hc]
      · intro h; exact absurd (Finset.mem_univ _) h
    exact hH.trans hR.symm

end N2bKit

/-! ## 2. The pair matrix and the four expansion pieces -/

/-- The pair matrix of four label vectors: N2b's honest hypothesis shape (the matrix N2d
consumes, `qM ((1 - x₁y₁) ⊗ₖ (1 - x₂y₂))`). -/
noncomputable def stairPairM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) : Matrix (Pr 23) (Pr 23) ℚ :=
  (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂)

theorem stairPairM_apply (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (a b : Pr 23) :
    stairPairM x₁ y₁ x₂ y₂ a b
      = ((if a.1 = b.1 then 1 else 0) - x₁ a.1 * y₁ b.1)
        * ((if a.2 = b.2 then 1 else 0) - x₂ a.2 * y₂ b.2) := by
  simp only [stairPairM, Matrix.kronecker_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply]

/-- The identity piece — vanishes pointwise, because row-family and column-family cells are
disjoint (`stairLR_disjoint`). -/
noncomputable def stairT1 (s t : ℚ × Pr 23) : ℚ :=
  if s.2.1 = t.2.1 then (if s.2.2 = t.2.2 then 1 else 0) else 0

/-- The k-piece: FIRST cell coordinate shared. -/
noncomputable def stairT2 (x₂ y₂ : Fin 23 → ℚ) (s t : ℚ × Pr 23) : ℚ :=
  if s.2.1 = t.2.1 then x₂ s.2.2 * y₂ t.2.2 else 0

/-- The l-piece: SECOND cell coordinate shared. -/
noncomputable def stairT3 (x₁ y₁ : Fin 23 → ℚ) (s t : ℚ × Pr 23) : ℚ :=
  if s.2.2 = t.2.2 then x₁ s.2.1 * y₁ t.2.1 else 0

/-- The whole piece (the `1 ⊗ₖ 1` term). -/
noncomputable def stairT4 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (s t : ℚ × Pr 23) : ℚ :=
  x₁ s.2.1 * y₁ t.2.1 * x₂ s.2.2 * y₂ t.2.2

theorem stairPairM_expand (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (s t : ℚ × Pr 23) :
    stairPairM x₁ y₁ x₂ y₂ s.2 t.2
      = stairT1 s t - stairT2 x₂ y₂ s t - stairT3 x₁ y₁ s t + stairT4 x₁ y₁ x₂ y₂ s t := by
  rw [stairPairM_apply]
  simp only [stairT1, stairT2, stairT3, stairT4]
  by_cases h1 : s.2.1 = t.2.1 <;> by_cases h2 : s.2.2 = t.2.2 <;> simp [h1, h2] <;> ring

/-! ## 3. The term factors (check_stair.structure grouping) -/

/-- l-group row factor: corner-row family `i`'s cells carrying SECOND coordinate `l`, weighted
by the `x₁` label. -/
noncomputable def stairUl (x₁ : Fin 23 → ℚ) (l : Fin 23) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if s.2.2 = l then s.1 * x₁ s.2.1 else 0).sum

noncomputable def stairVl (y₁ : Fin 23 → ℚ) (l : Fin 23) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if s.2.2 = l then s.1 * y₁ s.2.1 else 0).sum

/-- k-group row factor: FIRST coordinate `k`, weighted by the `x₂` label. -/
noncomputable def stairUk (x₂ : Fin 23 → ℚ) (k : Fin 23) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if s.2.1 = k then s.1 * x₂ s.2.2 else 0).sum

noncomputable def stairVk (y₂ : Fin 23 → ℚ) (k : Fin 23) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if s.2.1 = k then s.1 * y₂ s.2.2 else 0).sum

noncomputable def stairPw (x₁ x₂ : Fin 23 → ℚ) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => s.1 * x₁ s.2.1 * x₂ s.2.2).sum

noncomputable def stairQw (y₁ y₂ : Fin 23 → ℚ) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => s.1 * y₁ s.2.1 * y₂ s.2.2).sum

/-- Row factor of term `t`: `t < 23` = l-group, `23 ≤ t < 46` = k-group, `t = 46` = whole. -/
noncomputable def stairTermRow (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t i : ℕ) : ℚ :=
  if h : t < 23 then -stairUl x₁ ⟨t, h⟩ i
  else if _h2 : t < 46 then -stairUk x₂ ⟨t - 23, by omega⟩ i
  else stairPw x₁ x₂ i

noncomputable def stairTermCol (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t j : ℕ) : ℚ :=
  if h : t < 23 then stairVl y₁ ⟨t, h⟩ j
  else if _h2 : t < 46 then stairVk y₂ ⟨t - 23, by omega⟩ j
  else stairQw y₁ y₂ j

noncomputable def stairTermE (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t i j : ℕ) : ℚ :=
  stairTermRow x₁ y₁ x₂ y₂ t i * stairTermCol x₁ y₁ x₂ y₂ t j

/-- Term `t` as a rank-≤1 matrix on the 45×45 corner. -/
noncomputable def stairTermM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) :
    Matrix (Fin 45) (Fin 45) ℚ :=
  vecMulVec (fun r => stairTermRow x₁ y₁ x₂ y₂ t.val r.val)
    (fun c => stairTermCol x₁ y₁ x₂ y₂ t.val c.val)

/-! ## 4. The four double sums of the expansion -/

noncomputable def stairDS1 (i j : ℕ) : ℚ :=
  ((RtermsStair j).map fun t =>
    ((LtermsStair i).map fun s => (s.1 * stairT1 s t) * t.1).sum).sum

noncomputable def stairDS2 (x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) : ℚ :=
  ((RtermsStair j).map fun t =>
    ((LtermsStair i).map fun s => (s.1 * stairT2 x₂ y₂ s t) * t.1).sum).sum

noncomputable def stairDS3 (x₁ y₁ : Fin 23 → ℚ) (i j : ℕ) : ℚ :=
  ((RtermsStair j).map fun t =>
    ((LtermsStair i).map fun s => (s.1 * stairT3 x₁ y₁ s t) * t.1).sum).sum

noncomputable def stairDS4 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) : ℚ :=
  ((RtermsStair j).map fun t =>
    ((LtermsStair i).map fun s => (s.1 * stairT4 x₁ y₁ x₂ y₂ s t) * t.1).sum).sum

/-! ## 5. The corner as a double sum, split into the four pieces -/

theorem corStairQ_double (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) i j
      = ((RtermsStair j).map fun t =>
          ((LtermsStair i).map fun s => (s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2) * t.1).sum).sum := by
  simp only [corStairQ]
  refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
  exact (N2bKit.sum_map_mul_right (LtermsStair i)
    (fun s => s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2) t.1).symm

theorem corStairQ_split (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) i j
      = stairDS1 i j - stairDS2 x₂ y₂ i j - stairDS3 x₁ y₁ i j
        + stairDS4 x₁ y₁ x₂ y₂ i j := by
  rw [corStairQ_double]
  have hstep : ∀ t : ℚ × Pr 23,
      ((LtermsStair i).map fun s => (s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2) * t.1).sum
      = ((LtermsStair i).map fun s => (s.1 * stairT1 s t) * t.1).sum
        - ((LtermsStair i).map fun s => (s.1 * stairT2 x₂ y₂ s t) * t.1).sum
        - ((LtermsStair i).map fun s => (s.1 * stairT3 x₁ y₁ s t) * t.1).sum
        + ((LtermsStair i).map fun s => (s.1 * stairT4 x₁ y₁ x₂ y₂ s t) * t.1).sum := by
    intro t
    rw [show (List.map (fun s : ℚ × Pr 23 =>
          (s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2) * t.1) (LtermsStair i))
        = List.map (fun s : ℚ × Pr 23 =>
            (s.1 * stairT1 s t) * t.1 - (s.1 * stairT2 x₂ y₂ s t) * t.1
            - (s.1 * stairT3 x₁ y₁ s t) * t.1 + (s.1 * stairT4 x₁ y₁ x₂ y₂ s t) * t.1)
          (LtermsStair i) from
      List.map_congr_left (fun s _ => by rw [stairPairM_expand]; ring)]
    exact N2bKit.sum_map_four _ _ _ _ _
  simp only [stairDS1, stairDS2, stairDS3, stairDS4]
  rw [List.map_congr_left (fun t _ => hstep t)]
  exact N2bKit.sum_map_four _ _ _ _ _

/-! ## 6. Evaluation of the four pieces -/

theorem stairDS1_eq_zero (i j : ℕ) (hi : i < 45) (hj : j < 45) : stairDS1 i j = 0 := by
  simp only [stairDS1]
  refine List.sum_eq_zero (fun a ha => ?_)
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  refine List.sum_eq_zero (fun b hb => ?_)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
  have hne := stairLR_disjoint i j hi hj s hs t ht
  simp only [stairT1]
  by_cases h1 : s.2.1 = t.2.1 <;> by_cases h2 : s.2.2 = t.2.2
  · exact absurd (Prod.ext h1 h2) hne
  · simp [h1, h2]
  · simp [h1]
  · simp [h1]

theorem stairDS2_eq (x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) :
    stairDS2 x₂ y₂ i j = ∑ k : Fin 23, stairUk x₂ k i * stairVk y₂ k j := by
  simp only [stairDS2, stairUk, stairVk]
  rw [← N2bKit.sum_sum_ite_eq_group (lR := RtermsStair j) (lL := LtermsStair i)
    (f := fun s => s.1 * x₂ s.2.2) (g := fun t => t.1 * y₂ t.2.2)
    (k₁ := fun s => s.2.1) (k₂ := fun t => t.2.1)]
  exact N2bKit.sum_map_congr _ (fun t _ => N2bKit.sum_map_congr _ (fun s _ => by
    simp only [stairT2]; split_ifs <;> ring))

theorem stairDS3_eq (x₁ y₁ : Fin 23 → ℚ) (i j : ℕ) :
    stairDS3 x₁ y₁ i j = ∑ l : Fin 23, stairUl x₁ l i * stairVl y₁ l j := by
  simp only [stairDS3, stairUl, stairVl]
  rw [← N2bKit.sum_sum_ite_eq_group (lR := RtermsStair j) (lL := LtermsStair i)
    (f := fun s => s.1 * x₁ s.2.1) (g := fun t => t.1 * y₁ t.2.1)
    (k₁ := fun s => s.2.2) (k₂ := fun t => t.2.2)]
  exact N2bKit.sum_map_congr _ (fun t _ => N2bKit.sum_map_congr _ (fun s _ => by
    simp only [stairT3]; split_ifs <;> ring))

theorem stairDS4_eq (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) :
    stairDS4 x₁ y₁ x₂ y₂ i j = stairPw x₁ x₂ i * stairQw y₁ y₂ j := by
  simp only [stairDS4, stairPw, stairQw]
  rw [← N2bKit.sum_sum_mul (lR := RtermsStair j) (lL := LtermsStair i)
    (f := fun s => s.1 * x₁ s.2.1 * x₂ s.2.2) (g := fun t => t.1 * y₁ t.2.1 * y₂ t.2.2)]
  exact N2bKit.sum_map_congr _ (fun t _ => N2bKit.sum_map_congr _ (fun s _ => by
    simp only [stairT4]; ring))

/-! ## 7. The term sum -/

theorem stair_termE_lt (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 23) (i j : ℕ) :
    stairTermE x₁ y₁ x₂ y₂ t.val i j = -(stairUl x₁ t i * stairVl y₁ t j) := by
  simp only [stairTermE, stairTermRow, stairTermCol]
  rw [dif_pos t.isLt, dif_pos t.isLt]
  ring

theorem stair_termE_k (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (k : Fin 23) (i j : ℕ) :
    stairTermE x₁ y₁ x₂ y₂ (23 + k.val) i j = -(stairUk x₂ k i * stairVk y₂ k j) := by
  simp only [stairTermE, stairTermRow, stairTermCol, dif_neg (show ¬ (23 + k.val < 23) by omega),
    dif_pos (show 23 + k.val < 46 by omega)]
  ring

theorem stair_termE_46 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) :
    stairTermE x₁ y₁ x₂ y₂ 46 i j = stairPw x₁ x₂ i * stairQw y₁ y₂ j := by
  simp only [stairTermE, stairTermRow, stairTermCol, dif_neg (show ¬ (46 < 23) by omega),
    dif_neg (show ¬ (46 < 46) by omega)]

theorem stair_termE_sum (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) :
    (∑ t ∈ Finset.range 47, stairTermE x₁ y₁ x₂ y₂ t i j)
      = -(∑ l : Fin 23, stairUl x₁ l i * stairVl y₁ l j)
        - (∑ k : Fin 23, stairUk x₂ k i * stairVk y₂ k j)
        + stairPw x₁ x₂ i * stairQw y₁ y₂ j := by
  have e1 : (∑ t ∈ Finset.range 23, stairTermE x₁ y₁ x₂ y₂ t i j)
      = -(∑ l : Fin 23, stairUl x₁ l i * stairVl y₁ l j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => stairTermE x₁ y₁ x₂ y₂ t i j) 23,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun l _ => stair_termE_lt x₁ y₁ x₂ y₂ l i j)
  have e2 : (∑ k ∈ Finset.range 23, stairTermE x₁ y₁ x₂ y₂ (23 + k) i j)
      = -(∑ k : Fin 23, stairUk x₂ k i * stairVk y₂ k j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => stairTermE x₁ y₁ x₂ y₂ (23 + t) i j) 23,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => stair_termE_k x₁ y₁ x₂ y₂ k i j)
  have e3 : stairTermE x₁ y₁ x₂ y₂ 46 i j = stairPw x₁ x₂ i * stairQw y₁ y₂ j :=
    stair_termE_46 x₁ y₁ x₂ y₂ i j
  rw [← Finset.sum_range_add_sum_Ico (fun t => stairTermE x₁ y₁ x₂ y₂ t i j)
      (show 23 ≤ 47 by omega),
    show Finset.Ico 23 47 = insert 46 (Finset.Ico 23 46) by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega,
    Finset.sum_insert (by simp only [Finset.mem_Ico]; omega),
    Finset.sum_Ico_eq_sum_range]
  rw [e1, e2, e3]
  ring

/-- The corner of the pair matrix is the sum of the 47 rank-1 terms. -/
theorem corStairQ_pair_expand (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) (hi : i < 45) (hj : j < 45) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) i j
      = ∑ t ∈ Finset.range 47, stairTermE x₁ y₁ x₂ y₂ t i j := by
  rw [corStairQ_split, stairDS1_eq_zero i j hi hj, stairDS2_eq, stairDS3_eq, stairDS4_eq,
    stair_termE_sum]
  ring

/-- Matrix form: the whole 45×45 corner is `∑ t, stairTermM t`. -/
theorem stairCornerQOf_pair_eq_sum (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) = ∑ t : Fin 47, stairTermM x₁ y₁ x₂ y₂ t := by
  ext r c
  have h1 : (∑ t : Fin 47, stairTermM x₁ y₁ x₂ y₂ t) r c
      = ∑ t : Fin 47, stairTermM x₁ y₁ x₂ y₂ t r c := Matrix.sum_apply r c _ _
  rw [h1]
  show corStairQ (stairPairM x₁ y₁ x₂ y₂) r.val c.val
      = ∑ t : Fin 47, stairTermM x₁ y₁ x₂ y₂ t r c
  rw [corStairQ_pair_expand x₁ y₁ x₂ y₂ r.val c.val r.isLt c.isLt]
  exact (Fin.sum_univ_eq_sum_range
      (fun t => stairTermE x₁ y₁ x₂ y₂ t r.val c.val) 47).symm.trans
    (Finset.sum_congr rfl (fun t _ => by
      simp only [stairTermM, stairTermE, Matrix.vecMulVec_apply]))

end StaircasePort.Stair
