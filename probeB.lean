/- N2b probe (RESCUE COPY, rebuilt from session context 2026-11-06 after the /private/tmp
wipe). Target: content of StaircasePort/Pivot.lean additions once a base project exists.
Verification status: P1 + P2 (Fin-23-indexed variant) ran GREEN pre-wipe via
`lake env lean`; the Nat-indexed rework + P3 part 1 below were WRITTEN but NOT re-run —
first job on a rebuilt base is to run this file. See RESUME.md for blueprints of the
remaining P3 part 2 / P4. -/
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxHeartbeats 0

/-! ## P1: generic List.sum helpers (GREEN pre-wipe) -/

lemma List.sum_map_add {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map fun s => f s + g s).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma List.sum_map_mul_right {α : Type*} (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map fun s => f s * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; rw [add_mul]

lemma List.sum_map_ite_eq_zero {α γ : Type*} [DecidableEq γ] (l : List α)
    (c : α → γ) (f : α → ℚ) (n : γ) (h : n ∉ l.map c) :
    (l.map fun s => if c s = n then f s else 0).sum = 0 := by
  induction l with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    simp only [List.mem_cons, not_or] at h
    rw [if_neg (Ne.symm h.1), ih h.2, add_zero]

/-- The regrouping lemma: Σ_t Σ_s [k₁ s = k₂ t]·f s·g t = Σ_c (Σ_{s: k₁s=c} f)(Σ_{t: k₂t=c} g). -/
lemma List.sum_sum_ite_eq_group {α β γ : Type*} [Fintype γ] [DecidableEq γ]
    (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) (k₁ : α → γ) (k₂ : β → γ) :
    (lR.map fun t => (lL.map fun s => if k₁ s = k₂ t then f s * g t else (0 : ℚ)).sum).sum
    = ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
        (lR.map fun t => if k₂ t = c then g t else 0).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    have head_eq : (lL.map fun s => if k₁ s = k₂ t then f s * g t else 0).sum
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      have hmap : lL.map (fun s => if k₁ s = k₂ t then f s * g t else 0)
          = lL.map (fun s => (if k₁ s = k₂ t then f s else 0) * g t) := by
        congr 1; funext s; split_ifs <;> ring
      rw [hmap, List.sum_map_mul_right]
    have key : ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
          (if k₂ t = c then g t else 0)
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      have hcong : ∀ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
            (if k₂ t = c then g t else 0)
          = if k₂ t = c then (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t else 0 := by
        intro c
        split_ifs with h
        · rw [← h]
        · ring
      rw [Finset.sum_congr rfl (fun c _ => hcong c)]
      exact Fintype.sum_ite_eq (k₂ t) _
    rw [head_eq, ih]
    simp only [mul_add]
    rw [Finset.sum_add_distrib, key]

/-- Product-of-sums: Σ_t Σ_s f s · g t = (Σ_s f s)·(Σ_t g t). (GREEN pre-wipe) -/
lemma List.sum_sum_mul {α β : Type*} (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) :
    (lR.map fun t => (lL.map fun s => f s * g t).sum).sum = (lL.map f).sum * (lR.map g).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_mul_right, ih, mul_add]

/-! ## P2: definitions, disjointness, coherence pins, vanishing (Nat-indexed rework;
the Fin-23-indexed predecessor ran GREEN pre-wipe; this rework NOT yet run) -/

/-- The pair matrix of the four label vectors (N2b's honest hypothesis shape — the
scaffold's arbitrary-M statement is FALSE, see RESUME.md counterexample). -/
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

/-- The l-group factors (shared SECOND coordinate l). Nat group index (matches the
pinned stairLsndN/stairRsndN data form). -/
noncomputable def stairUl (x₁ : Fin 23 → ℚ) (l i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if (s.2.2 : ℕ) = l then s.1 * x₁ s.2.1 else 0).sum
noncomputable def stairVl (y₁ : Fin 23 → ℚ) (l j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if (s.2.2 : ℕ) = l then s.1 * y₁ s.2.1 else 0).sum

/-- The k-group factors (shared FIRST coordinate k). -/
noncomputable def stairUk (x₂ : Fin 23 → ℚ) (k i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if (s.2.1 : ℕ) = k then s.1 * x₂ s.2.2 else 0).sum
noncomputable def stairVk (y₂ : Fin 23 → ℚ) (k j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if (s.2.1 : ℕ) = k then s.1 * y₂ s.2.2 else 0).sum

/-- The whole-term factors. -/
noncomputable def stairPw (x₁ x₂ : Fin 23 → ℚ) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => s.1 * x₁ s.2.1 * x₂ s.2.2).sum
noncomputable def stairQw (y₁ y₂ : Fin 23 → ℚ) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => s.1 * y₁ s.2.1 * y₂ s.2.2).sum

/-- The 47-term family, Nat-indexed entry function: n < 23 = l-groups, 23 ≤ n < 46 =
k-groups (k = n − 23), n = 46 = the whole term. -/
noncomputable def stairTermN (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (n i j : ℕ) : ℚ :=
  if n < 23 then -stairUl x₁ n i * stairVl y₁ n j
  else if n < 46 then -stairUk x₂ (n - 23) i * stairVk y₂ (n - 23) j
  else stairPw x₁ x₂ i * stairQw y₁ y₂ j

/-- Row/col factors of the n-th term (so stairTermM is literally a vecMulVec: rank ≤ 1). -/
noncomputable def stairTermRow (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (n : ℕ) (i : Fin 45) : ℚ :=
  if n < 23 then -stairUl x₁ n i.val
  else if n < 46 then -stairUk x₂ (n - 23) i.val
  else stairPw x₁ x₂ i.val

noncomputable def stairTermCol (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (n : ℕ) (j : Fin 45) : ℚ :=
  if n < 23 then stairVl y₁ n j.val
  else if n < 46 then stairVk y₂ (n - 23) j.val
  else stairQw y₁ y₂ j.val

/-- The Fin 47-indexed term matrices (consumed by rank_le_support_cut via submatrix). -/
noncomputable def stairTermM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    Fin 47 → Matrix (Fin 45) (Fin 45) ℚ :=
  fun t => vecMulVec (stairTermRow x₁ y₁ x₂ y₂ t.val) (stairTermCol x₁ y₁ x₂ y₂ t.val)

lemma stairTermM_apply (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) (i j : Fin 45) :
    stairTermM x₁ y₁ x₂ y₂ t i j = stairTermN x₁ y₁ x₂ y₂ t.val i.val j.val := by
  simp only [stairTermM, Matrix.vecMulVec_apply, stairTermRow, stairTermCol, stairTermN]
  split_ifs <;> ring

lemma stairTermM_rank_le (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) :
    (stairTermM x₁ y₁ x₂ y₂ t).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

lemma submatrix_vecMulVec {u : Fin 45 → ℚ} {v : Fin 45 → ℚ}
    {r : Type*} {c : Type*} (fr : r → Fin 45) (fc : c → Fin 45) :
    (vecMulVec u v).submatrix fr fc = vecMulVec (u ∘ fr) (v ∘ fc) := by
  ext a b
  simp [Matrix.submatrix_apply, Matrix.vecMulVec_apply]

/-! ## Disjointness pin: L-cells ∩ R-cells = ∅ everywhere (the design() assert) -/

theorem stairLR_disjoint_pin :
    ((List.range 45).all fun i => (List.range 45).all fun j =>
      decide (∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q)) = true := by decide

lemma mem_stairLcellN {i : ℕ} {s : ℚ × Pr 23} (hs : s ∈ LtermsStair i) :
    ((s.2.1 : ℕ), (s.2.2 : ℕ)) ∈ stairLcellN i :=
  List.mem_map.mpr ⟨s, hs, rfl⟩

lemma mem_stairRcellN {j : ℕ} {t : ℚ × Pr 23} (ht : t ∈ RtermsStair j) :
    ((t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ stairRcellN j :=
  List.mem_map.mpr ⟨t, ht, rfl⟩

lemma stairLR_disjoint (i j : ℕ) (hi : i < 45) (hj : j < 45)
    (s : ℚ × Pr 23) (hs : s ∈ LtermsStair i)
    (t : ℚ × Pr 23) (ht : t ∈ RtermsStair j) : s.2 ≠ t.2 := by
  have hp : decide (∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q) = true :=
    List.all_eq_true.mp
      ((List.all_eq_true.mp stairLR_disjoint_pin) i (List.mem_range.mpr hi))
      j (List.mem_range.mpr hj)
  have hcert : ∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q := of_decide_eq_true hp
  intro hst
  exact hcert _ (mem_stairLcellN hs) _ (mem_stairRcellN ht)
    (Prod.ext (congrArg (fun c : Pr 23 => (c.1 : ℕ)) hst)
      (congrArg (fun c : Pr 23 => (c.2 : ℕ)) hst))

/-! ## Coherence pins: raw stairNESr/Sc data == the Lean family coordinate sets -/

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

/-! ## Vanishing lemmas (Nat-membership hypotheses match the pin data form) -/

lemma stairUl_eq_zero (x₁ : Fin 23 → ℚ) (l i : ℕ)
    (h : l ∉ stairLsndN i) : stairUl x₁ l i = 0 :=
  List.sum_map_ite_eq_zero (LtermsStair i) (fun s => (s.2.2 : ℕ))
    (fun s => s.1 * x₁ s.2.1) l (by simpa [stairLsndN] using h)

lemma stairVl_eq_zero (y₁ : Fin 23 → ℚ) (l j : ℕ)
    (h : l ∉ stairRsndN j) : stairVl y₁ l j = 0 :=
  List.sum_map_ite_eq_zero (RtermsStair j) (fun s => (s.2.2 : ℕ))
    (fun s => s.1 * y₁ s.2.1) l (by simpa [stairRsndN] using h)

lemma stairUk_eq_zero (x₂ : Fin 23 → ℚ) (k i : ℕ)
    (h : k ∉ stairLfstN i) : stairUk x₂ k i = 0 :=
  List.sum_map_ite_eq_zero (LtermsStair i) (fun s => (s.2.1 : ℕ))
    (fun s => s.1 * x₂ s.2.2) k (by simpa [stairLfstN] using h)

lemma stairVk_eq_zero (y₂ : Fin 23 → ℚ) (k j : ℕ)
    (h : k ∉ stairRfstN j) : stairVk y₂ k j = 0 :=
  List.sum_map_ite_eq_zero (RtermsStair j) (fun s => (s.2.1 : ℕ))
    (fun s => s.1 * y₂ s.2.2) k (by simpa [stairRfstN] using h)

/-! ## P3 part-1 helpers (written pre-wipe, NOT yet run) -/

lemma List.sum_map_neg {α : Type*} (l : List α) (f : α → ℚ) :
    (l.map fun s => -f s).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih, neg_add]

lemma List.sum_map_const_zero (α : Type*) (l : List α) :
    (l.map fun _ : α => (0 : ℚ)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons _ ss ih => simp only [List.map_cons, List.sum_cons, ih, add_zero]

/-- (l.map f).sum = 0 when f vanishes on all of l (for the diagonal piece A). NOT yet run. -/
lemma List.sum_map_eq_zero {α : Type*} (l : List α) (f : α → ℚ)
    (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons,
      h s (by simp), ih (fun x hx => h x (by simp [hx])), zero_add]

lemma mul_ite_one (P : Prop) [Decidable P] (a b : ℚ) :
    a * (if P then (1 : ℚ) else 0) * b = if P then a * b else 0 := by
  split_ifs <;> ring

/-- Per-entry Kronecker expansion of the corner summand into its 4 δ-pieces.
(Written pre-wipe; NOT yet run.) -/
lemma summand_normal (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (s t : ℚ × Pr 23) :
    s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2 * t.1
    = (if s.2 = t.2 then s.1 * t.1 else 0)
      - (if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0)
      - (if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0)
      + (s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2) := by
  have hδ : (if s.2.1 = t.2.1 then (1 : ℚ) else 0) * (if s.2.2 = t.2.2 then (1 : ℚ) else 0)
      = if s.2 = t.2 then (1 : ℚ) else 0 := by
    by_cases h1 : s.2.1 = t.2.1
    · by_cases h2 : s.2.2 = t.2.2
      · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2)]; ring
      · have hne : s.2 ≠ t.2 := fun hh => h2 (congrArg Prod.snd hh)
        rw [if_pos h1, if_neg h2, if_neg hne]; ring
    · have hne : s.2 ≠ t.2 := fun hh => h1 (congrArg Prod.fst hh)
      rw [if_neg h1, if_neg hne]; ring
  simp only [stairPairM, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]
  have pA : s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0)
        * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
      = if s.2 = t.2 then s.1 * t.1 else 0 := by
    have hass : s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0)
        * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
      = s.1 * ((if s.2.1 = t.2.1 then (1 : ℚ) else 0)
        * (if s.2.2 = t.2.2 then (1 : ℚ) else 0)) * t.1 := by ring
    rw [hass, hδ]
    exact mul_ite_one _ _ _
  have pB : s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0) * (x₂ s.2.2 * y₂ t.2.2) * t.1
      = if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0 := by
    split_ifs <;> ring
  have pC : s.1 * (x₁ s.2.1 * y₁ t.2.1) * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
      = if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0 := by
    split_ifs <;> ring
  have pD : s.1 * (x₁ s.2.1 * y₁ t.2.1) * (x₂ s.2.2 * y₂ t.2.2) * t.1
      = (s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2) := by ring
  have e1 : s.1 * (((if s.2.1 = t.2.1 then (1 : ℚ) else 0) - x₁ s.2.1 * y₁ t.2.1)
        * ((if s.2.2 = t.2.2 then (1 : ℚ) else 0) - x₂ s.2.2 * y₂ t.2.2)) * t.1
      = s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0)
          * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
        - s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0) * (x₂ s.2.2 * y₂ t.2.2) * t.1
        - s.1 * (x₁ s.2.1 * y₁ t.2.1)
          * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
        + s.1 * (x₁ s.2.1 * y₁ t.2.1) * (x₂ s.2.2 * y₂ t.2.2) * t.1 := by ring
  rw [e1, pA, pB, pC, pD]

end StaircasePort.Stair

/-! ## P3 part 2: the corner identity (corner entry = Σ over the 47 terms) -/

lemma List.sum_map_congr {α : Type*} (l : List α) {f g : α → ℚ}
    (h : ∀ s ∈ l, f s = g s) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h s (by simp), ih (fun x hx => h x (by simp [hx]))]

#check @Pr
#check @RtermsStair
example (g : ℚ × Pr 23 → Fin 23) : True := trivial
end StaircasePort.Stair
