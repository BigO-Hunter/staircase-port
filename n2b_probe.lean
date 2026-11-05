/- N2b probe: the 47-term decomposition machinery. Developed here, moved to Pivot.lean green. -/
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

/-! ## P1: generic List.sum helpers -/

lemma List.sum_map_add {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map fun s => f s + g s).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih, add_assoc]

lemma List.sum_map_mul_right {α : Type*} (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map fun s => f s * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih, add_mul]

lemma List.sum_map_mul_left {α : Type*} (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map fun s => c * f s).sum = c * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

lemma List.sum_map_ite_eq_zero {α : Type*} (l : List (ℚ × Pr 23))
    (c : ℚ × Pr 23 → ℕ) (f : ℚ × Pr 23 → ℚ) (n : ℕ)
    (h : n ∉ l.map c) :
    (l.map fun s => if c s = n then f s else 0).sum = 0 := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons] at h ⊢
    rw [if_neg h.1, ih h.2, add_zero]

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
    have head : (lL.map fun s => if k₁ s = k₂ t then f s * g t else 0).sum
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      induction lL with
      | nil => rfl
      | cons s ss ih2 =>
        simp only [List.map_cons, List.sum_cons]
        rw [← ih2]
        split_ifs with hc
        · ring
        · ring
    rw [head, add_comm, ih, ← add_mul]
    congr 1
    have distrib : ∀ c : γ,
        (lL.map fun s => if k₁ s = c then f s else 0).sum *
          ((if k₂ t = c then g t else 0) + (ts.map fun t' => if k₂ t' = c then g t' else 0).sum)
        = (lL.map fun s => if k₁ s = c then f s else 0).sum * (if k₂ t = c then g t else 0)
          + (lL.map fun s => if k₁ s = c then f s else 0).sum *
            (ts.map fun t' => if k₂ t' = c then g t' else 0).sum := fun c => mul_add _ _ _
    calc ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
            ((if k₂ t = c then g t else 0) + (ts.map fun t' => if k₂ t' = c then g t' else 0).sum)
        = ∑ c : γ, ((lL.map fun s => if k₁ s = c then f s else 0).sum * (if k₂ t = c then g t else 0)
            + (lL.map fun s => if k₁ s = c then f s else 0).sum *
              (ts.map fun t' => if k₂ t' = c then g t' else 0).sum) := by
          simp only [distrib]
      _ = (∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum * (if k₂ t = c then g t else 0))
          + ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
              (ts.map fun t' => if k₂ t' = c then g t' else 0).sum := Finset.sum_add_distrib
    -- first piece collapses to A(k₂ t) * g t
    -- (finished below)
    sorry

end StaircasePort.Stair
