/- N2b probe P1: generic List.sum helpers. -/
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

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

/-- Product-of-sums: Σ_t Σ_s f s · g t = (Σ_s f s)·(Σ_t g t). -/
lemma List.sum_sum_mul {α β : Type*} (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) :
    (lR.map fun t => (lL.map fun s => f s * g t).sum).sum = (lL.map f).sum * (lR.map g).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_mul_right, ih, mul_add]

end StaircasePort.Stair
