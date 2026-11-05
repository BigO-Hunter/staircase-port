/-
N5-2 scratch: staircase-frame corner polynomial `pDatStair` (the Pall-product corner factor).

Why: flag_gen's corner factor `pDat` (Defs4:1497) lives in the r6/Defs4 `cor` frame; at the
staircase witness that frame's 45x45 corner is SINGULAR (det = 0, rank 44; verified exactly by
scratch_corner_check2.py: det = 0 mod 2^31-1, 67108859, 1000003, 998244353), while N3's
`stair_data_cert` (StaircasePort/Cert.lean:213) certifies the STAIRCASE frame (`corStairQ`)
corner invertible at the same witness. So the corner factor must be rebuilt in that frame.
-/
import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Cert
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace StaircasePort.Stair

open Matrix Finset MvPolynomial IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

lemma eval_list_sum (f : Vr 23 → ℚ) : ∀ l : List (Rp 23),
    MvPolynomial.eval f l.sum = (l.map (MvPolynomial.eval f)).sum
  | [] => by simp
  | a :: t => by simp [eval_list_sum f t]

/-- Staircase-frame corner functional (generic coefficient ring) — the coefficient-ring
generalization of `corStairQ` (Cert.lean:96) / `cor` (Defs4:942). -/
def corStairR {R : Type*} [CommRing R] [Algebra ℚ R]
    (M : Matrix (Pr 23) (Pr 23) R) (i j : ℕ) : R :=
  ((RtermsStair j).map fun t =>
    ((LtermsStair i).map fun s => (algebraMap ℚ R s.1) * M s.2 t.2).sum *
      (algebraMap ℚ R t.1)).sum

/-- At `R = ℚ` this is `corStairQ` verbatim. -/
lemma corStairR_rat (M : Matrix (Pr 23) (Pr 23) ℚ) (i j : ℕ) :
    corStairR M i j = corStairQ M i j := by
  simp [corStairR, corStairQ]

/-- Scalar pull-out for the inner row sum. -/
lemma corStairR_inner_smul {R : Type*} [CommRing R] [Algebra ℚ R] (c : R)
    (l : List (ℚ × Pr 23)) (N : Pr 23 → R) :
    (l.map fun s => (algebraMap ℚ R s.1) * (c * N s.2)).sum =
      c * (l.map fun s => (algebraMap ℚ R s.1) * N s.2).sum := by
  rw [show (l.map fun s => (algebraMap ℚ R s.1) * (c * N s.2)) =
      (l.map fun s => c * ((algebraMap ℚ R s.1) * N s.2)) from
    List.map_congr_left fun s _ => by ring]
  exact List.sum_map_mul_left l (fun s => (algebraMap ℚ R s.1) * N s.2) c

lemma corStairR_smul {R : Type*} [CommRing R] [Algebra ℚ R] (c : R)
    (M : Matrix (Pr 23) (Pr 23) R) (i j : ℕ) :
    corStairR (c • M) i j = c * corStairR M i j := by
  unfold corStairR
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [show ((RtermsStair j).map fun t =>
        ((LtermsStair i).map fun s => (algebraMap ℚ R s.1) * (c * M s.2 t.2)).sum *
          (algebraMap ℚ R t.1)) =
      ((RtermsStair j).map fun t =>
        c * ((algebraMap ℚ R t.1) *
          ((LtermsStair i).map fun s => (algebraMap ℚ R s.1) * M s.2 t.2).sum)) from by
    apply List.map_congr_left
    intro t _
    rw [corStairR_inner_smul c (LtermsStair i) (fun u => M u t.2)]
    ring]
  rw [List.sum_map_mul_left]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

/-- `eval` commutes with the staircase corner functional. -/
lemma eval_corStairR (f : Vr 23 → ℚ) (M : Matrix (Pr 23) (Pr 23) (Rp 23)) (i j : ℕ) :
    MvPolynomial.eval f (corStairR M i j) =
      corStairR (M.map (MvPolynomial.eval f)) i j := by
  unfold corStairR
  rw [eval_list_sum, List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  rw [MvPolynomial.eval_mul, eval_list_sum, List.map_map]
  simp only [Function.comp_def]
  have h1 : (MvPolynomial.eval f) ((algebraMap ℚ (Rp 23)) t.1) = t.1 := by
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.eval_C]
  have h2 : (algebraMap ℚ ℚ) t.1 = t.1 := by simp
  rw [h1, h2]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [Matrix.map_apply, MvPolynomial.eval_mul]
  have h3 : (MvPolynomial.eval f) ((algebraMap ℚ (Rp 23)) s.1) = s.1 := by
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.eval_C]
  have h4 : (algebraMap ℚ ℚ) s.1 = s.1 := by simp
  rw [h3, h4]

end StaircasePort.Stair
