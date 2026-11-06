import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Data
import StaircasePort.Cert
import StaircasePort.Pivot
import StaircasePort.Signature
import StaircasePort.Projector

/-!
# N7 — the REWIRE: staircase-frame flag basis

The r6-frame route for `data_edge_stair`/`flagBasis_stair` was REFUTED (N2d: at the staircase
witness the r6-frame corner of `qM M` is singular, rank 44; 18 of the 39 corner positions are
not pivots). This file rebuilds the flag basis in the STAIRCASE frame:

* the staircase frame matrices `TeStair`/`TeStair'` (r6 `Te`/`Te'` analogues) and the
  conjugation identity `SbStair_conj` (r6 `Sb_conj` analogue);
* the generic edges restated at `qMStair`: `aux_edge_of_Stair` / `side_edge_of_Stair`
  (r6 bodies with `qM_corner` → `qMStair_corner`, `cor` → `corStairQ`);
* the staircase support computations (aux/side corner patterns over
  `LtermsStair`/`RtermsStair` — verified numerically first, `n7_auxside_probe.py`): the diag
  values are monomials `-stairAZL.getD β 0 · x β · y (β+1)` etc., so the aux/side clauses need
  the label facts `y l ≠ 0` for ALL `l` (r6 needed only `y 22`), obtained by widening the Pall
  `pA` factors to all `(β, l)` pairs via the `wP_l` witness (`pA_all_ne`);
* `data_edge_stair` restated: conclusion `DataE' (qMStair M)`, the `hpiv` slot replaced by
  `(hdet, hcorner)` — the middle clause is `isPiv_stairMid` (Projector.lean, PROVED) and the
  corner clause is the corner-hole contract `isPiv_stairCorner_contract` (being proved by a
  parallel agent; consumed here as the local `sorry` placeholder);
* `flag_gen_stair_aux` + `flagBasis_stair`: the N5-2 port with `S := SbStair U V` (one
  witness pair serves all three classes; the DataE clause cannot move alone — see
  SCAFFOLD.md "## N7 NOTES"). `flagBasis_stair`'s statement is BYTE-IDENTICAL.
-/

set_option maxRecDepth 20000

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker
open N52
open MvPolynomial

set_option maxHeartbeats 1000000

/-! ## R7-1 — the staircase flag frame -/

/-- The staircase frame rows: `PmStair` read in the staircase flag order (r6 `Te` analogue). -/
noncomputable def TeStair : Matrix (Fin (23 * 23)) (Pr 23) ℚ := PmStair.submatrix flagEquivStair id

/-- The staircase frame columns: `QmStair` read in the staircase flag order (r6 `Te'`). -/
noncomputable def TeStair' : Matrix (Pr 23) (Fin (23 * 23)) ℚ := QmStair.submatrix id flagEquivStair

lemma PmStair_mul_QmStair : PmStair * QmStair = 1 := by
  rw [PmStair, QmStair, Matrix.mul_assoc (Matrix.diagonal dv) TmStair,
    ← Matrix.mul_assoc TmStair TiStair (Matrix.diagonal fun u : Pr 23 => (dv u)⁻¹),
    TmStair_TiStair, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  ext u
  simp [dv_ne_zero]

lemma TeStair_TeStair' : TeStair * TeStair' = 1 := by
  rw [TeStair, TeStair', ← Matrix.submatrix_mul PmStair QmStair flagEquivStair id flagEquivStair
    Function.bijective_id, PmStair_mul_QmStair]
  ext i j; simp [Matrix.one_apply]

lemma TeStair'_TeStair : TeStair' * TeStair = 1 := by
  rw [TeStair', TeStair, ← Matrix.submatrix_mul QmStair PmStair id flagEquivStair id
    flagEquivStair.bijective, QmStair_mul_PmStair]
  ext i j; simp [Matrix.one_apply]

/-- The flag-basis form of the staircase projector (r6 `qM_eq` analogue). -/
lemma qMStair_eq (M : Matrix (Pr 23) (Pr 23) ℚ) : qMStair M = TeStair * M * TeStair' := by
  unfold qMStair TeStair TeStair'
  rw [Matrix.submatrix_mul _ _ flagEquivStair id flagEquivStair Function.bijective_id,
    Matrix.submatrix_mul _ _ flagEquivStair id id Function.bijective_id, submatrix_id_id]

/-- The staircase-frame basis change (r6 `Sb` analogue). -/
noncomputable def SbStair (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    Matrix (Fin ((19 + 4) * (19 + 4))) (Pr (19 + 4)) ℚ := TeStair * Kf U V

/-- The staircase-frame basis change, inverse side (r6 `Sbi` analogue). -/
noncomputable def SbiStair (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    Matrix (Pr (19 + 4)) (Fin ((19 + 4) * (19 + 4))) ℚ := Kfi U V * TeStair'

/-- The conjugation identity in the staircase frame (r6 `Sb_conj` analogue, same proof). -/
lemma SbStair_conj (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (A B : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    SbStair U V * (A ⊗ₖ B) * SbiStair U V =
      qMStair ((Uᵀ * A * U⁻¹ᵀ) ⊗ₖ (Vᵀ * B * V⁻¹ᵀ)) := by
  rw [qMStair_eq, mul_kronecker_mul, mul_kronecker_mul, SbStair, SbiStair, Kf, Kfi]
  simp only [Matrix.mul_assoc]

/-- The staircase-frame witness pair is a basis change (r6 `Sb_inv` analogue, same proof). -/
lemma SbStair_inv (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hU : U.det ≠ 0)
    (hV : V.det ≠ 0) : SbStair U V * SbiStair U V = 1 ∧ SbiStair U V * SbStair U V = 1 := by
  have k1 : Kf U V * Kfi U V = 1 := by
    rw [Kf, Kfi, ← mul_kronecker_mul, conj_one U hU, conj_one V hV, one_kronecker_one]
  have k2 : Kfi U V * Kf U V = 1 := by
    rw [Kf, Kfi, ← mul_kronecker_mul, conj_one' U hU, conj_one' V hV, one_kronecker_one]
  constructor
  · rw [SbStair, SbiStair, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Kf U V) (Kfi U V) TeStair', k1, Matrix.one_mul, TeStair_TeStair']
  · rw [SbStair, SbiStair, Matrix.mul_assoc,
      ← Matrix.mul_assoc TeStair' TeStair (Kf U V), TeStair'_TeStair, Matrix.one_mul, k2]

/-! ## R7-2 — the staircase aux-class support computations (over the staircase family) -/

section AuxStair

variable (x y : Fin (19 + 4) → ℚ)

/-- Staircase-frame analogue of `aux1_upper` (N52, r6-frame). The zero pattern is the same;
verified numerically (`n7_auxside_probe.py`). -/
lemma aux1_upper_Stair (β γ : ℕ) (hβγ : β < γ) (hγ : γ < 19 + 4) :
    corStairQ (1 ⊗ₖ (1 - vecMulVec x y)) β (19 + 3 + γ) = 0 := by
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]

/-- Staircase-frame analogue of `aux2_upper`. -/
lemma aux2_upper_Stair (β γ : ℕ) (hβγ : β < γ) (hγ : γ < 19 + 4) :
    corStairQ ((1 - vecMulVec x y) ⊗ₖ 1) β (19 + 3 + γ) = 0 := by
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]

/-- Staircase-frame analogue of `aux1_diag`: the diagonal value is the label monomial
`-a_β · x β · y (β+1)` (r6: `-x β · y 22`). Measured exact (`n7_auxside_probe.py`). -/
lemma aux1_diag_Stair (β : ℕ) (hβ : β < 19 + 3) :
    corStairQ (1 ⊗ₖ (1 - vecMulVec x y)) β (19 + 3 + β) =
      -((stairAZL.getD β 0 : ℤ) : ℚ) * x ⟨β, by omega⟩ * y ⟨β + 1, by omega⟩ := by
  have hfin : ((⟨19 + 3 + β - 21, by omega⟩ : Fin (19 + 4)) = ⟨β + 1, by omega⟩) := by
    simp only [Fin.mk.injEq]; omega
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

/-- Staircase-frame analogue of `aux1_diag_last`. -/
lemma aux1_diag_last_Stair :
    corStairQ (1 ⊗ₖ (1 - vecMulVec x y)) (19 + 3) (19 + 3 + (19 + 3)) =
      -(stairAlZ : ℚ) * x ⟨0, by omega⟩ * y ⟨19 + 3, by omega⟩ := by
  have hfin : ((⟨22, by omega⟩ : Fin (19 + 4)) = ⟨19 + 3, by omega⟩) := by simp
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

/-- Staircase-frame analogue of `aux2_diag`: `-b_β · x β · y (β+1)`. -/
lemma aux2_diag_Stair (β : ℕ) (hβ : β < 19 + 3) :
    corStairQ ((1 - vecMulVec x y) ⊗ₖ 1) β (19 + 3 + β) =
      -((stairBZL.getD β 0 : ℤ) : ℚ) * x ⟨β, by omega⟩ * y ⟨β + 1, by omega⟩ := by
  have hfin : ((⟨19 + 3 + β - 21, by omega⟩ : Fin (19 + 4)) = ⟨β + 1, by omega⟩) := by
    simp only [Fin.mk.injEq]; omega
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

/-- Staircase-frame analogue of `aux2_diag_last`. -/
lemma aux2_diag_last_Stair :
    corStairQ ((1 - vecMulVec x y) ⊗ₖ 1) (19 + 3) (19 + 3 + (19 + 3)) =
      -(stairBeZ : ℚ) * x ⟨0, by omega⟩ * y ⟨19 + 3, by omega⟩ := by
  have hfin : ((⟨22, by omega⟩ : Fin (19 + 4)) = ⟨19 + 3, by omega⟩) := by simp
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

end AuxStair

/-! ## R7-3 — the staircase aux-class edge (r6 `aux_edge_of` at `qMStair`) -/

/-- Staircase-frame analogue of `N52.aux_edge_of` (same body; `qM_corner` → `qMStair_corner`,
`cor` → `corStairQ`, `qM_idem`/`qM_trace` → `qMStair_*`). -/
theorem aux_edge_of_Stair (M : Matrix (Pr 23) (Pr 23) ℚ) (hM : M * M = M)
    (htr : M.trace = ((19 + 4) * (19 + 3) : ℕ))
    (hlow : ∀ β γ : ℕ, β < γ → γ < 19 + 4 → corStairQ M β (19 + 3 + γ) = 0)
    (hdiag : ∀ β : ℕ, β < 19 + 4 → corStairQ M β (19 + 3 + β) ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair M) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  have hk := two_k_le_23
  have hmm : (19 + 4) * (19 + 4) = (19 + 4) * (19 + 3) + (19 + 4) := by ring
  have hq := qMStair_idem hM
  have hrank : (qMStair M).rank = (19 + 4) * (19 + 4) - (19 + 4) := by
    have h1 := rank_eq_trace (qMStair M) hq
    rw [qMStair_trace, htr] at h1
    have := Nat.cast_injective h1
    omega
  set Cp : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ := (qMStair M).submatrix
    (fun l : Fin (19 + 4) => (⟨l.val, by omega⟩ : Fin ((19 + 4) * (19 + 4))))
    (fun r : Fin (19 + 4) => (⟨(19 + 4) * (19 + 4) - (19 + 4) + r.val, by omega⟩ :
      Fin ((19 + 4) * (19 + 4)))) with hCp
  have hCe : ∀ β γ : Fin (19 + 4), Cp β γ = corStairQ M β.val (19 + 3 + γ.val) := by
    intro β γ
    have e : (⟨(19 + 4) * (19 + 4) - (19 + 4) + γ.val, by omega⟩ : Fin ((19 + 4) * (19 + 4))) =
        ⟨23 * 23 - 45 + (19 + 3 + γ.val), by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hCp, submatrix_apply, e, ← qMStair_corner M β.val (19 + 3 + γ.val) (by omega) (by omega)]
  have hCl : ∀ β γ : Fin (19 + 4), β < γ → Cp β γ = 0 := fun β γ hβγ => by
    rw [hCe]; exact hlow _ _ hβγ γ.isLt
  have hCd : ∀ β : Fin (19 + 4), Cp β β ≠ 0 := fun β => by rw [hCe]; exact hdiag _ β.isLt
  have hdet : Cp.det ≠ 0 := by
    rw [det_of_isLowerTriangular Cp (fun a b hab => hCl a b hab)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hCd a
  have hmid := fun i (h1 : 19 + 4 ≤ i) (h2 : i < (19 + 4) * (19 + 4) - (19 + 4)) =>
    Platform.isPiv_mid (k := 19 + 4) (by omega) (qMStair M) hq hrank hdet h1 h2
  have hcorner : ∀ l : Fin (19 + 4), IsPiv (qMStair M) l.val ((19 + 4) * (19 + 4) - (19 + 4) + l.val) :=
    fun l => isPiv_block (qMStair M) Cp (by omega) (by omega) (fun i j => rfl)
      (isPiv_diag_of_lower Cp hCl hCd l)
  refine edge_exact (by omega) (qMStair M) hq _ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
    rcases hρ with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega
  · rw [DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil,
      List.nodup_append]
    refine ⟨DEPort.nodup_run _ _ _, DEPort.nodup_run _ _ _, ?_⟩
    intro a ha b hb hab
    rw [DEPort.mem_run] at ha hb
    obtain ⟨k, hk1, rfl⟩ := ha
    obtain ⟨k', hk2, rfl⟩ := hb
    simp only [Prod.mk.injEq] at hab
    omega
  · intro p hp
    rw [DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil,
      List.mem_append, DEPort.mem_run, DEPort.mem_run] at hp
    rcases hp with ⟨k, hk1, rfl⟩ | ⟨k, hk1, rfl⟩
    · simpa using hcorner ⟨k, hk1⟩
    · exact hmid _ (by simp only; omega) (by simp only; omega)
  · rw [hrank, DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil,
      List.length_append, DEPort.length_run, DEPort.length_run]

/-- Staircase-frame aux edge of the first kind (r6 `aux1_edge`; the label facts are the
strengthened all-coordinate nonvanishing the staircase diag values need). -/
lemma stairBeZ_ne : (stairBeZ : ℚ) ≠ 0 := by
  simp only [stairBeZ]; norm_num

lemma stairBZL_ne (r : ℕ) (hr : r < 22) : ((stairBZL.getD r 0 : ℤ) : ℚ) ≠ 0 := by
  interval_cases r <;> norm_num [stairBZL]

theorem aux1_edge_Stair (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : ∀ l : Fin (19 + 4), y l ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair (1 ⊗ₖ (1 - vecMulVec x y))) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  refine aux_edge_of_Stair _ ?_ ?_ (fun β γ h1 h2 => aux1_upper_Stair x y β γ h1 h2) ?_
  · rw [← mul_kronecker_mul, Matrix.one_mul, one_sub_vmv_idem x y hxy]
  · rw [trace_kronecker, trace_one, trace_one_sub_vmv x y hxy, Fintype.card_fin]; push_cast; ring
  · intro β hβ
    rcases Nat.lt_or_ge β (19 + 3) with h1 | h1
    · rw [aux1_diag_Stair x y β h1]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 (stairAZL_ne β (by omega))) (hx ⟨β, by omega⟩ h1))
        (hy ⟨β + 1, by omega⟩)
    · obtain rfl : β = 19 + 3 := by omega
      rw [aux1_diag_last_Stair]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 stairAlZ_ne) (hx ⟨0, by omega⟩ (by simp only; omega)))
        (hy ⟨19 + 3, by omega⟩)

/-- Staircase-frame aux edge of the second kind (r6 `aux2_edge`). -/
theorem aux2_edge_Stair (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : ∀ l : Fin (19 + 4), y l ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair ((1 - vecMulVec x y) ⊗ₖ 1)) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  refine aux_edge_of_Stair _ ?_ ?_ (fun β γ h1 h2 => aux2_upper_Stair x y β γ h1 h2) ?_
  · rw [← mul_kronecker_mul, Matrix.one_mul, one_sub_vmv_idem x y hxy]
  · rw [trace_kronecker, trace_one, trace_one_sub_vmv x y hxy, Fintype.card_fin]; push_cast; ring
  · intro β hβ
    rcases Nat.lt_or_ge β (19 + 3) with h1 | h1
    · rw [aux2_diag_Stair x y β h1]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 (stairBZL_ne β (by omega))) (hx ⟨β, by omega⟩ h1))
        (hy ⟨β + 1, by omega⟩)
    · obtain rfl : β = 19 + 3 := by omega
      rw [aux2_diag_last_Stair]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 stairBeZ_ne) (hx ⟨0, by omega⟩ (by simp only; omega)))
        (hy ⟨19 + 3, by omega⟩)

/-! ## R7-4 — the staircase side-class support computations -/

section SideStair

variable (x y : Fin (19 + 4) → ℚ)

/-- `TiStair_col` in the `QmStair_apply` order (column-entry times the inverse scale). -/
lemma TiStair_col' (j : ℕ) (hj : j < 45) (u : Pr 23) :
    TiStair u (bLsStair j) * (dv (bLsStair j))⁻¹ = sv (RtermsStair j) u := by
  rw [dv_bLs j hj, inv_inv, mul_comm, TiStair_col j hj]

/-- Staircase analogue of `side_B` (N52): `(TeStair * C) β a` reads the staircase family row. -/
lemma side_B_Stair (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ) (β : ℕ) (hβ : β < 2 * 19 + 7)
    (a : Fin (19 + 4)) :
    (TeStair * C) ⟨β, by have := two_k_le_23; omega⟩ a =
      ((LtermsStair β).map fun s => s.1 * C s.2 a).sum := by
  have hk := two_k_le_23
  simp only [TeStair, Matrix.mul_apply, Matrix.submatrix_apply, id, flagEquivStair_top β hβ,
    PmStair_apply, dv_aLs β hβ, TmStair_row β hβ, sum_sv_mul]

/-- Staircase analogue of `side_A` (N52): `(R * TeStair') a ⟨m-n+γ⟩` reads the staircase
family column. -/
lemma side_A_Stair (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ) (γ : ℕ) (hγ : γ < 19 + 4)
    (a : Fin (19 + 4)) :
    (R * TeStair') a ⟨(19 + 4) * (19 + 4) - (19 + 4) + γ, by have := two_k_le_23; omega⟩ =
      ((RtermsStair (19 + 3 + γ)).map fun t => R a t.2 * t.1).sum := by
  have hk := two_k_le_23
  have e : (⟨(19 + 4) * (19 + 4) - (19 + 4) + γ, by have := two_k_le_23; omega⟩ :
      Fin ((19 + 4) * (19 + 4))) =
      ⟨23 * 23 - 45 + (19 + 3 + γ), by have := two_k_le_23; omega⟩ := by
    refine Fin.ext (by simp only; omega)
  simp only [TeStair', Matrix.mul_apply, Matrix.submatrix_apply, id, e,
    flagEquivStair_bot _ (show 19 + 3 + γ < 2 * 19 + 7 by omega), QmStair_apply,
    TiStair_col' _ (show 19 + 3 + γ < 2 * 19 + 7 by omega), sum_mul_sv]

/-- Staircase analogue of `side1_B_upper` (N52). -/
lemma side1_B_upper_Stair (β : ℕ) (a : Fin (19 + 4)) (hβa : β < a.val) :
    ((LtermsStair β).map fun s => s.1 * Cx x s.2 a).sum = 0 := by
  have ha := a.isLt
  simp (disch := omega) only [LtermsStair, LtermsZStair, Cx, of_apply, dif_pos, dif_neg, if_pos,
    if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_zero,
    add_zero]

/-- Staircase analogue of `side1_B_diag` (N52): diag value `x β` resp. `stairAlZ · x 0`. -/
lemma side1_B_diag_Stair (β : Fin (19 + 4)) :
    ((LtermsStair β.val).map fun s => s.1 * Cx x s.2 β).sum =
      if β.val < 19 + 3 then x β else stairAlZ * x ⟨0, by omega⟩ := by
  have hb := β.isLt
  rcases Nat.lt_or_ge β.val (19 + 3) with h1 | h1
  · simp (disch := omega) only [LtermsStair, LtermsZStair, Cx, of_apply, dif_pos, if_pos, if_true,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero,
      Fin.eta, mul_one, Int.cast_one]
  · obtain ⟨b, hb'⟩ := β
    obtain rfl : b = 19 + 3 := by simp only at h1; omega
    simp (disch := omega) only [LtermsStair, LtermsZStair, Cx, of_apply, dif_pos, dif_neg, if_pos,
      if_neg, if_true, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_mul, add_zero, lt_irrefl, not_false_eq_true, ite_true, ite_false, mul_zero, ↓reduceIte,
      ↓reduceDIte, Int.cast_one, zero_add]

/-- Staircase analogue of `side1_A_upper` (N52). -/
lemma side1_A_upper_Stair (γ : ℕ) (hγ : γ < 19 + 4) (a : Fin (19 + 4)) (haγ : a.val < γ) :
    ((RtermsStair (19 + 3 + γ)).map fun t => Ry y a t.2 * t.1).sum = 0 := by
  have ha := a.isLt
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [RtermsStair, RtermsZStair, Ry, of_apply, dif_pos, dif_neg, if_pos,
      if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
      add_zero, Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [RtermsStair, RtermsZStair, Ry, of_apply, dif_pos, dif_neg, if_pos,
      if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
      add_zero, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte]

/-- Staircase analogue of `side1_A_diag` (N52), the `γ < 22` diagonal: `a_γ · y (γ+1)`. -/
lemma side1_A_diag_Stair (γ : ℕ) (hγ : γ < 19 + 3) :
    ((RtermsStair (19 + 3 + γ)).map fun t =>
      Ry y (⟨γ, by omega⟩ : Fin (19 + 4)) t.2 * t.1).sum =
      ((stairAZL.getD γ 0 : ℤ) : ℚ) * y ⟨γ + 1, by omega⟩ := by
  have hfin : ((⟨19 + 3 + γ - 21, by omega⟩ : Fin (19 + 4)) = ⟨γ + 1, by omega⟩) := by
    simp only [Fin.mk.injEq]; omega
  simp (disch := omega) only [RtermsStair, RtermsZStair, Ry, of_apply, dif_pos, dif_neg, if_pos,
    if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
    add_zero, Nat.add_sub_cancel_left, mul_one, zero_add, ite_true, ↓reduceIte]
  rw [hfin]; ring

/-- Staircase analogue of `side1_A_diag` (N52), the last diagonal: `y 22`. -/
lemma side1_A_diag_last_Stair :
    ((RtermsStair (19 + 3 + (19 + 3))).map fun t =>
      Ry y (⟨19 + 3, by omega⟩ : Fin (19 + 4)) t.2 * t.1).sum =
      y ⟨19 + 3, by omega⟩ := by
  simp (disch := omega) only [RtermsStair, RtermsZStair, Ry, of_apply, dif_pos, dif_neg, if_pos,
    if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
    add_zero, mul_one, ↓reduceIte, ↓reduceDIte, lt_irrefl, not_false_eq_true, Int.cast_one,
    one_mul]

/-- Staircase analogue of `side2_B_upper` (N52). -/
lemma side2_B_upper_Stair (β : ℕ) (a : Fin (19 + 4)) (hβa : β < a.val) :
    ((LtermsStair β).map fun s => s.1 * Cx2 x s.2 a).sum = 0 := by
  have ha := a.isLt
  simp (disch := omega) only [LtermsStair, LtermsZStair, Cx2, of_apply, dif_pos, dif_neg, if_pos,
    if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_zero,
    add_zero]

/-- Staircase analogue of `side2_B_diag` (N52): diag `x β` resp. `stairBeZ · x 0`. -/
lemma side2_B_diag_Stair (β : Fin (19 + 4)) :
    ((LtermsStair β.val).map fun s => s.1 * Cx2 x s.2 β).sum =
      if β.val < 19 + 3 then x β else stairBeZ * x ⟨0, by omega⟩ := by
  have hb := β.isLt
  rcases Nat.lt_or_ge β.val (19 + 3) with h1 | h1
  · simp (disch := omega) only [LtermsStair, LtermsZStair, Cx2, of_apply, dif_pos, if_pos, if_true,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero,
      Fin.eta, mul_one, Int.cast_one]
  · obtain ⟨b, hb'⟩ := β
    obtain rfl : b = 19 + 3 := by simp only at h1; omega
    simp (disch := omega) only [LtermsStair, LtermsZStair, Cx2, of_apply, dif_pos, dif_neg, if_pos,
      if_neg, if_true, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_mul, add_zero, lt_irrefl, not_false_eq_true, ite_true, ite_false, mul_zero, ↓reduceIte,
      ↓reduceDIte, Int.cast_one, zero_add]

/-- Staircase analogue of `side2_A_upper` (N52). -/
lemma side2_A_upper_Stair (γ : ℕ) (hγ : γ < 19 + 4) (a : Fin (19 + 4)) (haγ : a.val < γ) :
    ((RtermsStair (19 + 3 + γ)).map fun t => Ry2 y a t.2 * t.1).sum = 0 := by
  have ha := a.isLt
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [RtermsStair, RtermsZStair, Ry2, of_apply, dif_pos, dif_neg, if_pos,
      if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
      add_zero, Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [RtermsStair, RtermsZStair, Ry2, of_apply, dif_pos, dif_neg, if_pos,
      if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
      add_zero, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte]

/-- Staircase analogue of `side2_A_diag` (N52), the `γ < 22` diagonal: `b_γ · y (γ+1)`. -/
lemma side2_A_diag_Stair (γ : ℕ) (hγ : γ < 19 + 3) :
    ((RtermsStair (19 + 3 + γ)).map fun t =>
      Ry2 y (⟨γ, by omega⟩ : Fin (19 + 4)) t.2 * t.1).sum =
      ((stairBZL.getD γ 0 : ℤ) : ℚ) * y ⟨γ + 1, by omega⟩ := by
  have hfin : ((⟨19 + 3 + γ - 21, by omega⟩ : Fin (19 + 4)) = ⟨γ + 1, by omega⟩) := by
    simp only [Fin.mk.injEq]; omega
  simp (disch := omega) only [RtermsStair, RtermsZStair, Ry2, of_apply, dif_pos, dif_neg, if_pos,
    if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
    add_zero, Nat.add_sub_cancel_left, mul_one, zero_add, ite_true, ↓reduceIte]
  rw [hfin]; ring

/-- Staircase analogue of `side2_A_diag` (N52), the last diagonal: `y 22`. -/
lemma side2_A_diag_last_Stair :
    ((RtermsStair (19 + 3 + (19 + 3))).map fun t =>
      Ry2 y (⟨19 + 3, by omega⟩ : Fin (19 + 4)) t.2 * t.1).sum =
      y ⟨19 + 3, by omega⟩ := by
  simp (disch := omega) only [RtermsStair, RtermsZStair, Ry2, of_apply, dif_pos, dif_neg, if_pos,
    if_neg, Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul,
    add_zero, mul_one, ↓reduceIte, ↓reduceDIte, lt_irrefl, not_false_eq_true, Int.cast_one,
    one_mul]

/-- Staircase analogue of `rank_kron_vmv` (N52). -/
lemma rank_kron_vmv_Stair (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hAA : A * A = A)
    (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1) (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ)
    (hMM : M * M = M) (htr : M.trace = A.trace) : (qMStair M).rank = A.rank := by
  have h1 := rank_eq_trace (qMStair M) (qMStair_idem hMM)
  rw [qMStair_trace, htr, ← rank_eq_trace A hAA] at h1
  exact Nat.cast_injective h1

end SideStair

/-! ## R7-5 — the staircase side-class edge (r6 `side_edge_of` at `qMStair`) -/

/-- The staircase-frame qMStair factorization (r6 `qM_fac` analogue). -/
lemma qMStair_fac (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ) (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ) :
    qMStair (C * A * R) = (TeStair * C) * A * (R * TeStair') := by
  rw [qMStair_eq]; simp only [Matrix.mul_assoc]

/-- Staircase-frame analogue of `N52.side_edge_of` (same body; `Te`/`Te'` → `TeStair`/`TeStair'`,
`qM` → `qMStair`). The corner facts `hB/hBd/hA/hAd` are the STAIRCASE-family block conditions. -/
theorem side_edge_of_Stair (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ)
    (hB : ∀ i j : Fin (19 + 4), i < j →
      (TeStair * C) ⟨i.val, by have := two_k_le_23; omega⟩ j = 0)
    (hBd : ∀ i : Fin (19 + 4),
      (TeStair * C) ⟨i.val, by have := two_k_le_23; omega⟩ i ≠ 0)
    (hA : ∀ i j : Fin (19 + 4), i < j → (R * TeStair') i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + j.val, by have := two_k_le_23; omega⟩ = 0)
    (hAd : ∀ i : Fin (19 + 4), (R * TeStair') i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + i.val, by have := two_k_le_23; omega⟩ ≠ 0)
    (hM : C * A * R * (C * A * R) = C * A * R) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hrM : (qMStair (C * A * R)).rank = r)
    (hcor : 19 + 4 < 2 * r →
      (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ :
          Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair (C * A * R)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  have hk := two_k_le_23
  have hq : qMStair (C * A * R) * qMStair (C * A * R) = qMStair (C * A * R) := qMStair_idem hM
  have hrn : r ≤ 19 + 4 := hr ▸ rank_le_width A |>.trans (by simp)
  obtain ⟨e, he, rs', h1, h2, h3⟩ : ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair (C * A * R)) ∧
      ∃ rs', e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length =
        (qMStair (C * A * R)).rank := by
    refine DEPort.edge_singles (by nlinarith) _ hq _ ?_ ?_ ?_
    · intro ρ hρ
      unfold sideRuns at hρ
      split_ifs at hρ with hr2
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
        subst hρ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega
      · simp at hρ
    · unfold sideRuns
      split_ifs
      · rw [DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil]
        exact DEPort.nodup_run _ _ _
      · exact List.nodup_nil
    · intro p hp
      unfold sideRuns at hp
      split_ifs at hp with hr2
      · rw [DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil, DEPort.mem_run] at hp
        obtain ⟨t, ht, rfl⟩ := hp
        have hpiv : IsPiv A (19 + 4 - r + t) (19 + 4 - r + t) :=
          Platform.isPiv_mid (m := 19 + 4) (k := 19 + 4 - r) (by omega) A hAA (by omega) (hcor hr2)
            (by omega) (by omega)
        have his := Platform.isPiv_side (by nlinarith) (TeStair * C) A (R * TeStair') hB hBd hA hAd
          hpiv
        rw [qMStair_fac]
        have key : (19 + 4) * (19 + 4) - r + t =
            (19 + 4) * (19 + 4) - (19 + 4) + (19 + 4 - r + t) := by
          generalize (19 + 4) * (19 + 4) = M2 at hk ⊢; omega
        rw [key]; exact his
      · rw [DEPort.runPairs_nil] at hp; simp at hp
  exact ⟨e, he, rs', h1, h2, h3.trans hrM⟩

/-- Staircase-frame side edge of the first kind (r6 `side1_edge`; strengthened label facts). -/
theorem side1_edge_Stair (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : ∀ l : Fin (19 + 4), y l ≠ 0)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hcor : 19 + 4 < 2 * r → (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ : Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair (A ⊗ₖ vecMulVec x y)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  have hMM : A ⊗ₖ vecMulVec x y * (A ⊗ₖ vecMulVec x y) = A ⊗ₖ vecMulVec x y := by
    rw [← mul_kronecker_mul, hAA, vmv_idem x y hxy]
  have htr : (A ⊗ₖ vecMulVec x y).trace = A.trace := by
    rw [trace_kronecker, trace_vecMulVec, dotProduct_comm, hxy, mul_one]
  have hrM := rank_kron_vmv_Stair A hAA x y hxy _ hMM htr
  rw [kron_vec1] at hMM hrM ⊢
  refine side_edge_of_Stair _ A _ ?_ ?_ ?_ ?_ hMM hAA r hr (hrM.trans hr) hcor
  · intro i j hij
    rw [side_B_Stair _ _ (by omega)]
    exact side1_B_upper_Stair x i.val j hij
  · intro i
    rw [side_B_Stair _ _ (by omega), side1_B_diag_Stair]
    split_ifs with h1
    · exact hx i h1
    · exact mul_ne_zero stairAlZ_ne (hx ⟨0, by omega⟩ (by simp only; omega))
  · intro i j hij
    rw [side_A_Stair _ _ j.isLt]
    exact side1_A_upper_Stair y j.val j.isLt i hij
  · intro i
    rw [side_A_Stair _ _ i.isLt]
    rcases Nat.lt_or_ge i.val (19 + 3) with h1 | h1
    · rw [side1_A_diag_Stair y i.val h1]
      exact mul_ne_zero (stairAZL_ne i.val h1) (hy ⟨i.val + 1, by have := i.isLt; omega⟩)
    · have hi : i.val = 19 + 3 := by have := i.isLt; omega
      obtain ⟨b, hb'⟩ := i
      obtain rfl : b = 19 + 3 := hi
      rw [side1_A_diag_last_Stair]
      exact hy ⟨19 + 3, by omega⟩

/-- Staircase-frame side edge of the second kind (r6 `side2_edge`; strengthened label facts). -/
theorem side2_edge_Stair (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : ∀ l : Fin (19 + 4), y l ≠ 0)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hcor : 19 + 4 < 2 * r → (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ : Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair (vecMulVec x y ⊗ₖ A)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  have hMM : vecMulVec x y ⊗ₖ A * (vecMulVec x y ⊗ₖ A) = vecMulVec x y ⊗ₖ A := by
    rw [← mul_kronecker_mul, hAA, vmv_idem x y hxy]
  have htr : (vecMulVec x y ⊗ₖ A).trace = A.trace := by
    rw [trace_kronecker, trace_vecMulVec, dotProduct_comm, hxy, one_mul]
  have hrM := rank_kron_vmv_Stair A hAA x y hxy _ hMM htr
  rw [kron_vec2] at hMM hrM ⊢
  refine side_edge_of_Stair _ A _ ?_ ?_ ?_ ?_ hMM hAA r hr (hrM.trans hr) hcor
  · intro i j hij
    rw [side_B_Stair _ _ (by omega)]
    exact side2_B_upper_Stair x i.val j hij
  · intro i
    rw [side_B_Stair _ _ (by omega), side2_B_diag_Stair]
    split_ifs with h1
    · exact hx i h1
    · exact mul_ne_zero stairBeZ_ne (hx ⟨0, by omega⟩ (by simp only; omega))
  · intro i j hij
    rw [side_A_Stair _ _ j.isLt]
    exact side2_A_upper_Stair y j.val j.isLt i hij
  · intro i
    rw [side_A_Stair _ _ i.isLt]
    rcases Nat.lt_or_ge i.val (19 + 3) with h1 | h1
    · rw [side2_A_diag_Stair y i.val h1]
      exact mul_ne_zero (stairBZL_ne i.val h1) (hy ⟨i.val + 1, by have := i.isLt; omega⟩)
    · have hi : i.val = 19 + 3 := by have := i.isLt; omega
      obtain ⟨b, hb'⟩ := i
      obtain rfl : b = 19 + 3 := hi
      rw [side2_A_diag_last_Stair]
      exact hy ⟨19 + 3, by omega⟩


/-! ## R7-6 — the label facts at all coordinates (the staircase aux/side diag values need
`y l ≠ 0` for every `l`, not just `l = 22` — see SCAFFOLD.md "## N7 NOTES") -/

/-- The model rank-one label with the nonzero entry at column `l` (r6 `wP` generalised). -/
def wPl (n : ℕ) (hn : 0 < n) (l : Fin n) : Matrix (Fin n) (Fin n) ℚ :=
  vecMulVec (fun _ => 1) (Pi.single l 1)

lemma wPl_dot (hn : 0 < n) (l : Fin n) :
    (Pi.single l (1 : ℚ)) ⬝ᵥ (fun _ => 1) = 1 := by
  simp [dotProduct, Pi.single_apply]

lemma wPl_idem (hn : 0 < n) (l : Fin n) : wPl n hn l * wPl n hn l = wPl n hn l :=
  vmv_idem _ _ (wPl_dot hn l)

lemma wPl_trace (hn : 0 < n) (l : Fin n) : (wPl n hn l).trace = 1 := by
  simp only [wPl, trace_vecMulVec, dotProduct_comm, wPl_dot hn l]

lemma wPl_apply (hn : 0 < n) (l β : Fin n) : wPl n hn l β l = 1 := by
  simp [wPl, vecMulVec_apply, Pi.single_apply]

/-- **NEW (N7)** — `pA_U_ne` (N52) at EVERY coordinate pair: the polynomial `pA XU P β l` is
nonzero for all `(β, l)`. Same proof as `pA_U_ne`, conjugating to `wPl n hn l` (whose `(β, l)`
entry is 1 for every `β`) instead of `wP`. -/
lemma pA_all_ne (hn : 0 < n) (P : Matrix (Fin n) (Fin n) ℚ) (hP : P * P = P) (htr : P.trace = 1)
    (β l : Fin n) : pA XU P β l ≠ 0 := by
  obtain ⟨U, hU, hc⟩ := conj_wit P (wPl n hn l) hP (wPl_idem hn l) (htr.trans (wPl_trace hn l).symm)
  intro h0
  have := congrArg (eval (ptUV U 1)) h0
  rw [eval_pA_U, Uf_pt, hc, map_zero, Matrix.smul_apply, wPl_apply hn l, smul_eq_mul, mul_one] at this
  exact hU this

/-- **NEW (N7)** — the XV analogue. -/
lemma pA_all_ne_V (hn : 0 < n) (P : Matrix (Fin n) (Fin n) ℚ) (hP : P * P = P) (htr : P.trace = 1)
    (β l : Fin n) : pA XV P β l ≠ 0 := by
  obtain ⟨U, hU, hc⟩ := conj_wit P (wPl n hn l) hP (wPl_idem hn l) (htr.trans (wPl_trace hn l).symm)
  intro h0
  have := congrArg (eval (ptUV 1 U)) h0
  rw [eval_pA_V, Vf_pt, hc, map_zero, Matrix.smul_apply, wPl_apply hn l, smul_eq_mul, mul_one] at this
  exact hU this

end StaircasePort.Stair
