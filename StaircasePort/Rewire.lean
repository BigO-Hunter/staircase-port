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
  corner clause is the composed contract `isPiv_stairCorner_contract` (COMPOSE: the proved
  `isPiv_stairCorner`, zero sorry; its five hypotheses are derived at the call site from the
  label facts and the Pall product's `pDevStair`/`pMStairL` factors);
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

/-! ## R7-7 — the corner-hole contract (coordination placeholder) and the restated data edge -/

/-- **THE CORNER CONTRACT (COMPOSED)** — now the PROVED clause: `isPiv_stairCorner`
(Projector.lean, zero sorry) re-exported at the consumer's run list via the one-line
`runPairs (stairCornerRuns 23 529) = runPairs [(1, 507, 21), (25, 486, 18)]` bridge. The
five hypotheses mirror the proved binders verbatim (they are the proved clause's honest
set; `h₁/h₂/hdet` are NOT needed by the corner clause — they are the middle-run's fuel,
`isPiv_stairMid`). The rewire consumer derives `hu/hv` from the label facts (`labU`/`labV`)
and `hT/hM1/hM2` from the Pall product's new `pDevStair`/`pMStairL` factors (the COMPOSE
section below). This closes the ONLY sorry of the hypothesis-graph spine. -/
theorem isPiv_stairCorner_contract (x1 y1 x2 y2 : Fin 23 → ℚ)
    (hu : x1 ⟨0, by omega⟩ * x2 ⟨0, by omega⟩ ≠ 0)
    (hv : y1 ⟨22, by omega⟩ * y2 ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x2 (n7Fin l) * y2 (n7Fin (l + 1))
        + stairRunB l * x1 (n7Fin l) * y1 (n7Fin (l + 1)) ≠ 0)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x1 y1 x2 y2)) 25 20)
    (hM2 : ∀ t : ℕ, t < 18 →
      26 ≤ rk (stairCornerQOf (stairPairM x1 y1 x2 y2)) (26 + t) (2 + t)) :
    ∀ p ∈ runPairs (stairCornerRuns 23 529),
      IsPiv (qMStair (stairPairM x1 y1 x2 y2)) p.1 p.2 := by
  have hrun : runPairs (stairCornerRuns 23 529)
      = runPairs [(1, 507, 21), (25, 486, 18)] := by
    simp [stairCornerRuns, runPairs]
  rw [hrun]
  exact isPiv_stairCorner x1 y1 x2 y2 hu hv hT hM1 hM2

/-! ## COMPOSE — the Pall fuel for the corner hypotheses (`hT`/`hM1`/`hM2` at arbitrary labels)

The rewire's data clause must supply the corner clause's five hypotheses for the CONJUGATED
labels of every `Lab ×ˢ Lab` pair. `hu`/`hv` come from the label facts (`labU`/`labV`).
`hT`/`hM1`/`hM2` come from new Pall factors, each a nonzero polynomial by the
`conj_wit`/`ptUV` witness trick (the `pDatStair_ne` pattern with the WITNESS matrices as
`W₁`/`W₂` — `conj_wit` conjugates ANY idempotent trace-1 pair onto them):
* `pDevStair l` — the run-1 diagonal deviation; `eval f` = `(detU*detV) * hT-term`;
  witness `n7_hT_witness` (CornerData);
* `pMStairL k rl cl` — the det of the `(rl, cl)` minor of the staircase corner;
  `eval f` = `(detU*detV)^k * minor-det`; witness = the N2c certificates via `n7_cert_det`
  (the det form of `n2c_rank_lower`'s core).
The old r6-shape `pT` factors are DROPPED from Pall (their consumer `isPiv_stair_lower`
was refuted; the staircase `hT` is carried by `pDevStair`). -/

/-- **COMPOSE** — the N2c certificate as a witness minor determinant (the det form of
`n2c_rank_lower`'s core; the proof is its `hdetQ` block verbatim). -/
theorem n7_cert_det {n_ X Y : ℕ} (hX : X ≤ 45) (rl cl : List ℕ)
    (hrl : ∀ i : Fin n_, rl.getD i.val 0 < X)
    (hcl : ∀ i : Fin n_, Y ≤ cl.getD i.val 0)
    (hclB : ∀ i : Fin n_, cl.getD i.val 0 < 45)
    (rows cols : List (List ℕ))
    (hchk : certChk rows cols n_ stairCertP = true)
    (hent : ((List.range n_).all fun i => (List.range n_).all fun j =>
      decide (corZStair stairMZ (rl.getD i 0) (cl.getD j 0) % (stairCertP : ℤ) =
        (((rows.getD i []).getD j 0 : ℕ) : ℤ))) = true) :
    (Matrix.of fun i j : Fin n_ =>
      stairCornerQ (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
        (⟨cl.getD j.val 0, hclB j⟩ : Fin 45)).det ≠ 0 := by
  set Dz : Matrix (Fin n_) (Fin n_) ℤ :=
    Matrix.of fun i j => corZStair stairMZ (rl.getD i.val 0) (cl.getD j.val 0) with hDz
  have hentQ : (Matrix.of fun i j : Fin n_ =>
        stairCornerQ (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
          (⟨cl.getD j.val 0, hclB j⟩ : Fin 45)) =
      Dz.map (Int.cast : ℤ → ℚ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, hDz, stairCornerQ, stairCornerQOf,
      ← stairMZ_map, corStairQ_cast]
  have hdetQ : (Dz.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    have e1 : (Dz.map (Int.cast : ℤ → ℚ)).det = ((Dz.det : ℤ) : ℚ) := by
      have h := RingHom.map_det (Int.castRingHom ℚ) Dz
      rw [RingHom.mapMatrix_apply] at h
      exact h.symm
    rw [e1, Int.cast_ne_zero]
    intro h0
    have e2 := RingHom.map_det (Int.castRingHom (ZMod stairCertP)) Dz
    rw [RingHom.mapMatrix_apply, h0, map_zero] at e2
    have e3 : Dz.map (Int.castRingHom (ZMod stairCertP)) =
        Matrix.of fun i l : Fin n_ =>
          (((rows.getD i.val []).getD l.val 0 : ℕ) : ZMod stairCertP) := by
      ext i l
      rw [Matrix.map_apply, hDz, Matrix.of_apply, Matrix.of_apply, eq_intCast,
        ← ZMod.intCast_mod]
      have hc := hent
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
      rw [hc i.val i.isLt l.val l.isLt, Int.cast_natCast]
    rw [e3] at e2
    exact det_ne_zero_of_certChk rows cols hchk e2.symm
  rw [hentQ]
  exact hdetQ

/-- **COMPOSE** — the witness minor det at given row/col lists, in the
`corStairQ`-of-the-witness-kronecker form (consumed as `pMStairL_ne`'s `hc`). -/
theorem n7_witdet_gen (k X Y : ℕ) (hX : X ≤ 45) (rl cl : List ℕ)
    (hrl : ∀ i : Fin k, rl.getD i.val 0 < X)
    (hcl : ∀ i : Fin k, Y ≤ cl.getD i.val 0)
    (hclB : ∀ i : Fin k, cl.getD i.val 0 < 45)
    (rows cols : List (List ℕ))
    (hchk : certChk rows cols k stairCertP = true)
    (hent : ((List.range k).all fun i => (List.range k).all fun j =>
      decide (corZStair stairMZ (rl.getD i 0) (cl.getD j 0) % (stairCertP : ℤ) =
        (((rows.getD i []).getD j 0 : ℕ) : ℤ))) = true) :
    (Matrix.of fun i j : Fin k =>
      corStairQ ((1 - vecMulVec stairQX1 stairQY1) ⊗ₖ (1 - vecMulVec stairQX2 stairQY2))
        (rl.getD i.val 0) (cl.getD j.val 0)).det ≠ 0 := by
  have heq : (Matrix.of fun i j : Fin k =>
      corStairQ ((1 - vecMulVec stairQX1 stairQY1) ⊗ₖ (1 - vecMulVec stairQX2 stairQY2))
        (rl.getD i.val 0) (cl.getD j.val 0)) =
    (Matrix.of fun r c : Fin k =>
      stairCornerQ (⟨rl.getD r.val 0, by have := hrl r; have := hX; omega⟩ : Fin 45)
        (⟨cl.getD c.val 0, hclB c⟩ : Fin 45)) := by
    ext i j
    simp [stairMQ, stairCornerQ, stairCornerQOf]
  rw [heq]
  exact n7_cert_det hX rl cl hrl hcl hclB rows cols hchk hent

/-- **COMPOSE** — hM1's witness: cert 1 (rows 0..24, cols 20..44). -/
theorem n7_m1_witdet :
    (Matrix.of fun i j : Fin 25 =>
      corStairQ ((1 - vecMulVec stairQX1 stairQY1) ⊗ₖ (1 - vecMulVec stairQX2 stairQY2))
        (n2cR1.getD i.val 0) (n2cC1.getD j.val 0)).det ≠ 0 :=
  n7_witdet_gen 25 25 20 (by omega) n2cR1 n2cC1 (by decide) (by decide) (by decide)
    n2cS1 n2cT1 n2cChk1 n2cEnt1

/-- **COMPOSE** — the t-th run-2 certificate's row/col/S/T dispatch
(the `n7_hM2_witness` map: 0→12, 1→16, 2→8, 3→11, 4→14, 5→18, 6→21, 7→13, 8→17, 9→20,
10→22, 11→10, 12→19, 13→9, 14→23, 15→24, 16→15, 17→7). -/
def n7M2RL (t : ℕ) : List ℕ :=
  match t with
  | 0 => n2cR12 | 1 => n2cR16 | 2 => n2cR8 | 3 => n2cR11 | 4 => n2cR14 | 5 => n2cR18
  | 6 => n2cR21 | 7 => n2cR13 | 8 => n2cR17 | 9 => n2cR20 | 10 => n2cR22 | 11 => n2cR10
  | 12 => n2cR19 | 13 => n2cR9 | 14 => n2cR23 | 15 => n2cR24 | 16 => n2cR15 | _ => n2cR7

def n7M2CL (t : ℕ) : List ℕ :=
  match t with
  | 0 => n2cC12 | 1 => n2cC16 | 2 => n2cC8 | 3 => n2cC11 | 4 => n2cC14 | 5 => n2cC18
  | 6 => n2cC21 | 7 => n2cC13 | 8 => n2cC17 | 9 => n2cC20 | 10 => n2cC22 | 11 => n2cC10
  | 12 => n2cC19 | 13 => n2cC9 | 14 => n2cC23 | 15 => n2cC24 | 16 => n2cC15 | _ => n2cC7

def n7M2SL (t : ℕ) : List (List ℕ) :=
  match t with
  | 0 => n2cS12 | 1 => n2cS16 | 2 => n2cS8 | 3 => n2cS11 | 4 => n2cS14 | 5 => n2cS18
  | 6 => n2cS21 | 7 => n2cS13 | 8 => n2cS17 | 9 => n2cS20 | 10 => n2cS22 | 11 => n2cS10
  | 12 => n2cS19 | 13 => n2cS9 | 14 => n2cS23 | 15 => n2cS24 | 16 => n2cS15 | _ => n2cS7

def n7M2TL (t : ℕ) : List (List ℕ) :=
  match t with
  | 0 => n2cT12 | 1 => n2cT16 | 2 => n2cT8 | 3 => n2cT11 | 4 => n2cT14 | 5 => n2cT18
  | 6 => n2cT21 | 7 => n2cT13 | 8 => n2cT17 | 9 => n2cT20 | 10 => n2cT22 | 11 => n2cT10
  | 12 => n2cT19 | 13 => n2cT9 | 14 => n2cT23 | 15 => n2cT24 | 16 => n2cT15 | _ => n2cT7

/-- **COMPOSE** — the run-2 certificate pins (rows `< 26+t`, cols `≥ 2+t`, cols `< 45`). -/
theorem n7_m2_pins (t : ℕ) (ht : t < 18) :
    (∀ i : Fin 26, n7M2RL t.getD i.val 0 < 26 + t) ∧
      (∀ i : Fin 26, 2 + t ≤ n7M2CL t.getD i.val 0) ∧
      (∀ i : Fin 26, n7M2CL t.getD i.val 0 < 45) := by
  interval_cases t <;> simp only [n7M2RL, n7M2CL] <;> decide

/-- **COMPOSE** — hM2's witness: the 18 N2c 26-certificates (the `n7_hM2_witness`
dispatch, at the `corStairQ`-of-witness form). -/
theorem n7_m2_witdet : ∀ t : ℕ, t < 18 →
    (Matrix.of fun i j : Fin 26 =>
      corStairQ ((1 - vecMulVec stairQX1 stairQY1) ⊗ₖ (1 - vecMulVec stairQX2 stairQY2))
        (n7M2RL t.getD i.val 0) (n7M2CL t.getD j.val 0)).det ≠ 0 := by
  intro t ht
  interval_cases t <;> simp only [n7M2RL, n7M2CL] <;>
    first
    | exact n7_witdet_gen 26 26 2 (by omega) n2cR12 n2cC12 (by decide) (by decide) (by decide)
        n2cS12 n2cT12 n2cChk12 n2cEnt12
    | exact n7_witdet_gen 26 27 3 (by omega) n2cR16 n2cC16 (by decide) (by decide) (by decide)
        n2cS16 n2cT16 n2cChk16 n2cEnt16
    | exact n7_witdet_gen 26 28 4 (by omega) n2cR8 n2cC8 (by decide) (by decide) (by decide)
        n2cS8 n2cT8 n2cChk8 n2cEnt8
    | exact n7_witdet_gen 26 29 5 (by omega) n2cR11 n2cC11 (by decide) (by decide) (by decide)
        n2cS11 n2cT11 n2cChk11 n2cEnt11
    | exact n7_witdet_gen 26 30 6 (by omega) n2cR14 n2cC14 (by decide) (by decide) (by decide)
        n2cS14 n2cT14 n2cChk14 n2cEnt14
    | exact n7_witdet_gen 26 31 7 (by omega) n2cR18 n2cC18 (by decide) (by decide) (by decide)
        n2cS18 n2cT18 n2cChk18 n2cEnt18
    | exact n7_witdet_gen 26 32 8 (by omega) n2cR21 n2cC21 (by decide) (by decide) (by decide)
        n2cS21 n2cT21 n2cChk21 n2cEnt21
    | exact n7_witdet_gen 26 33 9 (by omega) n2cR13 n2cC13 (by decide) (by decide) (by decide)
        n2cS13 n2cT13 n2cChk13 n2cEnt13
    | exact n7_witdet_gen 26 34 10 (by omega) n2cR17 n2cC17 (by decide) (by decide) (by decide)
        n2cS17 n2cT17 n2cChk17 n2cEnt17
    | exact n7_witdet_gen 26 35 11 (by omega) n2cR20 n2cC20 (by decide) (by decide) (by decide)
        n2cS20 n2cT20 n2cChk20 n2cEnt20
    | exact n7_witdet_gen 26 36 12 (by omega) n2cR22 n2cC22 (by decide) (by decide) (by decide)
        n2cS22 n2cT22 n2cChk22 n2cEnt22
    | exact n7_witdet_gen 26 37 13 (by omega) n2cR10 n2cC10 (by decide) (by decide) (by decide)
        n2cS10 n2cT10 n2cChk10 n2cEnt10
    | exact n7_witdet_gen 26 38 14 (by omega) n2cR19 n2cC19 (by decide) (by decide) (by decide)
        n2cS19 n2cT19 n2cChk19 n2cEnt19
    | exact n7_witdet_gen 26 39 15 (by omega) n2cR9 n2cC9 (by decide) (by decide) (by decide)
        n2cS9 n2cT9 n2cChk9 n2cEnt9
    | exact n7_witdet_gen 26 40 16 (by omega) n2cR23 n2cC23 (by decide) (by decide) (by decide)
        n2cS23 n2cT23 n2cChk23 n2cEnt23
    | exact n7_witdet_gen 26 41 17 (by omega) n2cR24 n2cC24 (by decide) (by decide) (by decide)
        n2cS24 n2cT24 n2cChk24 n2cEnt24
    | exact n7_witdet_gen 26 42 18 (by omega) n2cR15 n2cC15 (by decide) (by decide) (by decide)
        n2cS15 n2cT15 n2cChk15 n2cEnt15
    | exact n7_witdet_gen 26 43 19 (by omega) n2cR7 n2cC7 (by decide) (by decide) (by decide)
        n2cS7 n2cT7 n2cChk7 n2cEnt7

/-- **COMPOSE** — the rank-minor fuel: the det of the `(rl, cl)` minor of the staircase
corner, as a polynomial in the pair labels (the `pDatStair` construction restricted to a
`k × k` minor). -/
noncomputable def pMStairL (k : ℕ) (rl cl : List ℕ)
    (P₁ P₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) : Rp (19 + 4) :=
  (Matrix.of fun i j : Fin k => corStairR (kM P₁ P₂) (rl.getD i.val 0) (cl.getD j.val 0)).det

/-- `eval_pDatStair_of` for the minor det (its proof verbatim, `45 → k`). -/
lemma eval_pMStairL (f : Vr (19 + 4) → ℚ) (k : ℕ) (rl cl : List ℕ)
    (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h1 : sconj (Uf f) P₁ = (Uf f).det • W₁) (h2 : sconj (Vf f) P₂ = (Vf f).det • W₂) :
    eval f (pMStairL k rl cl P₁ P₂) =
      ((Uf f).det * (Vf f).det) ^ k *
        (Matrix.of fun i j : Fin k =>
          corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) (rl.getD i.val 0) (cl.getD j.val 0)).det := by
  have key : (kM P₁ P₂).map (eval f) = ((Uf f).det * (Vf f).det) • ((1 - W₁) ⊗ₖ (1 - W₂)) := by
    rw [map_kM, h1, h2, ← smul_sub, ← smul_sub, smul_kronecker, kronecker_smul, smul_smul]
  rw [pMStairL, eval_det]
  have hmat : (Matrix.of fun i j : Fin k =>
      corStairR (kM P₁ P₂) (rl.getD i.val 0) (cl.getD j.val 0)).map (eval f) =
      ((Uf f).det * (Vf f).det) •
        (Matrix.of fun i j : Fin k =>
          corStairR ((1 - W₁) ⊗ₖ (1 - W₂)) (rl.getD i.val 0) (cl.getD j.val 0)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [eval_corStairR f (kM P₁ P₂) (rl.getD i.val 0) (cl.getD j.val 0), key, corStairR_smul]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [hmat, det_smul, Fintype.card_fin]
  have hdet_eq : (Matrix.of fun i j : Fin k =>
      corStairR ((1 - W₁) ⊗ₖ (1 - W₂)) (rl.getD i.val 0) (cl.getD j.val 0)) =
    (Matrix.of fun i j : Fin k =>
      corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) (rl.getD i.val 0) (cl.getD j.val 0)) := by
    ext i j
    simp only [Matrix.of_apply, corStairR_rat]
  rw [hdet_eq]

/-- `pDatStair_ne` for the minor det. -/
lemma pMStairL_ne (k : ℕ) (rl cl : List ℕ)
    (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂) (k₁ : W₁ * W₁ = W₁) (k₂ : W₂ * W₂ = W₂)
    (t₁ : P₁.trace = W₁.trace) (t₂ : P₂.trace = W₂.trace)
    (hc : (Matrix.of fun i j : Fin k =>
      corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) (rl.getD i.val 0) (cl.getD j.val 0)).det ≠ 0) :
    pMStairL k rl cl P₁ P₂ ≠ 0 := by
  obtain ⟨U, hU, e1⟩ := conj_wit P₁ W₁ h₁ k₁ t₁
  obtain ⟨V, hV, e2⟩ := conj_wit P₂ W₂ h₂ k₂ t₂
  intro h0
  have h2 := congrArg (eval (ptUV U V)) h0
  rw [eval_pMStairL (ptUV U V) k rl cl P₁ P₂ W₁ W₂ (by rw [Uf_pt]; exact e1)
    (by rw [Vf_pt]; exact e2), Uf_pt, Vf_pt, map_zero] at h2
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hU hV)) hc h2

/-- **COMPOSE** — the run-1 diagonal-deviation fuel: the `pT` cross-det pattern with the
staircase entries `(n7Fin l, n7Fin (l+1))`; `eval f` is `(detU*detV)` times the run-1
deviation of the conjugated labels. -/
noncomputable def pDevStair (l : ℕ) (P₁ P₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    Rp (19 + 4) :=
  MvPolynomial.C (stairRunB l) * pA XU P₁ (n7Fin l) (n7Fin (l + 1)) * (XV (n := 19 + 4)).det +
    MvPolynomial.C (stairRunA l) * pA XV P₂ (n7Fin l) (n7Fin (l + 1)) * (XU (n := 19 + 4)).det

lemma eval_pDevStair (f : Vr (19 + 4) → ℚ) (l : ℕ)
    (P₁ P₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    eval f (pDevStair l P₁ P₂) =
      sconj (Uf f) P₁ (n7Fin l) (n7Fin (l + 1)) * (Vf f).det +
        sconj (Vf f) P₂ (n7Fin l) (n7Fin (l + 1)) * (Uf f).det := by
  simp only [pDevStair, map_add, map_mul, MvPolynomial.eval_C, eval_pA_U, eval_pA_V,
    eval_detU, eval_detV]

/-- `pDatStair_ne` for the deviation (witness: `n7_hT_witness`). -/
lemma pDevStair_ne (l : ℕ) (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂) (k₁ : W₁ * W₁ = W₁) (k₂ : W₂ * W₂ = W₂)
    (t₁ : P₁.trace = W₁.trace) (t₂ : P₂.trace = W₂.trace)
    (hdev : stairRunA l * W₂ (n7Fin l) (n7Fin (l + 1))
        + stairRunB l * W₁ (n7Fin l) (n7Fin (l + 1)) ≠ 0) :
    pDevStair l P₁ P₂ ≠ 0 := by
  obtain ⟨U, hU, e1⟩ := conj_wit P₁ W₁ h₁ k₁ t₁
  obtain ⟨V, hV, e2⟩ := conj_wit P₂ W₂ h₂ k₂ t₂
  intro h0
  have h2 := congrArg (eval (ptUV U V)) h0
  rw [eval_pDevStair, Uf_pt, Vf_pt, e1, e2, map_zero, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul] at h2
  have hX : U.det * V.det * (stairRunA l * W₂ (n7Fin l) (n7Fin (l + 1))
      + stairRunB l * W₁ (n7Fin l) (n7Fin (l + 1)))
      = stairRunB l * (U.det * W₁ (n7Fin l) (n7Fin (l + 1))) * V.det
        + stairRunA l * (V.det * W₂ (n7Fin l) (n7Fin (l + 1))) * U.det := by
    ring
  rw [hX] at h2
  exact mul_ne_zero (mul_ne_zero hU hV) hdev h2

/-- **N7** — `data_edge_stair` restated in the staircase frame (the old r6-frame statement in
Signature.lean is deleted: its pivot hypothesis came from `isPiv_stair_lower`, REFUTED — N2d,
the frame is the wrong one). Statement deltas vs the N5-1 version (recorded in SCAFFOLD.md
"## N7 NOTES"): conclusion `DataE' (qMStair M)`; the `hpiv` slot is replaced by
`(hdet, hcorner)` — hdet is the staircase-frame corner det (a hypothesis in general,
`stair_data_cert` at the witness) and hcorner is exactly the corner-hole contract above. The
middle clause of hpiv is derived internally from `isPiv_stairMid` (Projector.lean, PROVED).
The edge-extraction body (hMM/hrank/hok/hnd/edge_singles) is the N5-1 proof with
`qM` → `qMStair`. -/
theorem data_edge_stair (x1 y1 x2 y2 : Fin 23 → ℚ)
    (h1 : y1 ⬝ᵥ x1 = 1) (h2 : y2 ⬝ᵥ x2 = 1)
    (hdet : (stairCornerQOf ((1 - vecMulVec x1 y1) ⊗ₖ (1 - vecMulVec x2 y2))).det ≠ 0)
    (hcorner : ∀ p ∈ runPairs (stairCornerRuns 23 529),
      IsPiv (qMStair (stairPairM x1 y1 x2 y2)) p.1 p.2) :
    DataE' (qMStair ((1 - vecMulVec x1 y1) ⊗ₖ (1 - vecMulVec x2 y2))) := by
  rw [stairPairM] at hcorner
  set M := (1 - vecMulVec x1 y1) ⊗ₖ (1 - vecMulVec x2 y2) with hMdef
  have hMM : M * M = M := by
    rw [hMdef, ← mul_kronecker_mul, one_sub_vmv_idem x1 y1 h1, one_sub_vmv_idem x2 y2 h2]
  have hq := qMStair_idem hMM
  have hrank : (qMStair M).rank = 484 := by
    have hr1 := rank_eq_trace (qMStair M) hq
    rw [qMStair_trace, hMdef, trace_kronecker, trace_one_sub_vmv x1 y1 h1,
      trace_one_sub_vmv x2 y2 h2] at hr1
    apply Nat.cast_injective (R := ℚ); rw [hr1]; norm_num
  have hok : ∀ ρ ∈ stairDataRuns 23 529, RunOK 529 ρ := fun ρ hρ =>
    stairRunOK ρ (List.mem_append.2 (Or.inl hρ))
  have hnd : (runPairs (stairDataRuns 23 529)).Nodup := by
    rw [stairDataRuns_eval, DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_cons,
      DEPort.runPairs_nil, List.append_nil, List.nodup_append]
    refine ⟨DEPort.nodup_run _ _ _, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨DEPort.nodup_run _ _ _, DEPort.nodup_run _ _ _, ?_⟩
      intro a ha b hb hab
      rw [DEPort.mem_run] at ha hb
      obtain ⟨k, hk, rfl⟩ := ha
      obtain ⟨k', hk', rfl⟩ := hb
      simp only [Prod.mk.injEq] at hab
      omega
    · intro a ha b hb hab
      rw [DEPort.mem_run] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      simp only [List.mem_append, DEPort.mem_run] at hb
      rcases hb with ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩ <;>
        simp only [Prod.mk.injEq] at hab <;> omega
  -- hpiv: the middle run is isPiv_stairMid (PROVED); the corner runs are hcorner
  have hmid := isPiv_stairMid x1 y1 x2 y2 h1 h2 hdet
  have hcr : runPairs (stairCornerRuns 23 529) =
      (List.range 21).map (fun k => (1 + k, 507 + k)) ++
        (List.range 18).map (fun k => (25 + k, 486 + k)) := by
    simp [stairCornerRuns, runPairs]
  have hpM : ∀ p ∈ runPairs (stairDataRuns 23 529), IsPiv (qMStair M) p.1 p.2 := by
    intro p hp
    have hsplit : runPairs (stairDataRuns 23 529) =
        (List.range 439).map (fun k => (45 + k, 45 + k)) ++
          ((List.range 21).map (fun k => (1 + k, 507 + k)) ++
            (List.range 18).map (fun k => (25 + k, 486 + k))) := by
      simp [stairDataRuns_eval, runPairs]
    rw [hsplit] at hp
    rcases List.mem_append.1 hp with h1 | h2
    · rw [DEPort.mem_run] at h1
      obtain ⟨k, hk, rfl⟩ := h1
      exact hmid (45 + k) (by omega) (by omega)
    · rcases List.mem_append.1 h2 with h2' | h3
      · exact hcorner p (by rw [hcr]; exact List.mem_append.2 (Or.inl h2'))
      · exact hcorner p (by rw [hcr]; exact List.mem_append.2 (Or.inr h3))
  obtain ⟨e, he, rs', hruns, hsing, hlen⟩ :=
    DEPort.edge_singles (m := 529) (by omega) (qMStair M) hq _ hok hnd hpM
  have hl : (runPairs (stairDataRuns 23 529)).length = 478 := by
    unfold stairDataRuns stairCornerRuns runPairs
    decide
  have h6 : rs'.length = 6 := by
    rw [hrank, hl] at hlen
    omega
  show ∃ e : Edge 529, EdgeQ e (qMStair M) ∧ ∃ rs', e.runs = stairDataRuns 23 529 ++ rs' ∧
    (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 6
  exact ⟨e, he, rs', hruns, hsing, h6⟩

namespace N52

/-! ## R7-8 — the staircase-frame flag_gen (the N5-2 port with `S := SbStair U V`)

One witness pair serves all three classes (AuxE + SideE + DataE'), so moving the DataE clause
to the staircase frame forces `S := SbStair U V` (SCAFFOLD.md "## N7 NOTES", Discovery 2). The
Pall product widens the `pA` factor from `\u220f β` to `\u220f β l` (pA_all_ne) so the label facts
strengthen to `(\u2200 β, x' β ≠ 0) ∧ (\u2200 l, y' l ≠ 0)`. hu/hv/hT and the old `isPiv_stair_lower`
consumption are GONE (the data clause needs only h1 h2 hdet hcorner). Statement unchanged. -/
theorem flag_gen_stair_aux (w1 v1 w2 v2 : Fin (19 + 4) → ℚ) (hw1 : v1 ⬝ᵥ w1 = 1) (hw2 : v2 ⬝ᵥ w2 = 1)
    (hcert : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairQ ((1 - vecMulVec w1 v1) ⊗ₖ (1 - vecMulVec w2 v2)) i.val j.val).det ≠ 0)
    (Lab : Finset ((Fin (19 + 4) → ℚ) × (Fin (19 + 4) → ℚ))) (hLab : ∀ p ∈ Lab, p.2 ⬝ᵥ p.1 = 1)
    (Pis : Finset (Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)) (hPis : ∀ A ∈ Pis, A * A = A) :
    ∃ (S : Matrix (Fin ((19 + 4) * (19 + 4))) (Pr (19 + 4)) ℚ)
      (Sinv : Matrix (Pr (19 + 4)) (Fin ((19 + 4) * (19 + 4))) ℚ),
      S * Sinv = 1 ∧ Sinv * S = 1 ∧
      (∀ p ∈ Lab, AuxE (h := 19) (S * ((1 : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) ⊗ₖ
          (1 - vecMulVec p.1 p.2)) * Sinv) ∧
        AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ (1 : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)) *
          Sinv)) ∧
      (∀ p ∈ Lab, ∀ A ∈ Pis, SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
        SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
      (∀ p1 ∈ Lab, ∀ p2 ∈ Lab,
        DataE' (h := 19) (S * ((1 - vecMulVec p1.1 p1.2) ⊗ₖ (1 - vecMulVec p2.1 p2.2)) * Sinv)) := by
  classical
  have hn : 0 < 19 + 4 := by omega
  let Pall : Rp (19 + 4) :=
    (XU (n := 19 + 4)).det * (XV (n := 19 + 4)).det *
      (∏ p ∈ Lab, ∏ β : Fin (19 + 4), ∏ l : Fin (19 + 4),
        (pA XU (vecMulVec p.1 p.2) β l * pA XV (vecMulVec p.1 p.2) β l)) *
      (∏ A ∈ Pis.filter (fun A => 19 + 4 < 2 * A.rank),
        (pCor XU A A.rank * pCor XV A A.rank)) *
      (∏ q ∈ Lab ×ˢ Lab, (pDatStair (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2) *
        ((pMStairL 25 n2cR1 n2cC1 (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2) *
          ∏ t : Fin 18, pMStairL 26 (n7M2RL t.val) (n7M2CL t.val)
            (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2)) *
        ∏ l ∈ Finset.Icc 1 21, pDevStair l (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2))))
  -- COMPOSE: the r6-shape `pT` factors are DROPPED (their consumer `isPiv_stair_lower`
  -- was refuted); the staircase `hT`/`hM1`/`hM2` fuels are `pDevStair`/`pMStairL`
  -- (witness-nonzero via the witness matrices + the N2c certificates).
  have hP : Pall ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero detU_ne detV_ne) ?_) ?_) ?_
    · refine prod_ne_zero_iff.2 fun p hp => prod_ne_zero_iff.2 fun β _ => ?_
      refine prod_ne_zero_iff.2 fun l _ => mul_ne_zero ?_ ?_
      · exact pA_all_ne hn _ (vmv_idem _ _ (hLab p hp)) (lab_trace _ _ (hLab p hp)) β l
      · exact pA_all_ne_V hn _ (vmv_idem _ _ (hLab p hp)) (lab_trace _ _ (hLab p hp)) β l
    · refine prod_ne_zero_iff.2 fun A hA => ?_
      rw [Finset.mem_filter] at hA
      exact mul_ne_zero (pCor_U_ne A (hPis A hA.1) _ rfl hA.2) (pCor_V_ne A (hPis A hA.1) _ rfl hA.2)
    · refine prod_ne_zero_iff.2 fun q hq => ?_
      rw [Finset.mem_product] at hq
      have d1 := hLab _ hq.1
      have d2 := hLab _ hq.2
      refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
      · exact pDatStair_ne _ _ _ _ (vmv_idem _ _ d1) (vmv_idem _ _ d2) (vmv_idem _ _ hw1)
          (vmv_idem _ _ hw2) ((lab_trace _ _ d1).trans (lab_trace _ _ hw1).symm)
          ((lab_trace _ _ d2).trans (lab_trace _ _ hw2).symm) hcert
      · refine mul_ne_zero
          (pMStairL_ne 25 n2cR1 n2cC1 _ _ _ _ (vmv_idem _ _ d1) (vmv_idem _ _ d2)
            (vmv_idem _ _ stairQxy1) (vmv_idem _ _ stairQxy2)
            ((lab_trace _ _ d1).trans (lab_trace _ _ stairQxy1).symm)
            ((lab_trace _ _ d2).trans (lab_trace _ _ stairQxy2).symm) n7_m1_witdet)
          (prod_ne_zero_iff.2 fun t _ =>
            pMStairL_ne 26 (n7M2RL t.val) (n7M2CL t.val) _ _ _ _ (vmv_idem _ _ d1)
              (vmv_idem _ _ d2) (vmv_idem _ _ stairQxy1) (vmv_idem _ _ stairQxy2)
              ((lab_trace _ _ d1).trans (lab_trace _ _ stairQxy1).symm)
              ((lab_trace _ _ d2).trans (lab_trace _ _ stairQxy2).symm)
              (n7_m2_witdet t.val t.isLt))
      · exact prod_ne_zero_iff.2 fun l hl =>
          pDevStair_ne l _ _ _ _ (vmv_idem _ _ d1) (vmv_idem _ _ d2)
            (vmv_idem _ _ stairQxy1) (vmv_idem _ _ stairQxy2)
            ((lab_trace _ _ d1).trans (lab_trace _ _ stairQxy1).symm)
            ((lab_trace _ _ d2).trans (lab_trace _ _ stairQxy2).symm)
            (fun h0 =>
              n7_hT_witness l (Finset.mem_Icc.1 hl).1 (Finset.mem_Icc.1 hl).2
                (by linear_combination h0))
  obtain ⟨f, hf⟩ := exists_eval_ne Pall hP
  simp only [Pall, map_mul, map_prod, mul_ne_zero_iff, prod_ne_zero_iff, Finset.mem_univ,
    true_implies] at hf
  obtain ⟨⟨⟨⟨hdU, hdV⟩, hlab⟩, hpis⟩, hdat⟩ := hf
  rw [eval_detU] at hdU
  rw [eval_detV] at hdV
  set U := Uf f with hUdef
  set V := Vf f with hVdef
  -- label facts (strengthened: all coordinates nonzero)
  have labU : ∀ p ∈ Lab, (∀ β, (Uᵀ *ᵥ p.1) β ≠ 0) ∧ (∀ l, (U⁻¹ *ᵥ p.2) l ≠ 0) := by
    intro p hp
    have h := fun β l => lab_of_sconj U hdU p.1 p.2 β l (by rw [← eval_pA_U]; exact (hlab p hp β l).1)
    exact ⟨fun β => (h β β).1, fun l => (h ⟨0, by omega⟩ l).2⟩
  have labV : ∀ p ∈ Lab, (∀ β, (Vᵀ *ᵥ p.1) β ≠ 0) ∧ (∀ l, (V⁻¹ *ᵥ p.2) l ≠ 0) := by
    intro p hp
    have h := fun β l => lab_of_sconj V hdV p.1 p.2 β l (by rw [← eval_pA_V]; exact (hlab p hp β l).2)
    exact ⟨fun β => (h β β).1, fun l => (h ⟨0, by omega⟩ l).2⟩
  have one_c : ∀ W : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ, W.det ≠ 0 → Wᵀ * 1 * W⁻¹ᵀ = 1 :=
    fun W hW => by rw [Matrix.mul_one, conj_one W hW]
  refine ⟨SbStair U V, SbiStair U V, (SbStair_inv U V hdU hdV).1, (SbStair_inv U V hdU hdV).2, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hxU, hyU⟩ := labU p hp
    obtain ⟨hxV, hyV⟩ := labV p hp
    constructor
    · rw [SbStair_conj, one_c U hdU, conj_sub_vmv V hdV]
      exact aux1_edge_Stair _ _ (conj_dot V hdV _ _ (hLab p hp)) (fun β _ => hxV β) hyV
    · rw [SbStair_conj, one_c V hdV, conj_sub_vmv U hdU]
      exact aux2_edge_Stair _ _ (conj_dot U hdU _ _ (hLab p hp)) (fun β _ => hxU β) hyU
  · intro p hp A hA
    obtain ⟨hxU, hyU⟩ := labU p hp
    obtain ⟨hxV, hyV⟩ := labV p hp
    have hcorU : 19 + 4 < 2 * A.rank → _ := fun hr => corner_of_pCor U A hdU A.rank (by
      rw [← eval_pCor_U]; exact (hpis A (Finset.mem_filter.2 ⟨hA, hr⟩)).1)
    have hcorV : 19 + 4 < 2 * A.rank → _ := fun hr => corner_of_pCor V A hdV A.rank (by
      rw [← eval_pCor_V]; exact (hpis A (Finset.mem_filter.2 ⟨hA, hr⟩)).2)
    constructor
    · rw [SbStair_conj, conj_vmv]
      exact side1_edge_Stair _ _ (conj_dot V hdV _ _ (hLab p hp)) (fun β _ => hxV β) hyV _
        (conj_idem U hdU A (hPis A hA)) A.rank (conj_rank U hdU A) hcorU
    · rw [SbStair_conj, conj_vmv]
      exact side2_edge_Stair _ _ (conj_dot U hdU _ _ (hLab p hp)) (fun β _ => hxU β) hyU _
        (conj_idem V hdV A (hPis A hA)) A.rank (conj_rank V hdV A) hcorV
  · intro p1 hp1 p2 hp2
    obtain ⟨hD, hPM, hPD⟩ := hdat (p1, p2) (Finset.mem_product.2 ⟨hp1, hp2⟩)
    obtain ⟨hM1e, hM2e⟩ := hPM
    rw [SbStair_conj, conj_sub_vmv U hdU, conj_sub_vmv V hdV]
    -- COMPOSE: data_edge_stair at qMStair; hdet from pDatStair; the corner clause's five
    -- hypotheses derived at the conjugated labels: hu/hv from the label facts (labU/labV),
    -- hT from the pDevStair factor, hM1/hM2 from the pMStairL factors (cert minors).
    have hc1 : (U⁻¹ *ᵥ p1.2) ⬝ᵥ (Uᵀ *ᵥ p1.1) = 1 := conj_dot U hdU _ _ (hLab _ hp1)
    have hc2 : (V⁻¹ *ᵥ p2.2) ⬝ᵥ (Vᵀ *ᵥ p2.1) = 1 := conj_dot V hdV _ _ (hLab _ hp2)
    have t := hD
    rw [eval_pDatStair_of f _ _ _ _ (sconj_eq U _ hdU) (sconj_eq V _ hdV), ← hUdef,
      ← hVdef, conj_vmv, conj_vmv] at t
    obtain ⟨hxU1, hyU1⟩ := labU p1 hp1
    obtain ⟨hxV2, hyV2⟩ := labV p2 hp2
    have hu' : (Uᵀ *ᵥ p1.1) ⟨0, by omega⟩ * (Vᵀ *ᵥ p2.1) ⟨0, by omega⟩ ≠ 0 :=
      mul_ne_zero (hxU1 _) (hxV2 _)
    have hv' : (U⁻¹ *ᵥ p1.2) ⟨22, by omega⟩ * (V⁻¹ *ᵥ p2.2) ⟨22, by omega⟩ ≠ 0 :=
      mul_ne_zero (hyU1 _) (hyV2 _)
    have hT' : ∀ l : ℕ, 1 ≤ l → l ≤ 21 →
        stairRunA l * (Vᵀ *ᵥ p2.1) (n7Fin l) * (V⁻¹ *ᵥ p2.2) (n7Fin (l + 1))
          + stairRunB l * (Uᵀ *ᵥ p1.1) (n7Fin l) * (U⁻¹ *ᵥ p1.2) (n7Fin (l + 1)) ≠ 0 := by
      intro l hl1 hl2
      have he := hPD l (Finset.mem_Icc.2 ⟨hl1, hl2⟩)
      rw [eval_pDevStair, ← hUdef, ← hVdef, sconj_eq U _ hdU, sconj_eq V _ hdV,
        conj_vmv, conj_vmv] at he
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul] at he
      refine fun h0 => he ?_
      linear_combination (U.det * V.det) * h0
    have hM1' : 25 ≤ rk (stairCornerQOf (stairPairM (Uᵀ *ᵥ p1.1) (U⁻¹ *ᵥ p1.2)
        (Vᵀ *ᵥ p2.1) (V⁻¹ *ᵥ p2.2))) 25 20 := by
      have he := hM1e
      rw [eval_pMStairL f 25 n2cR1 n2cC1 _ _ _ _ (sconj_eq U _ hdU) (sconj_eq V _ hdV),
        ← hUdef, ← hVdef, conj_vmv, conj_vmv] at he
      have hdet := right_ne_zero_of_mul he
      have hB : ∀ i : Fin 25, n2cR1.getD i.val 0 < 25 ∧ 20 ≤ n2cC1.getD i.val 0
          ∧ n2cC1.getD i.val 0 < 45 := by decide
      exact rk_ge_of_det _ 25 20
        (fun i => ⟨⟨n2cR1.getD i.val 0, by have := hB i; omega⟩, by have := hB i; omega⟩)
        (fun j => ⟨⟨n2cC1.getD j.val 0, (hB j).2.2⟩, (hB j).2.1⟩) hdet
    have hM2' : ∀ t : ℕ, t < 18 →
        26 ≤ rk (stairCornerQOf (stairPairM (Uᵀ *ᵥ p1.1) (U⁻¹ *ᵥ p1.2)
          (Vᵀ *ᵥ p2.1) (V⁻¹ *ᵥ p2.2))) (26 + t) (2 + t) := by
      intro t ht
      obtain ⟨p1', p2', p3'⟩ := n7_m2_pins t ht
      have he := hM2e ⟨t, by omega⟩
      rw [eval_pMStairL f 26 (n7M2RL t) (n7M2CL t) _ _ _ _ (sconj_eq U _ hdU)
        (sconj_eq V _ hdV), ← hUdef, ← hVdef, conj_vmv, conj_vmv] at he
      have hdet := right_ne_zero_of_mul he
      exact rk_ge_of_det _ (26 + t) (2 + t)
        (fun i => ⟨⟨n7M2RL t.getD i.val 0, p1' i⟩, by have := p1' i; omega⟩)
        (fun j => ⟨⟨n7M2CL t.getD j.val 0, p3' j⟩, p2' j⟩) hdet
    refine data_edge_stair _ _ _ _ hc1 hc2 (right_ne_zero_of_mul t)
      (isPiv_stairCorner_contract _ _ _ _ hu' hv' hT' hM1' hM2')

end N52

section

open N52

/-- **N5-2/N7** — `flagBasis_stair`: verbatim mirror of flagBasis_sol_aux
(nb_flagBasis_solution.lean:184-198) with the data clause `DataE (h := 19)` →
`DataE' (h := 19)` and the internal witness qx*/qy*/data_cert → stairQ*/stair_data_cert.
STATEMENT BYTE-IDENTICAL to the audited N5-2 version. N7 change: the witness pair is the
STAIRCASE frame's `SbStair U V` (the DataE clause lives at `qMStair`; one S serves all three
classes), and the internal flag_gen is `N52.flag_gen_stair_aux` (Rewire.lean). -/
theorem flagBasis_stair
    (Lab : Finset ((Fin (19 + 4) → ℚ) × (Fin (19 + 4) → ℚ)))
    (hLab : ∀ p ∈ Lab, p.2 ⬝ᵥ p.1 = 1)
    (Pis : Finset (Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ))
    (hPis : ∀ A ∈ Pis, A * A = A) :
    ∃ (S : Matrix (Fin ((19 + 4) * (19 + 4))) (Pr (19 + 4)) ℚ)
      (Sinv : Matrix (Pr (19 + 4)) (Fin ((19 + 4) * (19 + 4))) ℚ),
      S * Sinv = 1 ∧ Sinv * S = 1 ∧
      (∀ p ∈ Lab, AuxE (h := 19) (S * ((1 : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) ⊗ₖ
          (1 - vecMulVec p.1 p.2)) * Sinv) ∧
        AuxE (h := 19) (S * ((1 - vecMulVec p.1 p.2) ⊗ₖ
          (1 : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)) * Sinv)) ∧
      (∀ p ∈ Lab, ∀ A ∈ Pis, SideE (h := 19) (S * (A ⊗ₖ vecMulVec p.1 p.2) * Sinv) A.rank ∧
        SideE (h := 19) (S * (vecMulVec p.1 p.2 ⊗ₖ A) * Sinv) A.rank) ∧
      (∀ p₁ ∈ Lab, ∀ p₂ ∈ Lab,
        DataE' (h := 19) (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) *
          Sinv)) := by
  exact flag_gen_stair_aux stairQX1 stairQY1 stairQX2 stairQY2 stairQxy1 stairQxy2
    stair_data_cert Lab hLab Pis hPis

end

end StaircasePort.Stair
