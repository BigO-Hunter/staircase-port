/-
# N5 — the DataE → DataE' signature-swap points

The FLAGBASIS BODY VERDICT (REPORT.md) localized the corner to ONE specialized step; this
file states the two swapped signatures (data_edge, flagBasis) and lists — as comments —
every downstream consumption point where `dataRuns`/`DataE` must become
`stairDataRuns`/`DataE'`. All listed points are otherwise GENERIC (verified against the
fetched platform bodies nb_data_edge_solution.lean / nb_flag_gen_solution.lean /
nb_flagBasis_solution.lean).

SWAP POINTS (file:line → change):
1. nb_data_edge_solution.lean:503-517 `data_edge_sol_aux` → `data_edge_stair` below:
   * :516 `e.runs = dataRuns (h+4) ((h+4)*(h+4)) ++ rs'` → `stairDataRuns 23 529 ++ rs'`
   * :517 `rs'.length = h + 5` (= 24) → `rs'.length = 6`
   * :536-552 hcorner step `isPiv_rank1_lower` on the rank-one B → N2d
     `isPiv_stair_lower` (the rank-one hyp is FALSE for the staircase B, whose
     rightmost-pivot pattern is [21-run, 18-run, 6 singletons])
   * :554-555 hmid step `isPiv_mid (k := 2h+7)` — UNCHANGED (generic; needs only hdet,
     which becomes stair_data_cert at the staircase corner)
   * :521-531 hrank trace computation — UNCHANGED (label-shape-agnostic)
   * :527-537 Cp/hCe corner identity — restated with cor → corStairQ (Cert.lean)
   * hu/hv/hT hyps :505-508 — kept verbatim (22 = h+3, 21 = h+2 at h = 19); the staircase
     may add extra nonvanishing factors (N4 note) which flag_gen's Pall absorbs.
2. nb_flag_gen_solution.lean:1049 `refine data_edge _ _ _ _ (conj_dot U hdU …) …` →
   `refine data_edge_stair …` (the ONLY call swap inside flag_gen; its skeleton :956-971 is
   generic in {h}, the corner witnesses w₁v₁w₂v₂, hcert, Lab, Pis; hcert becomes
   stair_data_cert; Pall product :977-988 absorbs extra N4 factors; conclusion's DataE
   clause → DataE').
3. nb_flagBasis_solution.lean:198 `flag_gen (h:=19) qx1 qy1 qx2 qy2 qxy1 qxy2 data_cert …`
   → `flag_gen' (h:=19) stairQX1 stairQY1 stairQX2 stairQY2 stairQxy1 stairQxy2
   stair_data_cert …` and the conclusion :196-197 `DataE (h := 19) …` → `DataE' (h := 19) …`
   (`flagBasis_stair` below). Signature consumed upstream is UNCHANGED:
   accepted_bitNetR6_mom.lean:2289 FB0_ex = `flagBasis Lab0 hLab0 Pis0 hPis0`.
4. accepted_bitNetR6_mom.lean downstream (all generic over the runs data; swap only the
   runs list): spec0 :2291 (data clause), fb_data :2323-2325 via spec0.2.2.2.2,
   en_spec :2353, good_primes field mn :2539. good_edges/good_mats/edgeMat_eq :2106,:2506-2510
   and the six-family spec interface are UNAFFECTED (side/aux classes are corner-agnostic,
   rank-parameterized).
5. Dataset level (NOT in this skeleton; port task D2): R6Chk reflective certificate regen
   for R = 28866 slots (vs r6's 36513 nodes/38286 moves), pre-verified offline BEFORE Lean
   (the plain line's death was defective published densify data, Thm_pnd_obstruction.lean:10-22).
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Data
import StaircasePort.Cert
import StaircasePort.Pivot
set_option maxRecDepth 20000

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

/-! ## N5-1 ported helpers — verbatim from nb_data_edge_solution.lean (sub d536680e,
ACCEPTED; line cites below are into that file). Namespaced `DEPort` to stay clear of
N5-2 / peer files. Everything here is PROVED (no sorry): the label algebra (:485-494),
the flag-basis qM calculus (:290-303, :332-350), rank-via-trace (:389-395), the run-list
toolkit (:458-475) and `edge_singles` (:450-456, consuming the Platform.edge_of_pivs stub).
NOT ported here (owned elsewhere): the corner-identity machinery `Tm_row`/`Ti_col`/
`qM_corner`/`sum_sv_mul`/`sum_mul_sv`/`flagEquiv_top`/`flagEquiv_bot` (:305-361) and
`data_upper`/`data_diag` (:401-419) fed ONLY the rank-one corner step :536-552, which is
FALSE for the staircase and is replaced by `hpiv` (discharged by N2d `isPiv_stair_lower`);
the rk toolkit (:26-30, :83-95) is N2a's; the hmid/isPiv_mid consumption (:544-545,
:589) is inside N2d's route. -/

namespace DEPort

section Lab

variable {n : ℕ} (x y : Fin n → ℚ)

/-- Ported :485-486. -/
lemma vmv_idem (hxy : y ⬝ᵥ x = 1) : vecMulVec x y * vecMulVec x y = vecMulVec x y := by
  rw [vecMulVec_mul_vecMulVec, hxy, one_smul]

/-- Ported :488-490. -/
lemma one_sub_vmv_idem (hxy : y ⬝ᵥ x = 1) :
    (1 - vecMulVec x y) * (1 - vecMulVec x y) = 1 - vecMulVec x y := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, vmv_idem x y hxy]; abel

/-- Ported :492-494. -/
lemma trace_one_sub_vmv (hxy : y ⬝ᵥ x = 1) : (1 - vecMulVec x y).trace = (n : ℚ) - 1 := by
  rw [trace_sub, trace_one, trace_vecMulVec, dotProduct_comm, hxy, Fintype.card_fin]

end Lab

section Flag

variable {h : ℕ}

/-- Ported :290-300. -/
lemma Nm_sq : (Nm : Matrix (Pr (h + 4)) (Pr (h + 4)) ℚ) * Nm = 0 := by
  ext u w
  simp only [Matrix.mul_apply, Nm, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases h1 : u.1.val = h + 3 ∧ u.2.val < h + 3 ∧ v.1 = u.2 ∧ v.2.val = h + 3
  · rw [mul_eq_zero]; right
    rw [if_neg]
    rintro ⟨e1, -, -, -⟩
    have := h1.2.2.1
    rw [this] at e1; omega
  · rw [if_neg h1, zero_mul]

/-- Ported :302-303. -/
lemma Ti_Tm : (Ti : Matrix (Pr (h + 4)) (Pr (h + 4)) ℚ) * Tm = 1 := by
  rw [Tm, Ti, add_mul, one_mul, mul_sub, mul_one, Nm_sq]; abel

/-- Ported :332-337. -/
lemma qM_mul (M M' : Matrix (Pr (h + 4)) (Pr (h + 4)) ℚ) : qM M * qM M' = qM (M * M') := by
  unfold qM
  rw [submatrix_mul_equiv]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ti Tm (M' * Ti), Ti_Tm, Matrix.one_mul]

/-- Ported :339-340. -/
lemma qM_idem {M : Matrix (Pr (h + 4)) (Pr (h + 4)) ℚ} (hM : M * M = M) :
    qM M * qM M = qM M := by
  rw [qM_mul, hM]

/-- Ported :342-350. -/
lemma qM_trace (M : Matrix (Pr (h + 4)) (Pr (h + 4)) ℚ) : (qM M).trace = M.trace := by
  unfold qM
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  have hs := Equiv.sum_comp (flagEquiv (h := h))
    (fun u => (Tm * M * Ti : Matrix (Pr (h + 4)) (Pr (h + 4)) ℚ) u u)
  rw [hs]
  change (Tm * M * Ti).trace = M.trace
  rw [Matrix.trace_mul_cycle, Ti_Tm, Matrix.one_mul]

/-- Ported :389-395 (rank of an idempotent = trace; label-shape-agnostic). -/
lemma rank_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (q : Matrix ι ι ℚ)
    (hq : q * q = q) : (q.rank : ℚ) = q.trace := by
  have he : IsIdempotentElem (Matrix.toLin' q) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hq]
  have := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this, Matrix.rank, Matrix.toLin'_apply']

end Flag

section Gen

/-- Ported :458-461. -/
lemma runPairs_cons (a b r : ℕ) (rs : List (ℕ × ℕ × ℕ)) :
    runPairs ((a, b, r) :: rs) =
      (List.range r).map (fun k => (a + k, b + k)) ++ runPairs rs := by
  simp [runPairs]

/-- Ported :463. -/
lemma runPairs_nil : runPairs [] = [] := rfl

/-- Ported :465-466. -/
lemma nodup_run (a b r : ℕ) : ((List.range r).map fun k => (a + k, b + k)).Nodup :=
  (List.nodup_range).map fun k k' e => by simpa using congrArg Prod.fst e

/-- Ported :468-473. -/
lemma mem_run {a b r : ℕ} {x : ℕ × ℕ} :
    x ∈ (List.range r).map (fun k => (a + k, b + k)) ↔ ∃ k < r, x = (a + k, b + k) := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- Ported :475. -/
lemma length_run (a b r : ℕ) :
    ((List.range r).map (fun k => (a + k, b + k))).length = r := by simp

/-- Ported :450-456 (`edge_singles`), consuming the `Platform.edge_of_pivs` stub
(platform-Proved child f66c9619; at submission the stub sorry is replaced by the import —
its sorryAx is the ONLY sorryAx in data_edge_stair's footprint). -/
theorem edge_singles {m : ℕ} (hm : 1 < m) (q : Matrix (Fin m) (Fin m) ℚ) (hq : q * q = q)
    (rs : List (ℕ × ℕ × ℕ)) (hok : ∀ ρ ∈ rs, RunOK m ρ) (hnd : (runPairs rs).Nodup)
    (hp : ∀ x ∈ runPairs rs, IsPiv q x.1 x.2) :
    ∃ e : Edge m, EdgeQ e q ∧ ∃ rs', e.runs = rs ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs rs).length + rs'.length = q.rank := by
  obtain ⟨e, ⟨rs', h1, h2, h3⟩, h4, h5, h6, h7, h8, h9⟩ :=
    Platform.edge_of_pivs hm q hq rs hok hnd hp
  exact ⟨e, ⟨h4, h5, h6, h7, h8, h9⟩, rs', h1, h2, h3⟩

end Gen

end DEPort

/-- **N5-1** — `data_edge_stair`: the staircase data-entrance edge. Exact delta vs
data_edge_sol_aux (nb_data_edge_solution.lean:503-517): the pivot hyp is N2d's output (the
r6 proof obtained it from isPiv_mid + isPiv_rank1_lower; here isPiv_stair_lower supplies
both runs at once) and the conclusion is DataE' at h = 19. Assembly route (PROVED, this
file): idempotence + rank = 484 via the ported trace computation (:518-531 verbatim);
hok from N1's kernel-decided stairRunOK restricted to the run prefix; hnd HAND-PROVED via
the ported run toolkit (:575-583 pattern) and rs'.length = 6 from a kernel-decided
478 + 6 = 484 count — deliberately NOT consuming stairNodup/stair_pivot_budget, whose
native_decide would put Lean.ofReduceBool in the axiom footprint; hp := hpiv verbatim;
edge extraction via DEPort.edge_singles → Platform.edge_of_pivs (stub). -/
theorem data_edge_stair (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (h₁ : y₁ ⬝ᵥ x₁ = 1) (h₂ : y₂ ⬝ᵥ x₂ = 1)
    (hpiv : ∀ p ∈ runPairs (stairDataRuns 23 529),
      IsPiv (qM ((1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂))) p.1 p.2) :
    DataE' (qM ((1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂))) := by
  set M := (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂) with hMdef
  -- idempotence: Kronecker of two idempotents (body :522-524, verbatim)
  have hMM : M * M = M := by
    rw [hMdef, ← mul_kronecker_mul, DEPort.one_sub_vmv_idem x₁ y₁ h₁,
      DEPort.one_sub_vmv_idem x₂ y₂ h₂]
  have hq := DEPort.qM_idem hMM
  -- rank via trace (body :525-531, verbatim; concrete n = 23, h = 19)
  have hrank : (qM M).rank = 484 := by
    have h1 := DEPort.rank_eq_trace (qM M) hq
    rw [DEPort.qM_trace, hMdef, trace_kronecker, DEPort.trace_one_sub_vmv x₁ y₁ h₁,
      DEPort.trace_one_sub_vmv x₂ y₂ h₂] at h1
    apply Nat.cast_injective (R := ℚ); rw [h1]; norm_num
  -- hok: N1's stairRunOK (kernel `decide`, axiom-clean) restricted to the run prefix
  have hok : ∀ ρ ∈ stairDataRuns 23 529, RunOK 529 ρ := fun ρ hρ =>
    stairRunOK ρ (List.mem_append.2 (Or.inl hρ))
  -- hnd: hand proof, the body's :575-583 pattern on the three extracted runs
  -- (45,45,439) diagonal / (1,507,21) / (25,486,18); disjointness is omega on the offsets
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
  -- hp: the N2d hypothesis, verbatim
  have hpM : ∀ p ∈ runPairs (stairDataRuns 23 529), IsPiv (qM M) p.1 p.2 := hpiv
  obtain ⟨e, he, rs', hruns, hsing, hlen⟩ :=
    DEPort.edge_singles (m := 529) (by omega) (qM M) hq _ hok hnd hpM
  -- rs'.length = 6: 478 run positions (kernel-decided length count) + 6 = 484 = rank
  have hl : (runPairs (stairDataRuns 23 529)).length = 478 := by
    unfold stairDataRuns stairCornerRuns runPairs
    decide
  have h6 : rs'.length = 6 := by
    rw [hrank, hl] at hlen
    omega
  show ∃ e : Edge 529, EdgeQ e (qM M) ∧ ∃ rs', e.runs = stairDataRuns 23 529 ++ rs' ∧
    (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 6
  exact ⟨e, he, rs', hruns, hsing, h6⟩

/-! ## N5-2 machinery: the staircase-frame corner factor

`flag_gen`'s Pall-product corner factor is `pDat` (Defs4:1497), built from the r6/Defs4 `cor`
frame. At the staircase witness that frame's 45x45 corner is SINGULAR (det = 0 exactly; rank 44;
`scratch_corner_check2.py` verifies det = 0 mod 2^31-1, 67108859, 1000003, 998244353, and the
same script reproduces Defs4's r6 `certRows` exactly at the r6 witness), whereas N3's
`stair_data_cert` above certifies the STAIRCASE frame (`corStairQ`) corner invertible. The corner
factor is therefore rebuilt in the staircase frame as `pDatStair`, mirroring `pDat`/`eval_pDat_of`/
`pDat_ne` (nb_flag_gen_solution.lean:812-857) with `cor` -> `corStairQ` and `pDat` -> `pDatStair`.
The r6 witness-factor lemmas (`map_kM`, `eval_det`) are ported in the N5-2 port section below. -/

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

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace N52

/-! ## PLATFORM STUBS (wave-3 follow-up: replace each by an import at submission)

The ported `flag_gen` body consumes three generic Proved platform children whose statements are
verbatim below, specialized to h = 19 (ids + fetched bodies committed in ref/):

| stub | platform theorem | id | fetched body |
|---|---|---|---|
| `aux_edge_of` | IntMul.Kappa.R6.Bit.NB.aux_edge_of | c973e50d-124a-489e-b0fd-ac3804a68d0b | ref/nb_aux_edge_of_solution.lean:561 |
| `side_edge_of` | IntMul.Kappa.R6.Bit.NB.side_edge_of | f2e5b569-5d59-4157-8761-498f52b51299 | ref/nb_side_edge_of_solution.lean:196 |
| `idem_similar` | IntMul.Kappa.R6.Bit.NB.idem_similar | be86910c-e063-49cb-8700-1d314cebf2de | ref/nb_idem_similar_solution.lean:52 |

Porting them is mechanical but pulls a further generic chain (`edge_exact`,
`isPiv_diag_of_lower`, `isPiv_block`, `isPiv_mid` — the last already a `Platform` stub in
Pivot.lean); the bodies are in ref/ so no re-fetch is needed.

`aux_edge_of`: the aux-class edge at a generic pair matrix `M` with the Bruhat corner shape. -/
theorem aux_edge_of (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) (hM : M * M = M)
    (htr : M.trace = ((19 + 4) * (19 + 3) : ℕ))
    (hlow : ∀ β γ : ℕ, β < γ → γ < 19 + 4 → cor M β (19 + 3 + γ) = 0)
    (hdiag : ∀ β : ℕ, β < 19 + 4 → cor M β (19 + 3 + β) ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM M) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  sorry

/-- `side_edge_of`: the side-class edge of rank `r` at a factorized pair matrix `C * A * R`. -/
theorem side_edge_of (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ)
    (hB : ∀ i j : Fin (19 + 4), i < j →
      (Te (h := 19) * C) ⟨i.val, by have := two_k_le (h := 19); omega⟩ j = 0)
    (hBd : ∀ i : Fin (19 + 4),
      (Te (h := 19) * C) ⟨i.val, by have := two_k_le (h := 19); omega⟩ i ≠ 0)
    (hA : ∀ i j : Fin (19 + 4), i < j → (R * Te' (h := 19)) i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + j.val, by have := two_k_le (h := 19); omega⟩ = 0)
    (hAd : ∀ i : Fin (19 + 4), (R * Te' (h := 19)) i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + i.val, by have := two_k_le (h := 19); omega⟩ ≠ 0)
    (hM : C * A * R * (C * A * R) = C * A * R) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hrM : (qM (C * A * R)).rank = r)
    (hcor : 19 + 4 < 2 * r →
      (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ :
          Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (C * A * R)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  sorry

/-- `idem_similar`: idempotents of equal rank are similar — PORTED verbatim from the platform
body (ref/nb_idem_similar_solution.lean, submission 92d6f177 of
IntMul.Kappa.R6.Bit.NB.idem_similar, Proved be86910c-e063-49cb-8700-1d314cebf2de); so this
platform child needs NO stub. -/
theorem h50i_conj {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (f g : E →ₗ[ℚ] E) (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (hr : Module.finrank ℚ (LinearMap.range f) = Module.finrank ℚ (LinearMap.range g)) :
    ∃ φ : E ≃ₗ[ℚ] E, φ.toLinearMap ∘ₗ f = g ∘ₗ φ.toLinearMap := by
  have hk : Module.finrank ℚ (LinearMap.ker f) = Module.finrank ℚ (LinearMap.ker g) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := LinearMap.finrank_range_add_finrank_ker g
    omega
  let e1 := LinearEquiv.ofFinrankEq _ _ hr
  let e2 := LinearEquiv.ofFinrankEq _ _ hk
  have cf := LinearMap.IsIdempotentElem.isCompl hf
  have cg := LinearMap.IsIdempotentElem.isCompl hg
  let PA := (LinearMap.range f).prodEquivOfIsCompl (LinearMap.ker f) cf
  let PB := (LinearMap.range g).prodEquivOfIsCompl (LinearMap.ker g) cg
  let φ : E ≃ₗ[ℚ] E := (PA.symm.trans (e1.prodCongr e2)).trans PB
  refine ⟨φ, ?_⟩
  have hfr : ∀ y : LinearMap.range f, f y = y := fun y => (LinearMap.IsIdempotentElem.mem_range_iff hf).mp y.2
  have hgr : ∀ y : LinearMap.range g, g y = y := fun y => (LinearMap.IsIdempotentElem.mem_range_iff hg).mp y.2
  have key : ∀ p : LinearMap.range f × LinearMap.ker f, φ (f (PA p)) = g (φ (PA p)) := by
    rintro ⟨r, k⟩
    have h1 : PA (r, k) = (r : E) + (k : E) := Submodule.coe_prodEquivOfIsCompl' _ _ cf _
    have h2 : f (PA (r, k)) = PA (r, 0) := by
      rw [h1, map_add, LinearMap.mem_ker.mp k.2, add_zero, hfr]
      rw [Submodule.coe_prodEquivOfIsCompl' _ _ cf]; simp
    have h3 : ∀ q, φ (PA q) = PB ((e1.prodCongr e2) q) := by
      intro q; simp [φ]
    rw [h2, h3, h3]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    simp only [PB, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero, map_add,
      LinearMap.mem_ker.mp (e2 k).2, hgr]
  ext x
  have := key (PA.symm x)
  simpa using this

variable {n : ℕ}

theorem idem_similar (A B : Matrix (Fin n) (Fin n) ℚ) (hA : A * A = A) (hB : B * B = B)
    (hr : A.rank = B.rank) : ∃ Q : Matrix (Fin n) (Fin n) ℚ, IsUnit Q.det ∧ Q * A = B * Q := by
  have hfA : IsIdempotentElem A.mulVecLin := by
    show A.mulVecLin * A.mulVecLin = A.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hA]
  have hfB : IsIdempotentElem B.mulVecLin := by
    show B.mulVecLin * B.mulVecLin = B.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hB]
  obtain ⟨φ, hφ⟩ := h50i_conj A.mulVecLin B.mulVecLin hfA hfB hr
  refine ⟨LinearMap.toMatrix' φ.toLinearMap, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := LinearMap.toMatrix' φ.symm.toLinearMap) ?_
    rw [← LinearMap.toMatrix'_comp]
    simp
  · have := congrArg LinearMap.toMatrix' hφ
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at this
    have eA : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    have eB : LinearMap.toMatrix' B.mulVecLin = B := LinearMap.toMatrix'_toLin' B
    rw [eA, eB] at this
    exact this

/-! ## The staircase-frame corner factor (`pDatStair`) -/

section
-- Source module: Solutions.R6BitNBFlag
/-!
# Round six, bit network: the flag basis

The edge projectors are `q = S X S⁻¹` with `X` a Kronecker product on pairs `Fin n × Fin n`
(`n = 19 + 4`), `S = Π T K`, `K = Uᵀ ⊗ Vᵀ`. Here `T` is a unipotent change of coordinates on pairs
and `Π` an ordering of the pairs (`flagEquiv`) such that the first `k = 2n - 1` rows of `Π T` are
the sparse vectors `λ_β, ν_δ` (`Lterms`) and the last `k` columns of `T⁻¹ Πᵀ` are `ω_ε, μ_γ`
(`Rterms`). Everything here is for a pair matrix `M` (later `M = K X K⁻¹`):
`qM M = (T M T⁻¹)` reordered by `flagEquiv`.
-/


open Matrix Finset

section Flag


lemma sum_sv_mul {n : ℕ} (l : List (ℚ × Pr n)) (f : Pr n → ℚ) :
    ∑ u, sv l u * f u = (l.map fun s => s.1 * f s.2).sum := by
  induction l with
  | nil => simp [sv]
  | cons s l ih =>
    simp only [sv, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    simp [ite_mul]

lemma sum_mul_sv {n : ℕ} (l : List (ℚ × Pr n)) (f : Pr n → ℚ) :
    ∑ u, f u * sv l u = (l.map fun s => f s.2 * s.1).sum := by
  rw [show (∑ u, f u * sv l u) = ∑ u, sv l u * f u from
    Finset.sum_congr rfl fun u _ => mul_comm _ _, sum_sv_mul]
  congr 1
  exact List.map_congr_left fun s _ => mul_comm _ _

lemma Nm_sq : (Nm : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) * Nm = 0 := by
  ext u w
  simp only [Matrix.mul_apply, Nm, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases h1 : u.1.val = 19 + 3 ∧ u.2.val < 19 + 3 ∧ v.1 = u.2 ∧ v.2.val = 19 + 3
  · rw [mul_eq_zero]; right
    rw [if_neg]
    rintro ⟨e1, -, -, -⟩
    have := h1.2.2.1
    rw [this] at e1; omega
  · rw [if_neg h1, zero_mul]

lemma Tm_Ti : (Tm : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) * Ti = 1 := by
  rw [Tm, Ti, sub_mul, one_mul, mul_add, mul_one, Nm_sq]; abel

lemma Ti_Tm : (Ti : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) * Tm = 1 := by
  rw [Tm, Ti, add_mul, one_mul, mul_sub, mul_one, Nm_sq]; abel

/-- Row `aL i` of `T` is `λ/ν_i`. -/
lemma Tm_row (i : ℕ) (hi : i < 2 * 19 + 7) (u : Pr (19 + 4)) : Tm (aL i) u = sv (Lterms i) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [Tm, Nm, Matrix.sub_apply, of_apply, Matrix.one_apply, aL, Lterms, sv]
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] <;>
    (try split_ifs) <;> simp only [Prod.ext_iff, Fin.ext_iff, true_and, and_true] at * <;>
    first | (exfalso; omega) | norm_num

/-- Column `bL j` of `T⁻¹` is `ω/μ_j`. -/
lemma Ti_col (j : ℕ) (hj : j < 2 * 19 + 7) (u : Pr (19 + 4)) : Ti u (bL j) = sv (Rterms j) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [Ti, Nm, Matrix.add_apply, of_apply, Matrix.one_apply, bL, Rterms, sv]
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] <;>
    (try split_ifs) <;> simp only [Prod.ext_iff, Fin.ext_iff, true_and, and_true] at * <;>
    first | (exfalso; omega) | norm_num

lemma flagEquiv_top (i : ℕ) (hi : i < 2 * 19 + 7) :
    flagEquiv ⟨i, by have := two_k_le (h := 19); omega⟩ = aL (h := 19) i :=
  (Classical.choose_spec (exists_flagEquiv (h := 19))).1 i hi

lemma flagEquiv_bot (j : ℕ) (hj : j < 2 * 19 + 7) :
    flagEquiv ⟨(19 + 4) * (19 + 4) - (2 * 19 + 7) + j, by have := two_k_le (h := 19); omega⟩ =
      bL (h := 19) j :=
  (Classical.choose_spec (exists_flagEquiv (h := 19))).2 j hj

lemma qM_mul (M M' : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) : qM M * qM M' = qM (M * M') := by
  unfold qM
  rw [submatrix_mul_equiv]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ti Tm (M' * Ti), Ti_Tm, Matrix.one_mul]

lemma qM_idem {M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ} (hM : M * M = M) : qM M * qM M = qM M := by
  rw [qM_mul, hM]

lemma qM_trace (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) : (qM M).trace = M.trace := by
  unfold qM
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  have hs := Equiv.sum_comp (flagEquiv (h := 19))
    (fun u => (Tm * M * Ti : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) u u)
  rw [hs]
  change (Tm * M * Ti).trace = M.trace
  rw [Matrix.trace_mul_cycle, Ti_Tm, Matrix.one_mul]

lemma qM_corner (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) (i j : ℕ) (hi : i < 2 * 19 + 7)
    (hj : j < 2 * 19 + 7) :
    qM M ⟨i, by have := two_k_le (h := 19); omega⟩
      ⟨(19 + 4) * (19 + 4) - (2 * 19 + 7) + j, by have := two_k_le (h := 19); omega⟩ = cor M i j := by
  unfold qM cor
  rw [submatrix_apply, flagEquiv_top i hi, flagEquiv_bot j hj, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Ti_col j hj, Tm_row i hi]
  rw [show (∑ x, (∑ u, sv (Lterms i) u * M u x) * sv (Rterms j) x) =
      ∑ x, ((Lterms i).map fun s => s.1 * M s.2 x).sum * sv (Rterms j) x from
    Finset.sum_congr rfl fun x _ => by rw [sum_sv_mul], sum_mul_sv]

end Flag


end

section
-- Source module: Solutions.R6BitNBClass
/-!
# Round six, bit network: Bruhat profiles of the edge classes (flag basis, ℚ)

For transformed label data (vectors `x, y` with `y ⬝ x = 1`, idempotents `π`) satisfying the
genericity conditions, the projectors `qM M` of the edge classes have the claimed pivots, hence
edges with the claimed runs (`edge_of_pivs`).
-/


open Matrix Finset
open scoped Kronecker

section Class


/-- The rank of an idempotent is its trace. -/
lemma rank_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (q : Matrix ι ι ℚ) (hq : q * q = q) :
    (q.rank : ℚ) = q.trace := by
  have he : IsIdempotentElem (Matrix.toLin' q) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hq]
  have := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this, Matrix.rank, Matrix.toLin'_apply']

section Aux

variable (x y : Fin (19 + 4) → ℚ)

lemma aux1_upper (β γ : ℕ) (hβγ : β < γ) (hγ : γ < 19 + 4) :
    cor (1 ⊗ₖ (1 - vecMulVec x y)) β (19 + 3 + γ) = 0 := by
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])
  · obtain rfl : γ = 19 + 3 := by omega
    (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])

lemma aux1_diag (β : ℕ) (hβ : β < 19 + 3) :
    cor (1 ⊗ₖ (1 - vecMulVec x y)) β (19 + 3 + β) =
      -(x ⟨β, by omega⟩ * y ⟨19 + 3, by omega⟩) := by
  (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])

lemma aux1_diag_last :
    cor (1 ⊗ₖ (1 - vecMulVec x y)) (19 + 3) (19 + 3 + (19 + 3)) =
      -(x ⟨0, by omega⟩ * y ⟨19 + 3, by omega⟩) := by
  (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])

lemma aux2_upper (β γ : ℕ) (hβγ : β < γ) (hγ : γ < 19 + 4) :
    cor ((1 - vecMulVec x y) ⊗ₖ 1) β (19 + 3 + γ) = 0 := by
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])
  · obtain rfl : γ = 19 + 3 := by omega
    (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])

lemma aux2_diag (β : ℕ) (hβ : β < 19 + 3) :
    cor ((1 - vecMulVec x y) ⊗ₖ 1) β (19 + 3 + β) =
      -(x ⟨β, by omega⟩ * y ⟨19 + 3, by omega⟩) := by
  (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])

lemma aux2_diag_last :
    cor ((1 - vecMulVec x y) ⊗ₖ 1) (19 + 3) (19 + 3 + (19 + 3)) =
      x ⟨0, by omega⟩ * y ⟨19 + 3, by omega⟩ := by
  (simp (disch := omega) only [cor, Lterms, Rterms, dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul, mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left])

end Aux

/-! ## Side edges: factorization through `Fin n` -/

section Side

lemma kron_vec1 (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (x y : Fin (19 + 4) → ℚ) :
    A ⊗ₖ vecMulVec x y = Cx x * A * Ry y := by
  ext ⟨u1, u2⟩ ⟨v1, v2⟩
  simp only [kronecker_apply, vecMulVec_apply, Matrix.mul_apply, Cx, Ry, of_apply, ite_mul,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma kron_vec2 (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (x y : Fin (19 + 4) → ℚ) :
    vecMulVec x y ⊗ₖ A = Cx2 x * A * Ry2 y := by
  ext ⟨u1, u2⟩ ⟨v1, v2⟩
  simp only [kronecker_apply, vecMulVec_apply, Matrix.mul_apply, Cx2, Ry2, of_apply, ite_mul,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma qM_eq (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) : qM M = Te (h := 19) * M * Te' (h := 19) := by
  unfold qM Te Te'
  rw [Matrix.submatrix_mul _ _ flagEquiv id flagEquiv Function.bijective_id,
    Matrix.submatrix_mul _ _ flagEquiv id id Function.bijective_id, submatrix_id_id]

lemma side_B (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ) (β : ℕ) (hβ : β < 2 * 19 + 7)
    (a : Fin (19 + 4)) :
    (Te (h := 19) * C) ⟨β, by have := two_k_le (h := 19); omega⟩ a =
      ((Lterms β).map fun s => s.1 * C s.2 a).sum := by
  simp only [Te, Matrix.mul_apply, Matrix.submatrix_apply, id, flagEquiv_top β hβ, Tm_row β hβ,
    sum_sv_mul]

lemma side_A (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ) (γ : ℕ) (hγ : γ < 19 + 4)
    (a : Fin (19 + 4)) :
    (R * Te' (h := 19)) a ⟨(19 + 4) * (19 + 4) - (19 + 4) + γ, by have := two_k_le (h := 19); omega⟩ =
      ((Rterms (19 + 3 + γ)).map fun t => R a t.2 * t.1).sum := by
  have e : (⟨(19 + 4) * (19 + 4) - (19 + 4) + γ, by have := two_k_le (h := 19); omega⟩ :
      Fin ((19 + 4) * (19 + 4))) =
      ⟨(19 + 4) * (19 + 4) - (2 * 19 + 7) + (19 + 3 + γ), by have := two_k_le (h := 19); omega⟩ := by
    ext; simp only; have := two_k_le (h := 19); omega
  simp only [Te', Matrix.mul_apply, Matrix.submatrix_apply, id, e, flagEquiv_bot _ (show 19 + 3 + γ < 2 * 19 + 7 by omega),
    Ti_col _ (show 19 + 3 + γ < 2 * 19 + 7 by omega), sum_mul_sv]

variable (x y : Fin (19 + 4) → ℚ)

lemma side1_B_upper (β : ℕ) (a : Fin (19 + 4)) (hβa : β < a.val) :
    ((Lterms β).map fun s => s.1 * Cx x s.2 a).sum = 0 := by
  have ha := a.isLt
  simp (disch := omega) only [Lterms, Cx, of_apply, dif_pos, dif_neg, if_pos, if_neg, Fin.ext_iff,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_zero, add_zero]

lemma side1_B_diag (β : Fin (19 + 4)) :
    ((Lterms β.val).map fun s => s.1 * Cx x s.2 β).sum =
      if β.val < 19 + 3 then x β else x ⟨0, by omega⟩ := by
  have hb := β.isLt
  rcases Nat.lt_or_ge β.val (19 + 3) with h1 | h1
  · simp (disch := omega) only [Lterms, Cx, of_apply, dif_pos, if_pos, if_true, Fin.ext_iff,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero, Fin.eta]
  · obtain ⟨b, hb'⟩ := β
    obtain rfl : b = 19 + 3 := by simp only at h1; omega
    simp (disch := omega) only [Lterms, Cx, of_apply, dif_pos, dif_neg, if_pos, if_neg, if_true,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero,
      lt_irrefl, not_false_eq_true, ite_true, ite_false, mul_zero, ↓reduceIte, ↓reduceDIte]

lemma side1_A_upper (γ : ℕ) (hγ : γ < 19 + 4) (a : Fin (19 + 4)) (haγ : a.val < γ) :
    ((Rterms (19 + 3 + γ)).map fun t => Ry y a t.2 * t.1).sum = 0 := by
  have ha := a.isLt
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [Rterms, Ry, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [Rterms, Ry, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte]

lemma side1_A_diag (γ : Fin (19 + 4)) :
    ((Rterms (19 + 3 + γ.val)).map fun t => Ry y γ t.2 * t.1).sum = y ⟨19 + 3, by omega⟩ := by
  have hg := γ.isLt
  rcases Nat.lt_or_ge γ.val (19 + 3) with h1 | h1
  · simp (disch := omega) only [Rterms, Ry, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      Nat.add_sub_cancel_left, mul_one, zero_add, ite_true, ↓reduceIte]
  · obtain ⟨b, hb'⟩ := γ
    obtain rfl : b = 19 + 3 := by simp only at h1; omega
    simp (disch := omega) only [Rterms, Ry, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      mul_one, ↓reduceIte, ↓reduceDIte, lt_irrefl, not_false_eq_true]

lemma side2_B_upper (β : ℕ) (a : Fin (19 + 4)) (hβa : β < a.val) :
    ((Lterms β).map fun s => s.1 * Cx2 x s.2 a).sum = 0 := by
  have ha := a.isLt
  simp (disch := omega) only [Lterms, Cx2, of_apply, dif_pos, dif_neg, if_pos, if_neg, Fin.ext_iff,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_zero, add_zero]

lemma side2_B_diag (β : Fin (19 + 4)) :
    ((Lterms β.val).map fun s => s.1 * Cx2 x s.2 β).sum =
      if β.val < 19 + 3 then x β else -x ⟨0, by omega⟩ := by
  have hb := β.isLt
  rcases Nat.lt_or_ge β.val (19 + 3) with h1 | h1
  · simp (disch := omega) only [Lterms, Cx2, of_apply, dif_pos, if_pos, if_true, Fin.ext_iff,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero, Fin.eta]
  · obtain ⟨b, hb'⟩ := β
    obtain rfl : b = 19 + 3 := by simp only at h1; omega
    simp (disch := omega) only [Lterms, Cx2, of_apply, dif_pos, dif_neg, if_pos, if_neg, if_true,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero,
      lt_irrefl, not_false_eq_true, ite_true, ite_false, mul_zero, ↓reduceIte, ↓reduceDIte,
      zero_add, neg_mul]

lemma side2_A_upper (γ : ℕ) (hγ : γ < 19 + 4) (a : Fin (19 + 4)) (haγ : a.val < γ) :
    ((Rterms (19 + 3 + γ)).map fun t => Ry2 y a t.2 * t.1).sum = 0 := by
  have ha := a.isLt
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [Rterms, Ry2, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [Rterms, Ry2, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      ite_true, ite_false, dite_true, dite_false, ↓reduceIte, ↓reduceDIte]

lemma side2_A_diag (γ : Fin (19 + 4)) :
    ((Rterms (19 + 3 + γ.val)).map fun t => Ry2 y γ t.2 * t.1).sum = y ⟨19 + 3, by omega⟩ := by
  have hg := γ.isLt
  rcases Nat.lt_or_ge γ.val (19 + 3) with h1 | h1
  · simp (disch := omega) only [Rterms, Ry2, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      Nat.add_sub_cancel_left, mul_one, zero_add, ite_true, ↓reduceIte]
  · obtain ⟨b, hb'⟩ := γ
    obtain rfl : b = 19 + 3 := by simp only at h1; omega
    simp (disch := omega) only [Rterms, Ry2, of_apply, dif_pos, dif_neg, if_pos, if_neg,
      Fin.ext_iff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_mul, add_zero,
      mul_one, ↓reduceIte, ↓reduceDIte, lt_irrefl, not_false_eq_true]

end Side

end Class


end

section
-- Source module: Solutions.R6BitNBEdges
/-!
# Round six, bit network: edges of the classes (over ℚ)

`EdgeQ e q`: valid runs, lower triangular `E₁, E₂` with nonzero diagonals, and frame
`E₁ σ E₂ = pswQ q`. For each class, under the genericity conditions on the transformed labels,
an edge with the claimed runs exists.
-/


open Matrix Finset
open scoped Kronecker

/-! ## Labels -/

section Lab

variable {n : ℕ} (x y : Fin n → ℚ)

lemma vmv_idem (hxy : y ⬝ᵥ x = 1) : vecMulVec x y * vecMulVec x y = vecMulVec x y := by
  rw [vecMulVec_mul_vecMulVec, hxy, one_smul]

lemma one_sub_vmv_idem (hxy : y ⬝ᵥ x = 1) :
    (1 - vecMulVec x y) * (1 - vecMulVec x y) = 1 - vecMulVec x y := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, vmv_idem x y hxy]; abel

lemma trace_one_sub_vmv (hxy : y ⬝ᵥ x = 1) : (1 - vecMulVec x y).trace = (n : ℚ) - 1 := by
  rw [trace_sub, trace_one, trace_vecMulVec, dotProduct_comm, hxy, Fintype.card_fin]

end Lab

/-! ## Aux edges -/

section Aux


theorem aux1_edge (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : y ⟨19 + 3, by omega⟩ ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (1 ⊗ₖ (1 - vecMulVec x y))) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  refine aux_edge_of _ ?_ ?_ (fun β γ h1 h2 => aux1_upper x y β γ h1 h2) ?_
  · rw [← mul_kronecker_mul, Matrix.one_mul, one_sub_vmv_idem x y hxy]
  · rw [trace_kronecker, trace_one, trace_one_sub_vmv x y hxy, Fintype.card_fin]; push_cast; ring
  · intro β hβ
    rcases Nat.lt_or_ge β (19 + 3) with h1 | h1
    · rw [aux1_diag x y β h1, neg_ne_zero]
      exact mul_ne_zero (hx ⟨β, by omega⟩ h1) hy
    · obtain rfl : β = 19 + 3 := by omega
      rw [aux1_diag_last, neg_ne_zero]
      exact mul_ne_zero (hx _ (by simp only; omega)) hy

theorem aux2_edge (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : y ⟨19 + 3, by omega⟩ ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM ((1 - vecMulVec x y) ⊗ₖ 1)) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  refine aux_edge_of _ ?_ ?_ (fun β γ h1 h2 => aux2_upper x y β γ h1 h2) ?_
  · rw [← mul_kronecker_mul, Matrix.one_mul, one_sub_vmv_idem x y hxy]
  · rw [trace_kronecker, trace_one, trace_one_sub_vmv x y hxy, Fintype.card_fin]; push_cast; ring
  · intro β hβ
    rcases Nat.lt_or_ge β (19 + 3) with h1 | h1
    · rw [aux2_diag x y β h1, neg_ne_zero]
      exact mul_ne_zero (hx ⟨β, by omega⟩ h1) hy
    · obtain rfl : β = 19 + 3 := by omega
      rw [aux2_diag_last]
      exact mul_ne_zero (hx _ (by simp only; omega)) hy

end Aux

/-! ## Side edges -/

section Side


lemma rank_kron_vmv (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hAA : A * A = A) (x y : Fin (19 + 4) → ℚ)
    (hxy : y ⬝ᵥ x = 1) (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) (hMM : M * M = M)
    (htr : M.trace = A.trace) : (qM M).rank = A.rank := by
  have h1 := rank_eq_trace (qM M) (qM_idem hMM)
  rw [qM_trace, htr, ← rank_eq_trace A hAA] at h1
  exact Nat.cast_injective h1

theorem side1_edge (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : y ⟨19 + 3, by omega⟩ ≠ 0)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hcor : 19 + 4 < 2 * r → (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ : Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (A ⊗ₖ vecMulVec x y)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  have hMM : A ⊗ₖ vecMulVec x y * (A ⊗ₖ vecMulVec x y) = A ⊗ₖ vecMulVec x y := by
    rw [← mul_kronecker_mul, hAA, vmv_idem x y hxy]
  have htr : (A ⊗ₖ vecMulVec x y).trace = A.trace := by
    rw [trace_kronecker, trace_vecMulVec, dotProduct_comm, hxy, mul_one]
  have hrM := rank_kron_vmv A hAA x y hxy _ hMM htr
  rw [kron_vec1] at hMM hrM ⊢
  refine side_edge_of _ A _ ?_ ?_ ?_ ?_ hMM hAA r hr (hrM.trans hr) hcor
  · intro i j hij
    rw [side_B _ _ (by omega)]
    exact side1_B_upper x i.val j hij
  · intro i
    rw [side_B _ _ (by omega), side1_B_diag]
    split_ifs with h1
    · exact hx i h1
    · exact hx _ (by simp only; omega)
  · intro i j hij
    rw [side_A _ _ j.isLt]
    exact side1_A_upper y j.val j.isLt i hij
  · intro i
    rw [side_A _ _ i.isLt, side1_A_diag]
    exact hy

theorem side2_edge (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : y ⟨19 + 3, by omega⟩ ≠ 0)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hcor : 19 + 4 < 2 * r → (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ : Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (vecMulVec x y ⊗ₖ A)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  have hMM : vecMulVec x y ⊗ₖ A * (vecMulVec x y ⊗ₖ A) = vecMulVec x y ⊗ₖ A := by
    rw [← mul_kronecker_mul, hAA, vmv_idem x y hxy]
  have htr : (vecMulVec x y ⊗ₖ A).trace = A.trace := by
    rw [trace_kronecker, trace_vecMulVec, dotProduct_comm, hxy, one_mul]
  have hrM := rank_kron_vmv A hAA x y hxy _ hMM htr
  rw [kron_vec2] at hMM hrM ⊢
  refine side_edge_of _ A _ ?_ ?_ ?_ ?_ hMM hAA r hr (hrM.trans hr) hcor
  · intro i j hij
    rw [side_B _ _ (by omega)]
    exact side2_B_upper x i.val j hij
  · intro i
    rw [side_B _ _ (by omega), side2_B_diag]
    split_ifs with h1
    · exact hx i h1
    · exact neg_ne_zero.2 (hx _ (by simp only; omega))
  · intro i j hij
    rw [side_A _ _ j.isLt]
    exact side2_A_upper y j.val j.isLt i hij
  · intro i
    rw [side_A _ _ i.isLt, side2_A_diag]
    exact hy

end Side

/-! ## Data entrance edges -/


end

section
-- Source module: Solutions.R6BitNBSim
/-!
# Round six, bit network: similarity of idempotents, explicit corner idempotent, transitivity

* `idem_similar`: idempotent matrices over `ℚ` of equal rank are similar.
* `eIdem n r`: an explicit idempotent of rank `r` whose top-right `(n-r)`-corner is the identity
  (for `n < 2r`).
* `conj_rank_one`: for `y ⬝ x = 1 = y' ⬝ x'` some invertible `Q` has `Q (x yᵀ) Q⁻¹ = x' y'ᵀ`.
-/


open Matrix Finset

section Sim

variable {n : ℕ}

/-- Idempotents of equal trace are similar. -/
theorem idem_similar_trace (A B : Matrix (Fin n) (Fin n) ℚ) (hA : A * A = A) (hB : B * B = B)
    (hr : A.trace = B.trace) : ∃ Q : Matrix (Fin n) (Fin n) ℚ, IsUnit Q.det ∧ Q * A = B * Q := by
  refine idem_similar A B hA hB ?_
  have h1 := rank_eq_trace A hA
  have h2 := rank_eq_trace B hB
  exact_mod_cast h1.trans (hr.trans h2.symm)

end Sim

section EIdem

variable {n r : ℕ}

lemma eIdem_mul (hr : n < 2 * r) : eIdem n r * eIdem n r = eIdem n r := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < n - r
  · rw [Finset.sum_eq_single ⟨r + i.val, by omega⟩]
    · simp only [eIdem, of_apply, hi, if_true]
      have : ¬ r + i.val < n - r := by omega
      simp only [this, if_false, if_true, one_mul]
      by_cases hj : j.val = r + i.val
      · have : j = ⟨r + i.val, by omega⟩ := Fin.ext hj
        simp [hj, this]
      · have : j ≠ ⟨r + i.val, by omega⟩ := fun e => hj (by rw [e])
        simp [hj, this]
    · intro b _ hb
      simp only [eIdem, of_apply, hi, if_true]
      have : ¬ b.val = r + i.val := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  · rw [Finset.sum_eq_single i]
    · simp only [eIdem, of_apply, hi, if_false, if_true, one_mul]
    · intro b _ hb
      simp [eIdem, hi, hb]
    · simp

lemma eIdem_trace (hr : n < 2 * r) (hrn : r ≤ n) : (eIdem n r).trace = r := by
  rw [Matrix.trace]
  have : ∀ i : Fin n, Matrix.diag (eIdem n r) i = if i.val < n - r then 0 else 1 := by
    intro i
    simp only [Matrix.diag, eIdem, of_apply]
    by_cases h1 : i.val < n - r
    · rw [if_pos h1, if_pos h1, if_neg (by omega : ¬ i.val = r + i.val)]
    · rw [if_neg h1, if_neg h1]; simp
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < n - r then (0 : ℚ) else 1) n]
  rw [show Finset.range n = Finset.range ((n - r) + r) by congr 1; omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_range] at hi; simp [hi])]
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [if_neg (by omega : ¬ (n - r + i < n - r))])]
  simp

lemma eIdem_corner (l c : Fin (n - r)) (hrn : r ≤ n) :
    eIdem n r ⟨l.val, by omega⟩ ⟨n - (n - r) + c.val, by omega⟩ = if l = c then 1 else 0 := by
  simp only [eIdem, of_apply, l.2, if_true]
  by_cases e : l = c
  · subst e; simp only [if_true]; rw [if_pos (by omega)]
  · rw [if_neg e, if_neg]; intro hh; exact e (Fin.ext (by omega))

lemma eIdem_corner_det (hrn : r ≤ n) :
    ((eIdem n r).submatrix (fun l : Fin (n - r) => (⟨l.val, by omega⟩ : Fin n))
      (fun c : Fin (n - r) => (⟨n - (n - r) + c.val, by omega⟩ : Fin n))).det ≠ 0 := by
  have : (eIdem n r).submatrix (fun l : Fin (n - r) => (⟨l.val, by omega⟩ : Fin n))
      (fun c : Fin (n - r) => (⟨n - (n - r) + c.val, by omega⟩ : Fin n)) = 1 := by
    ext l c
    rw [submatrix_apply, eIdem_corner l c hrn, Matrix.one_apply]
  rw [this, det_one]; exact one_ne_zero

end EIdem


end

section
-- Source module: Solutions.R6BitNBGen
/-!
# Round six, bit network: genericity of the flag basis

Polynomials in the entries of two generic matrices `U, V` (`MvPolynomial (Bool × Fin n × Fin n) ℚ`)
encode the genericity conditions through the scaled conjugate `sconj W A = Wᵀ A adj(W)ᵀ`
(`= det W • Wᵀ A W⁻ᵀ`). Each condition polynomial is nonzero (witness via `idem_similar`), so a
rational point avoids all of them (`exists_eval_ne`).
-/


open Matrix Finset MvPolynomial
open scoped Kronecker

section Poly

variable {n : ℕ}

lemma Uf_pt (U V : Matrix (Fin n) (Fin n) ℚ) : Uf (ptUV U V) = U := by ext; simp [Uf, ptUV]
lemma Vf_pt (U V : Matrix (Fin n) (Fin n) ℚ) : Vf (ptUV U V) = V := by ext; simp [Vf, ptUV]

lemma map_XU (f : Vr n → ℚ) : (XU (n := n)).map (eval f) = Uf f := by ext; simp [XU, Uf]
lemma map_XV (f : Vr n → ℚ) : (XV (n := n)).map (eval f) = Vf f := by ext; simp [XV, Vf]
lemma map_cm {ι κ : Type*} (f : Vr n → ℚ) (A : Matrix ι κ ℚ) : (cm (n := n) A).map (eval f) = A := by
  ext; simp [cm]

lemma eval_det {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Vr n → ℚ) (W : Matrix ι ι (Rp n)) :
    eval f W.det = (W.map (eval f)).det := by
  rw [RingHom.map_det]; rfl

lemma map_sconj {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (W A : Matrix (Fin n) (Fin n) S) : (sconj W A).map φ = sconj (W.map φ) (A.map φ) := by
  have ha := RingHom.map_adjugate φ W
  simp only [RingHom.mapMatrix_apply] at ha
  simp only [sconj, Matrix.map_mul, transpose_map, ha]

lemma adj_eq (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) : U.adjugate = U.det • U⁻¹ := by
  rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hU, one_smul]

lemma sconj_eq (U A : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) :
    sconj U A = U.det • (Uᵀ * A * U⁻¹ᵀ) := by
  rw [sconj, adj_eq U hU, transpose_smul, Matrix.mul_smul]

lemma det_sub_smul {k : ℕ} (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (f g : Fin k → Fin n) :
    ((c • M).submatrix f g).det = c ^ k * (M.submatrix f g).det := by
  rw [show (c • M).submatrix f g = c • M.submatrix f g from by ext; simp, det_smul, Fintype.card_fin]

/-- A rational point avoids a nonzero polynomial. -/
lemma exists_eval_ne (P : Rp n) (hP : P ≠ 0) : ∃ f, eval f P ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hP (MvPolynomial.funext fun f => by simp [hc f])

/-- Witness: idempotents of equal trace are scaled-conjugate. -/
lemma conj_wit (P P' : Matrix (Fin n) (Fin n) ℚ) (hP : P * P = P) (hP' : P' * P' = P')
    (htr : P.trace = P'.trace) : ∃ U : Matrix (Fin n) (Fin n) ℚ, U.det ≠ 0 ∧ sconj U P = U.det • P' := by
  obtain ⟨Q, hQ, hQP⟩ := idem_similar_trace P P' hP hP' htr
  refine ⟨Qᵀ, by rw [det_transpose]; exact hQ.ne_zero, ?_⟩
  rw [sconj, transpose_transpose, adjugate_transpose, transpose_transpose, hQP, Matrix.mul_assoc,
    mul_adjugate, det_transpose, Matrix.mul_smul, Matrix.mul_one]

end Poly

/-! ## Condition polynomials -/

section Conds

variable {n : ℕ}

lemma eval_pA_U (f : Vr n → ℚ) (P : Matrix (Fin n) (Fin n) ℚ) (β l : Fin n) :
    eval f (pA XU P β l) = sconj (Uf f) P β l := by
  have := congrArg (fun M => M β l) (map_sconj (eval f) XU (cm P))
  simp only [map_apply, map_XU, map_cm] at this
  exact this

lemma eval_pA_V (f : Vr n → ℚ) (P : Matrix (Fin n) (Fin n) ℚ) (β l : Fin n) :
    eval f (pA XV P β l) = sconj (Vf f) P β l := by
  have := congrArg (fun M => M β l) (map_sconj (eval f) XV (cm P))
  simp only [map_apply, map_XV, map_cm] at this
  exact this

lemma eval_pCor_U (f : Vr n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) (r : ℕ) :
    eval f (pCor XU A r) = ((sconj (Uf f) A).submatrix (fun l : Fin (n - r) => (⟨l.val, by omega⟩ : Fin n))
      (fun c : Fin (n - r) => (⟨n - (n - r) + c.val, by omega⟩ : Fin n))).det := by
  rw [pCor, eval_det]
  congr 1
  ext l c
  simp only [map_apply, submatrix_apply]
  have := congrArg (fun M => M ⟨l.val, by omega⟩ ⟨n - (n - r) + c.val, by omega⟩)
    (map_sconj (eval f) XU (cm A))
  simp only [map_apply, map_XU, map_cm] at this
  exact this

lemma eval_pCor_V (f : Vr n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) (r : ℕ) :
    eval f (pCor XV A r) = ((sconj (Vf f) A).submatrix (fun l : Fin (n - r) => (⟨l.val, by omega⟩ : Fin n))
      (fun c : Fin (n - r) => (⟨n - (n - r) + c.val, by omega⟩ : Fin n))).det := by
  rw [pCor, eval_det]
  congr 1
  ext l c
  simp only [map_apply, submatrix_apply]
  have := congrArg (fun M => M ⟨l.val, by omega⟩ ⟨n - (n - r) + c.val, by omega⟩)
    (map_sconj (eval f) XV (cm A))
  simp only [map_apply, map_XV, map_cm] at this
  exact this

lemma eval_pT (f : Vr n → ℚ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℚ) (l e : Fin n) :
    eval f (pT P₁ P₂ l e) = sconj (Uf f) P₁ l e * (Vf f).det + sconj (Vf f) P₂ l e * (Uf f).det := by
  simp only [pT, map_add, map_mul, eval_pA_U, eval_pA_V, eval_det, map_XU, map_XV]

lemma eval_detU (f : Vr n → ℚ) : eval f (XU (n := n)).det = (Uf f).det := by rw [eval_det, map_XU]
lemma eval_detV (f : Vr n → ℚ) : eval f (XV (n := n)).det = (Vf f).det := by rw [eval_det, map_XV]

end Conds

/-! ## Witnesses -/

section Wit

variable {n : ℕ}

lemma wP_dot (hn : 0 < n) : (Pi.single (⟨n - 1, by omega⟩ : Fin n) (1 : ℚ)) ⬝ᵥ (fun _ => 1) = 1 := by
  simp [dotProduct, Pi.single_apply]

lemma wP_idem (hn : 0 < n) : wP n hn * wP n hn = wP n hn := vmv_idem _ _ (wP_dot hn)

lemma wP_trace (hn : 0 < n) : (wP n hn).trace = 1 := by
  rw [wP, trace_vecMulVec, dotProduct_comm, wP_dot hn]

lemma wP_apply (hn : 0 < n) (β : Fin n) : wP n hn β ⟨n - 1, by omega⟩ = 1 := by
  simp [wP, vecMulVec_apply]

lemma lab_trace (x y : Fin n → ℚ) (hxy : y ⬝ᵥ x = 1) : (vecMulVec x y).trace = 1 := by
  rw [trace_vecMulVec, dotProduct_comm, hxy]

lemma pA_U_ne (hn : 0 < n) (P : Matrix (Fin n) (Fin n) ℚ) (hP : P * P = P) (htr : P.trace = 1)
    (β : Fin n) : pA XU P β ⟨n - 1, by omega⟩ ≠ 0 := by
  obtain ⟨U, hU, hc⟩ := conj_wit P (wP n hn) hP (wP_idem hn) (htr.trans (wP_trace hn).symm)
  intro h0
  have := congrArg (eval (ptUV U 1)) h0
  rw [eval_pA_U, Uf_pt, hc, map_zero, Matrix.smul_apply, wP_apply, smul_eq_mul, mul_one] at this
  exact hU this

lemma pA_V_ne (hn : 0 < n) (P : Matrix (Fin n) (Fin n) ℚ) (hP : P * P = P) (htr : P.trace = 1)
    (β : Fin n) : pA XV P β ⟨n - 1, by omega⟩ ≠ 0 := by
  obtain ⟨U, hU, hc⟩ := conj_wit P (wP n hn) hP (wP_idem hn) (htr.trans (wP_trace hn).symm)
  intro h0
  have := congrArg (eval (ptUV 1 U)) h0
  rw [eval_pA_V, Vf_pt, hc, map_zero, Matrix.smul_apply, wP_apply, smul_eq_mul, mul_one] at this
  exact hU this

lemma detU_ne : (XU (n := n)).det ≠ 0 := by
  intro h0
  have := congrArg (eval (ptUV 1 1)) h0
  rw [eval_detU, Uf_pt, det_one, map_zero] at this
  exact one_ne_zero this

lemma detV_ne : (XV (n := n)).det ≠ 0 := by
  intro h0
  have := congrArg (eval (ptUV 1 1)) h0
  rw [eval_detV, Vf_pt, det_one, map_zero] at this
  exact one_ne_zero this

lemma pT_ne (hn : 0 < n) (P₁ P₂ : Matrix (Fin n) (Fin n) ℚ) (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (t₁ : P₁.trace = 1) (t₂ : P₂.trace = 1) (l : Fin n) : pT P₁ P₂ l ⟨n - 1, by omega⟩ ≠ 0 := by
  obtain ⟨U, hU, hc⟩ := conj_wit P₁ (wP n hn) h₁ (wP_idem hn) (t₁.trans (wP_trace hn).symm)
  obtain ⟨V, hV, hd⟩ := conj_wit P₂ (wP n hn) h₂ (wP_idem hn) (t₂.trans (wP_trace hn).symm)
  intro h0
  have := congrArg (eval (ptUV U V)) h0
  rw [eval_pT, Uf_pt, Vf_pt, hc, hd, map_zero, Matrix.smul_apply, Matrix.smul_apply, wP_apply, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one, mul_comm V.det, ← two_mul] at this
  exact mul_ne_zero two_ne_zero (mul_ne_zero hU hV) this

lemma pCor_U_ne (A : Matrix (Fin n) (Fin n) ℚ) (hA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (h2r : n < 2 * r) : pCor XU A r ≠ 0 := by
  have hrn : r ≤ n := hr ▸ (Matrix.rank_le_card_width A).trans (by simp)
  have htr : A.trace = (eIdem n r).trace := by
    rw [eIdem_trace h2r hrn, ← rank_eq_trace A hA, hr]
  obtain ⟨U, hU, hc⟩ := conj_wit A (eIdem n r) hA (eIdem_mul h2r) htr
  intro h0
  have := congrArg (eval (ptUV U 1)) h0
  rw [eval_pCor_U, Uf_pt, hc, map_zero, det_sub_smul] at this
  exact mul_ne_zero (pow_ne_zero _ hU) (eIdem_corner_det hrn) this

lemma pCor_V_ne (A : Matrix (Fin n) (Fin n) ℚ) (hA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (h2r : n < 2 * r) : pCor XV A r ≠ 0 := by
  have hrn : r ≤ n := hr ▸ (Matrix.rank_le_card_width A).trans (by simp)
  have htr : A.trace = (eIdem n r).trace := by
    rw [eIdem_trace h2r hrn, ← rank_eq_trace A hA, hr]
  obtain ⟨U, hU, hc⟩ := conj_wit A (eIdem n r) hA (eIdem_mul h2r) htr
  intro h0
  have := congrArg (eval (ptUV 1 U)) h0
  rw [eval_pCor_V, Vf_pt, hc, map_zero, det_sub_smul] at this
  exact mul_ne_zero (pow_ne_zero _ hU) (eIdem_corner_det hrn) this

end Wit


end

section
-- Source module: Solutions.R6BitNBMain
/-!
# Round six, bit network: the flag basis (main theorem of part (c))

`flagBasis`: for any finite set of labels `(x, y)` (`y ⬝ x = 1`) and any finite set of
idempotents, at `19 = 23` (`n = 23`, `m = 529`) there is one rational basis change `S`
(`S * Sinv = 1 = Sinv * S`) in which every edge of every class has the claimed Bruhat runs:
* aux `1 ⊗ (1 - x yᵀ)`, `(1 - x yᵀ) ⊗ 1`: exactly `[(0, m-n, n), (n, n, m-2n)]`;
* side `A ⊗ x yᵀ`, `x yᵀ ⊗ A`: `sideRuns n m (rank A)` plus singletons, total `rank A` pivots;
* data `(1 - x₁ y₁ᵀ) ⊗ (1 - x₂ y₂ᵀ)`: `dataRuns n m` plus `n + 1` singletons.
-/


open Matrix Finset MvPolynomial
open scoped Kronecker

section Data


lemma map_kM (f : Vr (19 + 4) → ℚ) (P₁ P₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    (kM P₁ P₂).map (eval f) =
      ((Uf f).det • 1 - sconj (Uf f) P₁) ⊗ₖ ((Vf f).det • 1 - sconj (Vf f) P₂) := by
  ext u v
  have e1 := eval_pA_U f P₁ u.1 v.1
  have e2 := eval_pA_V f P₂ u.2 v.2
  simp only [pA] at e1 e2
  simp only [kM, map_apply, kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, map_sub, eval_detU, eval_detV, e1, e2, Matrix.one_apply, apply_ite (eval f), map_one,
    map_zero]

/-- **The staircase-frame corner factor** — `pDat` (Defs4:1497) with the corner functional
`cor` (r6/Defs4 frame) replaced by the staircase frame `corStairR` (which at `R = ℚ` is
Cert.lean's `corStairQ`). This is the N5-2 substitution forced by the frame discovery: at the
staircase witness the r6-frame 45x45 corner is SINGULAR (det = 0, rank 44 — the r6 witness
reproduces Defs4's `certRows` exactly, so the implementation is validated; see
scratch_corner_check2.py), while the staircase-frame corner is invertible there (N3's
`stair_data_cert`, Cert.lean:213). Consumed by the Pall product below in place of `pDat`. -/
noncomputable def pDatStair (P₁ P₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) : Rp (19 + 4) :=
  (Matrix.of fun i j : Fin (2 * 19 + 7) => corStairR (kM P₁ P₂) i.val j.val).det

/-- Ported from `eval_pDat_of` (nb_flag_gen_solution.lean:823-844) with `cor` -> `corStairQ`
and the scalar pull-out done entrywise by `corStairR_smul` (Signature.lean) rather than through
the `Te`/`Te'` frame product. -/
lemma eval_pDatStair_of (f : Vr (19 + 4) → ℚ) (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h1 : sconj (Uf f) P₁ = (Uf f).det • W₁) (h2 : sconj (Vf f) P₂ = (Vf f).det • W₂) :
    eval f (pDatStair P₁ P₂) = ((Uf f).det * (Vf f).det) ^ (2 * 19 + 7) *
      (Matrix.of fun i j : Fin (2 * 19 + 7) =>
        corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val).det := by
  have key : (kM P₁ P₂).map (eval f) = ((Uf f).det * (Vf f).det) • ((1 - W₁) ⊗ₖ (1 - W₂)) := by
    rw [map_kM, h1, h2, ← smul_sub, ← smul_sub, smul_kronecker, kronecker_smul, smul_smul]
  rw [pDatStair, eval_det]
  have hmat : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairR (kM P₁ P₂) i.val j.val).map (eval f) =
      ((Uf f).det * (Vf f).det) •
        (Matrix.of fun i j : Fin (2 * 19 + 7) =>
          corStairR ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [eval_corStairR f (kM P₁ P₂) i.val j.val, key, corStairR_smul]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have hdet_eq : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairR ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val) =
      (Matrix.of fun i j : Fin (2 * 19 + 7) =>
        corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val) := by
    ext i j
    simp only [Matrix.of_apply, corStairR_rat]
  rw [hmat, det_smul, Fintype.card_fin, hdet_eq]

/-- Ported from `pDat_ne` (nb_flag_gen_solution.lean:846-857). The witness nonvanishing it
consumes is `hc`, in the staircase frame — instantiated by `stair_data_cert` (N3). -/
lemma pDatStair_ne (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂) (k₁ : W₁ * W₁ = W₁) (k₂ : W₂ * W₂ = W₂)
    (t₁ : P₁.trace = W₁.trace) (t₂ : P₂.trace = W₂.trace)
    (hc : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val).det ≠ 0) :
    pDatStair P₁ P₂ ≠ 0 := by
  obtain ⟨U, hU, e1⟩ := conj_wit P₁ W₁ h₁ k₁ t₁
  obtain ⟨V, hV, e2⟩ := conj_wit P₂ W₂ h₂ k₂ t₂
  intro h0
  have := congrArg (eval (ptUV U V)) h0
  rw [eval_pDatStair_of (ptUV U V) P₁ P₂ W₁ W₂ (by rw [Uf_pt]; exact e1)
    (by rw [Vf_pt]; exact e2), Uf_pt, Vf_pt, map_zero] at this
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hU hV)) hc this


end Data

/-! ## Conjugation algebra -/

section ConjAlg

variable {n : ℕ}

lemma conj_vmv (U : Matrix (Fin n) (Fin n) ℚ) (x y : Fin n → ℚ) :
    Uᵀ * vecMulVec x y * U⁻¹ᵀ = vecMulVec (Uᵀ *ᵥ x) (U⁻¹ *ᵥ y) := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

lemma conj_one (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) : Uᵀ * U⁻¹ᵀ = 1 := by
  rw [← transpose_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hU), transpose_one]

lemma conj_one' (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) : U⁻¹ᵀ * Uᵀ = 1 := by
  rw [← transpose_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hU), transpose_one]

lemma conj_dot (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) (x y : Fin n → ℚ) (hxy : y ⬝ᵥ x = 1) :
    (U⁻¹ *ᵥ y) ⬝ᵥ (Uᵀ *ᵥ x) = 1 := by
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hU),
    one_mulVec, hxy]

lemma conj_sub_vmv (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) (x y : Fin n → ℚ) :
    Uᵀ * (1 - vecMulVec x y) * U⁻¹ᵀ = 1 - vecMulVec (Uᵀ *ᵥ x) (U⁻¹ *ᵥ y) := by
  rw [mul_sub, sub_mul, Matrix.mul_one, conj_one U hU, conj_vmv]

lemma conj_idem (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A * A = A) : (Uᵀ * A * U⁻¹ᵀ) * (Uᵀ * A * U⁻¹ᵀ) = Uᵀ * A * U⁻¹ᵀ := by
  calc (Uᵀ * A * U⁻¹ᵀ) * (Uᵀ * A * U⁻¹ᵀ) = Uᵀ * A * (U⁻¹ᵀ * Uᵀ) * A * U⁻¹ᵀ := by
          simp only [Matrix.mul_assoc]
    _ = Uᵀ * A * U⁻¹ᵀ := by rw [conj_one' U hU, Matrix.mul_one, Matrix.mul_assoc Uᵀ A A, hA]

lemma conj_rank (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) (A : Matrix (Fin n) (Fin n) ℚ) :
    (Uᵀ * A * U⁻¹ᵀ).rank = A.rank := by
  have h1 : IsUnit Uᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.2 hU
  have h2 : IsUnit U⁻¹ᵀ.det := by
    rw [det_transpose, det_nonsing_inv]; exact (isUnit_iff_ne_zero.2 hU).ringInverse
  rw [rank_mul_eq_left_of_isUnit_det _ _ h2, rank_mul_eq_right_of_isUnit_det _ _ h1]

/-- Label facts from the scaled entry. -/
lemma lab_of_sconj (U : Matrix (Fin n) (Fin n) ℚ) (hU : U.det ≠ 0) (x y : Fin n → ℚ) (β l : Fin n)
    (hne : sconj U (vecMulVec x y) β l ≠ 0) : (Uᵀ *ᵥ x) β ≠ 0 ∧ (U⁻¹ *ᵥ y) l ≠ 0 := by
  rw [sconj_eq U _ hU, conj_vmv, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at hne
  exact ⟨fun h0 => hne (by rw [h0]; ring), fun h0 => hne (by rw [h0]; ring)⟩

end ConjAlg

/-! ## The frame -/

section Frame


lemma Te_Te' : Te (h := 19) * Te' (h := 19) = 1 := by
  have := qM_eq 1
  rw [Matrix.mul_one] at this
  rw [← this, qM, Matrix.mul_one, Tm_Ti, submatrix_one_equiv]

lemma Te'_Te : Te' (h := 19) * Te (h := 19) = 1 := by
  unfold Te Te'
  rw [submatrix_mul_equiv, Ti_Tm, submatrix_id_id]

lemma Sb_conj (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (A B : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    Sb U V * (A ⊗ₖ B) * Sbi U V = qM ((Uᵀ * A * U⁻¹ᵀ) ⊗ₖ (Vᵀ * B * V⁻¹ᵀ)) := by
  rw [qM_eq, mul_kronecker_mul, mul_kronecker_mul, Sb, Sbi, Kf, Kfi]
  simp only [Matrix.mul_assoc]

lemma Sb_inv (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hU : U.det ≠ 0) (hV : V.det ≠ 0) :
    Sb U V * Sbi U V = 1 ∧ Sbi U V * Sb U V = 1 := by
  have k1 : Kf U V * Kfi U V = 1 := by
    rw [Kf, Kfi, ← mul_kronecker_mul, conj_one U hU, conj_one V hV, one_kronecker_one]
  have k2 : Kfi U V * Kf U V = 1 := by
    rw [Kf, Kfi, ← mul_kronecker_mul, conj_one' U hU, conj_one' V hV, one_kronecker_one]
  constructor
  · rw [Sb, Sbi, Matrix.mul_assoc, ← Matrix.mul_assoc (Kf U V), k1, Matrix.one_mul, Te_Te']
  · rw [Sb, Sbi, Matrix.mul_assoc, ← Matrix.mul_assoc (Te' (h := 19)), Te'_Te, Matrix.one_mul, k2]

end Frame

/-! ## Main theorem -/

section Main


lemma lst_eq : lst 19 = ⟨19 + 3, by omega⟩ := Fin.ext (by simp [lst])

lemma corner_of_pCor (U A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hU : U.det ≠ 0) (r : ℕ)
    (hne : ((sconj U A).submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
      (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ : Fin (19 + 4)))).det ≠ 0) :
    ((Uᵀ * A * U⁻¹ᵀ).submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
      (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ : Fin (19 + 4)))).det ≠ 0 := by
  rw [sconj_eq U A hU, det_sub_smul] at hne
  exact right_ne_zero_of_mul hne

/-- **Flag basis (general `19`, given a data-corner certificate).** -/
theorem flag_gen_stair_aux (w₁ v₁ w₂ v₂ : Fin (19 + 4) → ℚ) (hw₁ : v₁ ⬝ᵥ w₁ = 1) (hw₂ : v₂ ⬝ᵥ w₂ = 1)
    (hcert : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairQ ((1 - vecMulVec w₁ v₁) ⊗ₖ (1 - vecMulVec w₂ v₂)) i.val j.val).det ≠ 0)
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
      (∀ p₁ ∈ Lab, ∀ p₂ ∈ Lab,
        DataE' (h := 19) (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv)) := by
  classical
  have hn : 0 < 19 + 4 := by omega
  let Pall : Rp (19 + 4) :=
    (XU (n := 19 + 4)).det * (XV (n := 19 + 4)).det *
      (∏ p ∈ Lab, ∏ β : Fin (19 + 4),
        (pA XU (vecMulVec p.1 p.2) β (lst 19) * pA XV (vecMulVec p.1 p.2) β (lst 19))) *
      (∏ A ∈ Pis.filter (fun A => 19 + 4 < 2 * A.rank),
        (pCor XU A A.rank * pCor XV A A.rank)) *
      (∏ q ∈ Lab ×ˢ Lab, (pDatStair (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2) *
        ∏ l : Fin (19 + 4), pT (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2) l (lst 19)))
  have hP : Pall ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero detU_ne detV_ne) ?_) ?_) ?_
    · refine prod_ne_zero_iff.2 fun p hp => prod_ne_zero_iff.2 fun β _ => mul_ne_zero ?_ ?_
      · exact pA_U_ne hn _ (vmv_idem _ _ (hLab p hp)) (lab_trace _ _ (hLab p hp)) β
      · exact pA_V_ne hn _ (vmv_idem _ _ (hLab p hp)) (lab_trace _ _ (hLab p hp)) β
    · refine prod_ne_zero_iff.2 fun A hA => ?_
      rw [Finset.mem_filter] at hA
      exact mul_ne_zero (pCor_U_ne A (hPis A hA.1) _ rfl hA.2) (pCor_V_ne A (hPis A hA.1) _ rfl hA.2)
    · refine prod_ne_zero_iff.2 fun q hq => ?_
      rw [Finset.mem_product] at hq
      have d1 := hLab _ hq.1
      have d2 := hLab _ hq.2
      refine mul_ne_zero ?_ (prod_ne_zero_iff.2 fun l _ => ?_)
      · exact pDatStair_ne _ _ _ _ (vmv_idem _ _ d1) (vmv_idem _ _ d2) (vmv_idem _ _ hw₁) (vmv_idem _ _ hw₂)
          ((lab_trace _ _ d1).trans (lab_trace _ _ hw₁).symm)
          ((lab_trace _ _ d2).trans (lab_trace _ _ hw₂).symm) hcert
      · exact pT_ne hn _ _ (vmv_idem _ _ d1) (vmv_idem _ _ d2) (lab_trace _ _ d1) (lab_trace _ _ d2) l
  obtain ⟨f, hf⟩ := exists_eval_ne Pall hP
  simp only [Pall, map_mul, map_prod, mul_ne_zero_iff, prod_ne_zero_iff, Finset.mem_univ,
    true_implies] at hf
  obtain ⟨⟨⟨⟨hdU, hdV⟩, hlab⟩, hpis⟩, hdat⟩ := hf
  rw [eval_detU] at hdU
  rw [eval_detV] at hdV
  set U := Uf f with hUdef
  set V := Vf f with hVdef
  -- label facts
  have labU : ∀ p ∈ Lab, (∀ β, (Uᵀ *ᵥ p.1) β ≠ 0) ∧ (U⁻¹ *ᵥ p.2) ⟨19 + 3, by omega⟩ ≠ 0 := by
    intro p hp
    have := fun β => lab_of_sconj U hdU p.1 p.2 β (lst 19) (by rw [← eval_pA_U]; exact (hlab p hp β).1)
    refine ⟨fun β => (this β).1, ?_⟩
    have := (this 0).2; rwa [lst_eq] at this
  have labV : ∀ p ∈ Lab, (∀ β, (Vᵀ *ᵥ p.1) β ≠ 0) ∧ (V⁻¹ *ᵥ p.2) ⟨19 + 3, by omega⟩ ≠ 0 := by
    intro p hp
    have := fun β => lab_of_sconj V hdV p.1 p.2 β (lst 19) (by rw [← eval_pA_V]; exact (hlab p hp β).2)
    refine ⟨fun β => (this β).1, ?_⟩
    have := (this 0).2; rwa [lst_eq] at this
  have one_c : ∀ W : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ, W.det ≠ 0 → Wᵀ * 1 * W⁻¹ᵀ = 1 :=
    fun W hW => by rw [Matrix.mul_one, conj_one W hW]
  refine ⟨Sb U V, Sbi U V, (Sb_inv U V hdU hdV).1, (Sb_inv U V hdU hdV).2, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hxU, hyU⟩ := labU p hp
    obtain ⟨hxV, hyV⟩ := labV p hp
    constructor
    · rw [Sb_conj, one_c U hdU, conj_sub_vmv V hdV]
      exact aux1_edge _ _ (conj_dot V hdV _ _ (hLab p hp)) (fun β _ => hxV β) hyV
    · rw [Sb_conj, one_c V hdV, conj_sub_vmv U hdU]
      exact aux2_edge _ _ (conj_dot U hdU _ _ (hLab p hp)) (fun β _ => hxU β) hyU
  · intro p hp A hA
    obtain ⟨hxU, hyU⟩ := labU p hp
    obtain ⟨hxV, hyV⟩ := labV p hp
    have hcorU : 19 + 4 < 2 * A.rank → _ := fun hr => corner_of_pCor U A hdU A.rank (by
      rw [← eval_pCor_U]; exact (hpis A (Finset.mem_filter.2 ⟨hA, hr⟩)).1)
    have hcorV : 19 + 4 < 2 * A.rank → _ := fun hr => corner_of_pCor V A hdV A.rank (by
      rw [← eval_pCor_V]; exact (hpis A (Finset.mem_filter.2 ⟨hA, hr⟩)).2)
    constructor
    · rw [Sb_conj, conj_vmv]
      exact side1_edge _ _ (conj_dot V hdV _ _ (hLab p hp)) (fun β _ => hxV β) hyV _
        (conj_idem U hdU A (hPis A hA)) A.rank (conj_rank U hdU A) hcorU
    · rw [Sb_conj, conj_vmv]
      exact side2_edge _ _ (conj_dot U hdU _ _ (hLab p hp)) (fun β _ => hxU β) hyU _
        (conj_idem V hdV A (hPis A hA)) A.rank (conj_rank V hdV A) hcorV
  · intro p₁ hp₁ p₂ hp₂
    obtain ⟨hx1, hy1⟩ := labU p₁ hp₁
    obtain ⟨hx2, hy2⟩ := labV p₂ hp₂
    have hq := hdat (p₁, p₂) (Finset.mem_product.2 ⟨hp₁, hp₂⟩)
    obtain ⟨hD, hT⟩ := hq
    rw [Sb_conj, conj_sub_vmv U hdU, conj_sub_vmv V hdV]
    -- N5-2 swap (fetched :1049): platform `data_edge` (r6 frame) -> `data_edge_stair`
    -- (N5-1, Signature.lean:197) whose pivot hypothesis is N2d `isPiv_stair_lower`
    -- (Pivot.lean:310). It needs the STAIRCASE-frame corner det, supplied below.
    have h₁' : (U⁻¹ *ᵥ p₁.2) ⬝ᵥ (Uᵀ *ᵥ p₁.1) = 1 := conj_dot U hdU _ _ (hLab _ hp₁)
    have h₂' : (V⁻¹ *ᵥ p₂.2) ⬝ᵥ (Vᵀ *ᵥ p₂.1) = 1 := conj_dot V hdV _ _ (hLab _ hp₂)
    refine data_edge_stair _ _ _ _ h₁' h₂'
      (isPiv_stair_lower _ _ _ _ h₁' h₂' (mul_ne_zero (hx1 _) (hx2 _)) (mul_ne_zero hy1 hy2) ?_ ?_)
    · intro l _ _
      have t := hT ⟨l, by omega⟩
      rw [eval_pT, ← hUdef, ← hVdef, sconj_eq U _ hdU, sconj_eq V _ hdV, conj_vmv, conj_vmv,
        Matrix.smul_apply, Matrix.smul_apply, vecMulVec_apply, vecMulVec_apply, smul_eq_mul,
        smul_eq_mul, lst_eq] at t
      intro h0
      apply t
      linear_combination (U.det * V.det) * h0
    · have t := hD
      rw [eval_pDatStair_of f _ _ _ _ (sconj_eq U _ hdU) (sconj_eq V _ hdV), ← hUdef,
        ← hVdef, conj_vmv, conj_vmv] at t
      exact right_ne_zero_of_mul t

end Main

end

end N52

/-- **N5-2** — `flagBasis_stair`: verbatim mirror of flagBasis_sol_aux
(nb_flagBasis_solution.lean:184-198) with the data clause `DataE (h := 19)` →
`DataE' (h := 19)` and the internal witness qx*/qy*/data_cert → stairQ*/stair_data_cert.
Upstream consumption (FB0_ex, accepted_bitNetR6_mom.lean:2289) keeps the SAME signature.
Route: flag_gen skeleton (generic, nb_flag_gen_solution.lean:956-971) + data_edge_stair +
stair_data_cert (N3) + stairQxy1/2 (N3-1/2). -/
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
  -- The r6 delegation (nb_flagBasis_solution.lean:198)
  --   `flag_gen (h := 19) qx1 qy1 qx2 qy2 qxy1 qxy2 data_cert Lab hLab Pis hPis`
  -- becomes the ported body with the staircase witness. The one hypothesis the port adds over
  -- the r6 body is `hcert`, supplied here by N3's kernel-checked `stair_data_cert`
  -- (Cert.lean:213) — the same role `data_cert` plays in the r6 body
  -- (nb_flagBasis_solution.lean:121-147).
  exact N52.flag_gen_stair_aux stairQX1 stairQY1 stairQX2 stairQY2 stairQxy1 stairQxy2
    stair_data_cert Lab hLab Pis hPis

end StaircasePort.Stair
