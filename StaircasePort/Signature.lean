/-!
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
  sorry

end StaircasePort.Stair
