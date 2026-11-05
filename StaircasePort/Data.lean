/-
# N1 — staircase data definitions: `stairDataRuns`, `stairSingles`, `DataE'`

The staircase entrance corner of witness-1 (PR#62 producer, Jain certificate_round7.py:26-33,
HEADLINE) replaces the round-6 corner runs `[h−2] ++ [1]*(h+1)` (deferred.py:152
ROUND6_CORNER) with `[h−2, h−5] ++ [1]*6` (deferred.py:153 STAIRCASE_CORNER), h = 23.

All offsets below are EXTRACTED, not guessed: extract/extract_staircase.py replicates
check_stair.py main() (h=23, seed=1, npairs=20) and dumps the dominant rightmost-pivot
pattern pc of the 45×45 corner; runs with offsets (corner coordinates (i,j,len)):
  [(0,44,1), (1,23,21), (22,22,1), (23,21,1), (24,20,1), (25,2,18), (43,1,1), (44,0,1)]
(extract/out/staircase_data.json, field runs_offsets). Global m=529 column = 484 + corner
column (484 = m − (2h−1) = m − 45, the corner block offset of nb_data_edge_solution.lean:533).
The 21-run sits at the SAME offset as r6's corner run (dataRuns second entry (1, m−n+1, n−2),
Defs4:1233-1234); the 18-run at corner (25,2) → global (25, 486) is new; r6's 24 singletons
(rs'.length = h+5 = 24, Defs4:1545-1548 DataE) become 6.

Rank budget: 439 + 21 + 18 + 6 = 484 = 529 − 45 = rank (qM M) (trace computation,
nb_data_edge_solution.lean:525-531 — label-shape-agnostic, reuses verbatim).
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData

namespace StaircasePort.Stair

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB

/-! ## N1: the staircase data runs -/

/-- The staircase corner runs (global m-coordinates). Extracted offsets
(extract/out/staircase_data.json dataRuns_prime[1:]): 21-run at corner (1,23) — same as r6's
(dataRuns 23 529 = [(45,45,439), (1,507,21)], Defs4:1233-1234) — and the NEW 18-run at
corner (25,2) → global (25, 486, 18). Generic form mirrors dataRuns: row n+2, column
m−2n+3, length n−5 (= h−5 of STAIRCASE_CORNER, deferred.py:153). -/
def stairCornerRuns (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(1, m - n + 1, n - 2), (n + 2, m - 2 * n + 3, n - 5)]

/-- The staircase data runs: the UNCHANGED middle-block run (45,45,439) = dataRuns first
entry (confirmed: isPiv_mid needs only k=45, rank 484, corner det ≠ 0 — positions (i,i),
i ∈ [45,483]; extract/out/staircase_data.json middle_run) plus the two corner runs. -/
def stairDataRuns (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  (2 * n - 1, 2 * n - 1, m - 2 * (2 * n - 1)) :: stairCornerRuns n m

/-- The 6 singleton positions of the extracted pivot pattern (corner coords (0,44),(22,22),
(23,21),(24,20),(43,1),(44,0) → global col 484+j). INFORMATIONAL: in `DataE'` the singleton
complement rs' is produced by edge_of_pivs with length forced to 6 by the rank count; these
concrete positions record where check_stair's rightmost_pivots places them. -/
def stairSingles (m : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(0, m - 1, 1), (22, m - 23, 1), (23, m - 24, 1), (24, m - 25, 1), (43, m - 44, 1),
   (44, m - 45, 1)]

/-- The 45×45-corner-local run list (corner coordinates, for the pivot statements of
StaircasePort.Pivot): two runs + six singletons, in pc order. -/
def stairCornerRuns45 : List (ℕ × ℕ × ℕ) :=
  [(1, 23, 21), (25, 2, 18), (0, 44, 1), (22, 22, 1), (23, 21, 1), (24, 20, 1), (43, 1, 1),
   (44, 0, 1)]

/-- **N1** — the staircase data-edge class: `DataE` (Defs4:1545-1548) with `dataRuns` →
`stairDataRuns` and `rs'.length = h + 5` (= 24) → `rs'.length = 6`. Source of the 6:
STAIRCASE_CORNER(23) = [21,18,1⁶] (deferred.py:153); 439+21+18+6 = 484 = rank. -/
def DataE' {h : ℕ} (q : Matrix (Fin ((h + 4) * (h + 4))) (Fin ((h + 4) * (h + 4))) ℚ) : Prop :=
  ∃ e : Edge ((h + 4) * (h + 4)), EdgeQ e q ∧ ∃ rs',
    e.runs = stairDataRuns (h + 4) ((h + 4) * (h + 4)) ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
    rs'.length = 6

/-! ## N1 computational pins (no sorry: these are extractions made checkable) -/

theorem stairDataRuns_eval : stairDataRuns 23 529 = [(45, 45, 439), (1, 507, 21), (25, 486, 18)] :=
  rfl

/-- The exact delta vs r6: the middle-block run and the 21-run are UNCHANGED; the staircase
adds the 18-run. (dataRuns def: Defs4:1233-1234.) -/
theorem stairDataRuns_delta : stairDataRuns 23 529 = dataRuns 23 529 ++ [(25, 486, 18)] := rfl

theorem stairSingles_eval :
    stairSingles 529 = [(0, 528, 1), (22, 506, 1), (23, 505, 1), (24, 504, 1), (43, 485, 1),
      (44, 484, 1)] := rfl

/-- Pivot budget: 439 + 21 + 18 = 478 run positions, + 6 singletons = 484 = rank (qM M) =
529 − 45 (nb_data_edge_solution.lean:521-531 hrank). -/
theorem stair_pivot_budget :
    (IntMul.Kappa.R6.Bit.NB.runPairs (stairDataRuns 23 529)).length + 6 = 529 - 45 := by
  native_decide

/-- RunOK for every run of the staircase data list (edge_singles hyp hok,
nb_data_edge_solution.lean:453-462 pattern). -/
theorem stairRunOK : ∀ ρ ∈ stairDataRuns 23 529 ++ stairSingles 529, RunOK 529 ρ := by
  intro ρ hρ
  simp only [stairDataRuns, stairCornerRuns, stairSingles, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hρ
  rcases hρ with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (unfold RunOK; decide)

/-- Nodup of the run positions (edge_singles hyp hnd, nb_data_edge_solution.lean:558-566
pattern) — the 478 run positions plus the 6 extracted singleton positions are pairwise
distinct, and disjoint from the middle-block diagonal (extract/out/staircase_data.json
middle_run.disjoint_from_corner_runs). -/
theorem stairNodup :
    (IntMul.Kappa.R6.Bit.NB.runPairs (stairDataRuns 23 529 ++ stairSingles 529)).Nodup := by
  native_decide

/-! ## T and W for witness-1 (extract/extract_T.py, extract/out/T_data.json) -/

/-- **T = 3217907 for staircase witness-1 — RESOLVED** (was inferred-not-verified in
REPORT.md). T = 46v + N under the r6 temporary-role addressing tmp₁(b,c)=23b+c,
tmp₂(a,c)=23v+23a+c, τ(a₁,a₂)=46v+a₁v+a₂ (accepted_bitNetR6_mom.lean:2126-2127
" T = 46 v + N = 3217907"); the R8 Oppbank port kept the same budget
(Def_IntMul_Kappa_R8_Data_BitOppbankConsts.lean:16,45 "same temporary budget as R6").
Witness-1 keeps h=23 (certificate_round7.py:27) hence v = C(23,3) = 1771, N = v² = 3136441
(extract_T.py, recomputed from frozen witness_23.json.gz/deferred_23.json.gz): only R
(28866 vs r6's 40077) and hence W change. CAVEAT (SCAFFOLD.md): the τ addressing lives in
the Lean QHNet construction, not the frozen JSON; final confirmation is the net definition
itself (port task D2/N5). -/
def stairT : ℕ := 3217907

theorem stairT_eq : stairT = 46 * 1771 + 1771 ^ 2 := rfl

/-- W = 108516254 = 2N + 2vR (deferred.py:187 Wd = 2N + 2A, A = vR; R = 28866 from
deferred_23.json.gz) — the leaf's role count (formal_statement.lean). -/
def stairW : ℕ := 108516254

theorem stairW_eq : stairW = 2 * 1771 ^ 2 + 2 * 1771 * 28866 := rfl

end StaircasePort.Stair
