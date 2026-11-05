/-
# Top-level target: the r7 leaf, restated against the real QHNet definitions

formal_statement (platform e27d1a90-cfee-4b83-9b0b-b6c6f0ab652d, fetched verbatim to
/private/tmp/leaf-recon/formal_statement.lean):
  `theorem bitNetR7_mom : BitNetMomStmtG 108516254 529 Jain.bitR7 := by sorry`
`BitNetMomStmtG` (Def_IntMul_Kappa_RG_Defs.lean:31-34) unfolds to the ∃-statement below;
the unfolding is restated here directly against Defs4's QHNet (Defs4:212) because RG_Defs'
import closure (13 further R6 Defs files: Defs2/10-16/20-23) is out of this skeleton's
scope — the unfolded statement is verbatim the def body.

T = 3217907 (Data.lean stairT, RESOLVED from frozen witness data), W = 108516254
(Data.lean stairW), m = 529. The moment side is D3-trivial once C.hist = Jain.bitR7
(mirror-verified: producer hist == bitR7 all 37 entries, Σn_w = 1905413587, REPORT.md §ii;
stair_hist_target below pins the sum). Assembly pattern: r6's
`⟨3217907, net ch0, q₀, h1, h2, fun τ _ _ => (mom_eq τ).le⟩` (accepted_bitNetR6_mom.lean:3096).
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_KappaJainData
import StaircasePort.Data

namespace StaircasePort

open IntMul.Kappa

/-- The leaf goal, unfolded (BitNetMomStmtG, Def_IntMul_Kappa_RG_Defs.lean:31-34, verbatim
def body). Dependencies NOT in this skeleton: the QHNet construction of the staircase
witness-1 net itself (port task D2/dataset regen + net assembly, generic per REPORT.md D4)
and RunsOK/EdgesOK/FormalOK for it — EdgesOK via the generic edgesOK_large_of_edgeQ route
(Thm_net0Pnd_EdgesOK.lean:106, REPORT.md §6), FormalOK via flagBasis_stair (N5) + the
good_primes assembly. -/
theorem staircase_bitNetR7_mom :
    ∃ (T : ℕ) (C : IntMul.Kappa.R6.Bit.QHNet (ZMod 2) 108516254 T 529) (q₀ : ℕ),
      C.RunsOK ∧
      (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
        histMoment C.hist 529 τ ≤ histMoment Jain.bitR7 529 τ := by sorry

/-- Moment-side pin (D3): Σ n_w of Jain.bitR7 = 1905413587 — the value the producer mirror
recomputed exactly (producer_mirror_result.json / extract_T.py sum_nw), i.e. the net to be
constructed must have this child-call total; equality C.hist = Jain.bitR7 then discharges
the τ-bound by `.le` (r6 mom_eq pattern). -/
theorem stair_hist_target : (Jain.bitR7.map fun p => p.2).sum = 1905413587 := by native_decide

/-- Rank-sum pin: histRankSum Jain.bitR7 = 57403754177 (extract_T.py s; REPORT.md §ii). -/
theorem stair_ranksum_target : histRankSum Jain.bitR7 = 57403754177 := by native_decide

end StaircasePort
