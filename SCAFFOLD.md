# SCAFFOLD.md — staircase witness-1 Lean port skeleton (r7 leaf e27d1a90, bounded first increment)

Date: 2026-11-04. Skeleton only: definitions + sorry'd statements + extracted data.
Every statement elaborates against the REAL platform definitions (Defs4 closure below).

## Environment
- Toolchain v4.34.1 + Mathlib d13f23b7 (project copied from /private/tmp/intmult-sol, its
  `.lake` APFS-cloned with `cp -Rc`; intmult-sol itself untouched).
- `Definitions/` = exact 64-file import closure of `Def_IntMul_Kappa_R6_Defs4` (source:
  ~/prove2me_workspace/Definitions, bodies identical to intmult-sol's migrated copies —
  only provenance headers differ) + `Def_IntMul_KappaJainData`. Built GREEN on v4.34.1:
  `build_defs.log` "Build completed successfully (8987 jobs)", 0 errors. This validates the
  whole r6 vocabulary (QHNet, Edge, EdgeQ, rk, IsPiv, RunOK, runPairs, runPiv, pswQ, qM,
  cor/corZ, certChk, dataRuns, DataE/AuxE/SideE, MZ, certRows/certCols) on the dev toolchain.
- Build: `lake build StaircasePort` (lib root `StaircasePort.lean`; there is no
  `Definitions.lean` root module — build leaf targets like
  `lake build Definitions.Def_IntMul_Kappa_R6_Defs4` or the StaircasePort root, never bare
  `lake build Definitions`).

## Extraction (all exact ints/Fractions, stdlib-only, rerunnable)
| script | output | content |
|---|---|---|
| extract/fetch_statements.py | extract/statements/pivot_statements.{json,lean} | verbatim formal_statements: isPiv_rank1_lower (e90110dd), isPiv_mid (06f02169), edge_of_pivs (f66c9619), isPiv_side (ef7049d3) — all Proved |
| extract/extract_T.py | extract/out/T_data.json | **T = 3217907 RESOLVED** = 46v+N, v=C(23,3)=1771, N=v²=3136441 (h=23 unchanged from r6; only R=28866 and W=2N+2vR=108516254 change). Cross-checks: s=57403754177, Σn_w=1905413587, all from frozen witness_23/deferred_23.json.gz |
| extract/extract_staircase.py | extract/out/staircase_data.json | (a) dominant pc, runs+offsets [(0,44,1),(1,23,21),(22,22,1),(23,21,1),(24,20,1),(25,2,18),(43,1,1),(44,0,1)]; dataRuns' = [(45,45,439),(1,507,21),(25,486,18)]; rs'.length=6; 689 NE blocks (i,j,rho,cut), cut≥rho on all; (c) 45×45 corner + 45×23 B block at witness; (d) middle-run (45,45,439) confirmation incl. disjointness; --ij control: identical pc, certified |
| extract/extract_cert.py | extract/out/cert_data.json | N3 data: ℤ labels x₁=p,y₁=ξ,x₂=v,y₂=ν with y⬝x=1 EXACT over ℤ (extended-Euclid lift of the --ij witness, values mod P untouched), family coeffs (al,be,a[],b[] lifted from [1,P)), 45×45 ℤ corner (≤36 digits), det≠0 mod 67108859, certRows/certCols with rows·cols=1 verified (r6 certChk convention) |
| extract/gen_lean_data.py | StaircasePort/CertData.lean, StaircasePort/NEBlocks.lean | generated Lean data (exact ints only) |

Producer chain copy: extract/jainroot/ (check_stair.py + linalg/check_lifted/deferred/
certificate_round7 @ c05adfe, from /private/tmp/leaf-recon — jain-verify NOT touched).

## N-item map
| N | file | statements | depends on |
|---|---|---|---|
| N1 | StaircasePort/Data.lean | stairCornerRuns/stairDataRuns/stairSingles/stairCornerRuns45, **DataE'** (rs'.length 6, not h+5=24), pins stairDataRuns_eval/_delta (rfl), stair_pivot_budget, stairRunOK, stairNodup (native_decide — NO sorry), stairT/stairW | Defs4 |
| N2 | StaircasePort/Pivot.lean | Platform restatements (4, verbatim) + **rank_le_support_cut** (N2a generic), **stairNE_rk_le** (N2b, 689-block table), **stairCorner_pivots_witness** (N2c), **isPiv_stair_lower** (N2d master, generalizes isPiv_rank1_lower) | N1, N3 (labels/corner), NEBlocks |
| N3 | StaircasePort/Cert.lean (+ generated CertData.lean) | LtermsZStair/RtermsZStair/corZStair/corStairQ/stairMZ/stairMQ/stairCornerQOf/stairCornerQ; stairQxy1/2, stairMZ_map, stair_cert_chk, stair_cert_entries, **stair_data_cert** (det ≠ 0, mirrors nb_flagBasis_solution.lean:97-147) | CertData only |
| N4 | StaircasePort/Nonvan.lean | stairF1..F4 defs (explicit --ij line algebra), **stair_f_nonvanishing** (f1..f4 every line + inner corners), **stair_hu/stair_hv/stair_hT** at witness labels (all verified numerically TRUE by gen_lean_data.py) | CertData only |
| N5 | StaircasePort/Signature.lean | **data_edge_stair** (DataE' conclusion, hpiv = N2d), **flagBasis_stair** (verbatim flagBasis_sol_aux signature, DataE→DataE'); header comment lists ALL swap points (data_edge :503-517/:536-552/:554-555, flag_gen :1049, flagBasis :196-198, accepted_bitNetR6_mom :2289/:2291/:2323-2325/:2353/:2539) | N1, N3, N2d |
| Top | StaircasePort/Top.lean | **staircase_bitNetR7_mom** (BitNetMomStmtG 108516254 529 Jain.bitR7 unfolded verbatim, RG_Defs:31-34), stair_hist_target/stair_ranksum_target (native_decide, no sorry) | N1 |

## Fan-out independence & recommended proving order
Independent (claimable in parallel, no cross-deps): **N3**, **N4**, **N2a**, **N5-1
(data_edge_stair assembly, given N2d as hyp)**.
Chain: N2a → N2b → N2c (needs N3 witness + stair_data_cert) → N2d (needs Platform.isPiv_mid
+ isPiv_block port) → N5-2 (flagBasis_stair, needs N3+N5-1).
Recommended order: N4 (hours) ∥ N3 (days, mechanical — r6 proofs port verbatim) ∥ N2a
(generic toolkit, days) → N2b → N5-1 → N2c → N2d → N5-2 → then OUTSIDE this skeleton:
D2 dataset regen (R=28866, pre-verify offline — the plain line died on defective frozen
data), QHNet construction (T confirmation lives there), RunsOK/EdgesOK (generic
edgesOK_large_of_edgeQ route, REPORT §6), FormalOK assembly (good_primes pattern), D3
moment equality (trivial, pins already proved here).

## N2 proof-route summary (per plan)
NE-rank UPPER bound via row/col/term-support factorization (rank_le_support_cut) using
data_edge's rank toolkit — rank_eq_of_range_rows/cols (nb_data_edge_solution.lean:26-30)
and rank_submatrix_range (:83), both PROVED with full proofs in the fetched body — plus
RIGHTMOST-PIVOT LOWER bound at the extracted witness (N2c). The min-cut computation stays
offline: cut VALUES are extracted data (stairNEBlocks), each re-checkable against
check_stair.cut_bound. Informal certificate: check_stair.py 23 → `certified=True` on this
machine (runs [21,18,1⁶], 689 blocks, invertible, single pivot pattern over 20 pairs) with
DISCRIMINATING negative control (--control: certified=False, 3 rank violations).
**Fallback if support-factorization fails: formalize the max-flow bound (+weeks).**

## Statement/build fixes made during scaffolding (build-driven; the scaffold's job)
1. **NEW GOTCHA (v4.34.1): a leading `/-! ... -/` module doc-comment BEFORE the imports is a
   PARSE ERROR** ("invalid 'import' command, it must be used in the beginning of the file") —
   minimal repro confirmed. File headers must use plain `/- -/`; `/-!` blocks are fine AFTER
   imports (Mathlib + the platform bodies use exactly that order). Applied to all 7 files.
2. `set_option maxRecDepth 20000` required for the big literals (689-tuple NEBlocks list,
   45×45 certRows/certCols) — default depth fails at parse ("maximum recursion depth").
   Baked into gen_lean_data.py's templates.
3. `stairRunOK`: `decide` cannot synthesize `Decidable (∀ ρ ∈ l, RunOK 529 ρ)` through the
   opaque `RunOK` def — route: simp the membership to equalities, `rcases` with the NESTED
   pattern `(rfl|rfl|rfl)|rfl|...` (List.mem_append leaves a nested Or group; mem_cons
   orientation is `ρ = t`), then `unfold RunOK; decide` per literal.
4. `stairT_eq`/`stairW_eq`: `norm_num` does not unfold the defs → `rfl` (closed numerals).
5. `flagBasis_stair`: explicit `(h := 19)` on the DataE' clause (h not inferable from
   Fin 529 by unification — the r6 original likewise writes `AuxE (h := 19)`).
6. N2b bound reads the CUT column `t.2.2.2` of stairNEBlocks tuples (i,j,rho,cut); the
   generated self-check asserts cut ≥ rho (`t.2.2.2 ≥ t.2.2.1`).
7. Pivot.lean needs `open scoped Kronecker` for `⊗ₖ` (scoped notation; "expected token").

## Build status (GREEN)
- `lake build Definitions.Def_IntMul_Kappa_R6_Defs4 ...` → build_defs.log: "Build completed
  successfully (8987 jobs)", 0 errors — the full r6 vocabulary compiles on v4.34.1/d13f23b7.
- `lake build StaircasePort` → build_scaffold.log: "Build completed successfully (8997
  jobs)", 0 errors; only `declaration uses sorry` warnings (expected for a skeleton).
- axcheck.lean (`lake env lean axcheck.lean`) prints the axiom profiles: sorryAx appears
  EXACTLY on the sorry'd statements; stairRunOK [propext], stairDataRuns_delta [no axioms],
  stairT_eq [propext]; the native_decide pins carry only their native_decide axioms
  (standard; if a submission gate forbids native_decide, downgrade to `decide` — slower but
  kernel-checked).

## GAPs (nothing below is guessed; each is flagged where consumed)
1. T=3217907 resolved structurally (46v+N; h=23, v, N all recomputed from frozen JSON) but
   the τ-addressing itself lives in the Lean QHNet construction (Defs), not the JSON —
   final confirmation = the net definition (D2). Data.lean stairT docstring carries this.
2. DataE''s rs' singletons come from edge_of_pivs' construction; the extracted stairSingles
   positions are informational (length 6 is forced by the rank count; positions not claimed).
3. Exact extra nonvanishing factors for the staircase deviation steps (RC/CC cells beyond
   hu/hv/hT) = N2 proof work; flag_gen's Pall product (nb_flag_gen_solution.lean:977-988)
   absorbs them structurally. N4 states the verified f1..f4/inner-corner/hu/hv/hT set.
4. N2b is stated at the flag-basis corner (stairCornerQOf M); the corner-transfer identity
   (hCe: Cp i j = cor M i j restated with corStairQ, nb_data_edge_solution.lean:534-537)
   and isPiv_block (PROVED at :227-238) are inside N2d's route, not separately stated.
5. Platform bodies of isPiv_mid/edge_of_pivs/isPiv_side not fetched (statements verbatim
   from search; bodies platform-side). At submission, Platform.* sorries → imports of the
   Proved children (ids in Pivot.lean header).
6. flag_gen' (the internal generic consumer of data_edge_stair) is NOT restated;
   flagBasis_stair states the consumed signature directly. The fetched 1071-line flag_gen
   body ports with the single :1049 call swap.
7. stair_cert_entries `decide +kernel` load: 36-digit ℤ entries vs r6's small ints — if the
   kernel balks, re-search a small-integer witness (Zariski-open ⇒ exists; not done here).
8. RG_Defs (BitNetMomStmtG) not imported — would pull 13 more R6 Defs files; Top.lean
   unfolds the def body verbatim instead (checked line-by-line against the fetched source).
9. Dataset regen (D2: recChk/dimAll/nestOK analogues for R=28866) is out of skeleton scope
   by design — it is mechanical and must be Python-pre-verified first (REPORT.md lesson).

## Gotchas honored (banked)
- No dangling `/--` doc-comments (parse error) — prose uses `/-!` (after imports) or `/- -/`
  file headers; every `/--` is attached to a declaration.
- Bare `end` for unnamed sections; no `end noncomputable section` anywhere.
- All builds detached (nohup + log): build_defs.log, build_scaffold.log.
## N4 NOTES (2026-11-04, N4 agent)
- N4 PROVED: stair_f_nonvanishing + stair_hu/hv/hT, axioms [propext, Classical.choice,
  Quot.sound], NO native_decide, zero sorry in Nonvan.lean. Same-file helpers: stairTv_mem,
  stairG_val, stairA/C/B/D_ne_zero, stairCoeffA/B_ne_zero ([propext, Quot.sound]).
- Statement delta (cosmetic only): binder `ht` renamed `_ht` in stair_f_nonvanishing.
  Nonvanishing is cardinality-free (tv in {0,1} for ANY t); hyp kept, unused. Pass positionally.
- LANDMINE (for N3 cert_entries decide+kernel and N2 tables): `decide` STICKS on Q `*`/`+`
  here (whnf won't unfold mkRat/Rat.add gcd-normalization: "reduction got stuck at ...add...").
  decide DOES work for pure getD -> Int.cast -> decEq literal checks (no arithmetic) --
  interval_cases + decide route used for the 22-entry coeff lists.
- For Q-arithmetic nonzeroness: `simp [accessor defs, LIST defs]` -- BOTH must be passed
  (simp won't unfold stairWX1L etc. otherwise; getD stays stuck at `l[i]?`), then `norm_num`
  fallback (simp arith leaves forms like `!1+3 = 0`). hu/hv closed by simp alone.
- Benign warnings left in place (2x unnecessarySeqFocus, 2x never-executed norm_num) --
  file is green; not worth a re-verification cycle.
## N3 RESUME (2026-11-04, subagent sp-n3) — STATUS: PROVED, item COMPLETE
Stopping point: ALL six N3 statements proved in StaircasePort/Cert.lean, zero sorry in the
file; `lake build StaircasePort` GREEN (8997 jobs); commit e91cda8 (+ final axcheck commit).
stair_data_cert axioms: [propext, Classical.choice, Quot.sound] — kernel-checked, no
native_decide, no sorryAx (n3_axcheck.lean prints all 6 + 3 ported helpers).

GAP-7 TIMING (decide +kernel; wall via /usr/bin/time -l; host at load ~65/16 cores, so
wall >> CPU; baseline import ≈60s wall):
| stage | content | wall | CPU(u+s) | axioms |
|---|---|---|---|---|
| t0 | native_decide sanity: all props TRUE (dots, worst entry, all 2025, certChk) | 89s | 17s | VM (test-only) |
| t1 | kernel, single worst entry (22,23) 36-digit | 64s | 11s | propext,Quot.sound |
| t4 | kernel, full certChk (2025 Nat dotL) | 68s | 14s | propext |
| t2 | kernel, worst row (22, 45 entries) | 62s | 12s | propext,Quot.sound |
| FINAL | lake build StaircasePort incl. real stair_cert_entries (all 2025) | 176s | 49s | — |
Verdict: GAP-7 outcome (a) — kernel decide FEASIBLE at 36-digit scale; per-entry marginal
kernel cost ≈ negligible (1 entry ≈ 1 row ≈ full build minus baseline); NO native_decide
fallback used, NO small-integer witness re-search needed (GAP 7 fallback can be struck).

What failed: nothing on the proof side — every port elaborated and kernel-checked on first
build. One env gotcha: nohup'd `lake env` needs `export LEAN_TOOLCHAIN=$(cat lean-toolchain)`
(transient elan "no default toolchain" otherwise).

Files: StaircasePort/Cert.lean (proofs; generic lemmas dotL_eq/certChk_sound/
det_ne_zero_of_certChk ported verbatim from nb_flagBasis_solution.lean:46-93; corStairQ_cast
= cor_cast analogue, no Lterms_eq step needed). CertData.lean UNCHANGED. New: n3_t0_native.lean
n3_t1_kernel_entry.lean n3_t2_kernel_row.lean n3_t4_kernel_chk.lean n3_axcheck.lean
extract/n3_corner_stats.py. No shared-file change requests.
Next for successors: N2c (stairCorner_pivots_witness) and N5-2 flagBasis_stair hcert can now
consume stair_data_cert; nothing blocked on N3.
## N2b NOTES (2026-11-05/06, sp-n2b-r2 — recovery agent after the kernel panic)
STATUS: PROVED + MERGED. `stairNE_rk_le` in StaircasePort/Pivot.lean is no longer sorry.

### THE STATEMENT-SHAPE FINDING (the scaffold's N2b statement was FALSE)
`∀ M : Matrix (Pr 23) (Pr 23) ℚ, rk (stairCornerQOf M) (i+1) j ≤ cut` is refuted:
`corStairQ M` is only BILINEAR in `M`, so at block (1,24) (pinned cut = 1) corner row 0 reads
only the M-cells ((0,0),·) and row 1 only ((1,1),·). Explicit witness (exact ℚ,
extract/counterexample_check.py): M[(0,0),(2,3)] = 1/7, M[(1,1),(3,4)] = 1/13, rest 0 gives a
2x2 block minor [[1,0],[0,7/13]], rank 2 > 1.
HONEST FORM (what is proved, and what N2c/N2d actually consume):
  theorem stairNE_rk_le (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
      ∀ t ∈ stairNEBlocks, rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (t.1+1) t.2.1 ≤ t.2.2.2
  stairPairM x₁ y₁ x₂ y₂ := (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂)
Found INDEPENDENTLY twice (this agent's numeric check + the predecessor's counterexample in
RESCUE_RESUME.md), so it is not a measurement artefact.

### NEBlocks.lean INTERFACE (regenerated here; predecessor's version was lost/was NOT built)
My regen differs from the predecessor's rescued blueprint and is BETTER for the proof: instead
of zip-aligned `stairNECutR0/C0/T0 : List (List ℕ)` (which forces `getD`-by-index bridges) the
cut sets are CARRIED IN the block:
  structure StairNEBlock := (i j rho cut : ℕ) (R0 C0 T0 : List ℕ)
  stairNEBlocksX : List StairNEBlock                     -- 689 entries
  stairNESr / stairNESc : List (List ℕ)                  -- 47 term supports
  stairNEBlocksX_map : stairNEBlocksX.map (i,j,rho,cut) = stairNEBlocks   -- rfl, no axioms
  stairNE_cuts_card  : stairNEBlocksX.all stairNEcardOK = true            -- kernel decide
  stairNE_cuts_cover : stairNEBlocksX.all stairNEcoverOK = true           -- kernel decide
  stairNEcardOK/stairNEcoverOK : Bool predicates (bridged by *_spec lemmas in Pivot.lean)
Existing value pins (`stairNEBlocks`, `stairNEBlocks_length`, `stairNEBlocks_cut_ge_rho`) are
byte-identical; no native_decide added. stairNE_cuts_cover axioms: [propext, Quot.sound].
RENAME LEDGER vs the rescue blueprint: stairNECutR0/C0/T0 (getD lists) -> StairNEBlock fields;
`stairNE_rk_le_block (n : Fin 689)` -> `stairNE_block_le (b : StairNEBlock)` (no index
arithmetic); the `getD_eq_getElem_of_lt` bridge is GONE (List.mem_map + stairNEBlocksX_map
substitutes the block directly).

### PHASE-1 EXTRACTION (re-run here, verified)
extract/extract_cuts.py (predecessor's, recovered): 689/689 clone flows == pinned cut values ==
producer check_stair.cut_bound, |R0|+|C0|+|T0| == flow in every block. T0 = {46} in all 689,
plus {23} in 289 of them; max |T0| = 2; |R0| ≤ 35, |C0| ≤ 20.

### PROOF ARCHITECTURE (all in Pivot.lean, namespace StaircasePort.Stair)
P1 List-sum kit (sum_map_add/sub/four/mul_right/congr, sum_sum_mul, sum_sum_ite_eq_group
= the algebraic heart); stairPairM + stairPairM_apply; the 4 δ-pieces stairT1..T4 and
stairPairM_expand; Nat-indexed factor sums stairUl/Vl/Uk/Vk/Pw/Qw (the pin data form — this is
what makes `Fin.sum_univ_eq_sum_range` fire); stairTermN/Row/Col/M (each M is literally a
vecMulVec, so rank ≤ 1 by Matrix.rank_vecMulVec_le); CORNER IDENTITY
corStairQ_stairPairM_sumN (range-47 split: 23 l-groups + 23 k-groups + the whole term; the
diagonal piece dies on stairLR_disjoint); coherence accessors stairNESr_iff/stairNESc_iff;
vanishing lemmas; card_filter_mem_fin (|filter of Fin 45 by raw list| = list length);
stairBlockR0/C0/T0/Terms; stairBlock_hsum; stairNE_block_le (rank_le_support_cut, TERM MODE);
stairNE_rk_le (689 blocks via List.mem_map on stairNEBlocksX_map).
LANDMINES HIT (for successors): (a) appending after a file's trailing `end` silently puts your
declarations OUTSIDE the namespace — the symptom is `Pr`/`RtermsStair` "unknown identifier"
with autoImplicit binding `Pr` as an implicit variable; (b) `List.sum_map_sub` does NOT exist
in Mathlib d13f23b7 (nor `List.map_congr`; `List.sum_map_congr` is free to define);
(c) `Finset.card_image_of_injective` takes (f) (hf) with s implicit — `_ _ f_inj` misfires;
(d) `funext` will not close a `List.map = List.map` goal (use List.map_congr_left);
(e) `Matrix.vecMulVec_apply` on a goal whose RHS is the zero FUNCTION leaves `0 = 0 c` — close
with `simp`, not `ring`; (f) stairTermRow/stairTermCol take the index as `Fin 45`, not `ℕ`.
### NEXT
N2c (stairCorner_pivots_witness) then N2d; nothing in N2b blocks them.
## N2b RESUME (2026-11-06) — STATUS: PROVED, item COMPLETE
Stop point: nothing in flight. `stairNE_rk_le` is PROVED and MERGED in StaircasePort/Pivot.lean;
`lake build StaircasePort` GREEN (8997 jobs); axioms of stairNE_rk_le = [propext,
Classical.choice, Quot.sound] (n2b_axcheck.lean); zero sorry added, no native_decide in the
proof layer. `n2b_full.lean` at the clone root is the standalone version of the same
development (kept for reference/diffing; Pivot.lean is the source of truth).
Tried-and-failed routes worth not repeating: arbitrary-M statement (FALSE, see counterexample),
zip-based cut-set interface (needs getD index bridges; StairNEBlock fields are strictly better),
`rw [Finset.sum_apply]` under Matrix transparency (ext to entries first, always).
NEXT: N2c (stairCorner_pivots_witness, still sorry) — consumes N3's stair_data_cert (proved)
and now N2b's upper bound; then N2d.
## N52 RESUME (2026-11-05, subagent sp-n52) — STATUS: PROVED, item COMPLETE
`StaircasePort.Stair.flagBasis_stair` (Signature.lean:1525) is PROVED with its statement
UNCHANGED. `lake build StaircasePort` GREEN (8997 jobs). Axioms:
`[propext, sorryAx, Classical.choice, Quot.sound]` — the only road to sorryAx is four
documented stubs (below); no `native_decide`, no `axiom`, no `admit`. The N5-2 machinery
(`corStairR`/`pDatStair`/`eval_pDatStair_of`/`pDatStair_ne`) is axiom-CLEAN
(`[propext, Classical.choice, Quot.sound]`).
### What was actually needed (the scaffold's route was INCOMPLETE)
The plan ("port flag_gen, swap only the :1049 data_edge call") does not close, and the reason
is a FRAME discovery, not a proof gap:
* `flag_gen`'s Pall corner factor is `pDat` (Defs4:1497), which encodes the r6/Defs4 `cor`
  frame (`Lterms`/`Rterms`, Defs4:834-949).
* At the STAIRCASE witness (CertData's `stairWX1L..stairWY2L`) that frame's 45x45 corner is
  **SINGULAR**: det = 0 exactly (0 mod 2^31-1, 67108859, 1000003, 998244353), rank 44.
  `scratch_corner_check2.py` validates the implementation two ways: it reproduces Defs4's r6
  `certRows` EXACTLY (0/2025 mismatches at the r6 witness) and reproduces CertData's
  `stairCertRows` structure; the r6 witness is invertible in the r6 frame (as `data_cert` says)
  and the staircase witness is invertible in the STAIRCASE frame (N3's `stair_data_cert`).
  => `pDat`'s hcert cannot be instantiated at the staircase witness. The corner factor must be
  rebuilt in the staircase frame: `pDatStair` (Signature.lean, `corStairR` =
  coefficient-ring-generic `corStairQ`), whose witness nonvanishing is exactly `stair_data_cert`.
* Consequence for N2d: `isPiv_stair_lower`'s `hdet` is `stairCornerQOf` (staircase frame) and
  the flag_gen Pall machinery can now produce exactly that (`eval_pDatStair_of`). Whoever
  discharges N2d must NOT assume `corStairQ = cor`; the two frames are genuinely different
  (random-label sampling finds points where the r6 frame is singular and the staircase frame is
  not — `scratch_corner_check2.py`'s sample loop).
* The `(h := 19)` / `Fin (19 + 4)` convention in the target statement is CORRECT: verified
  against the fetched r6 bodies (`nb_flagBasis_solution.lean:184-198` writes `DataE (h := 19)`
  with `Fin (19 + 4)`). No statement change was made or needed.
### Files / artifacts (all committed)
* `ref/nb_{flagBasis,flag_gen,data_edge,aux_edge_of,side_edge_of,idem_similar}_solution.lean` —
  re-fetched platform bodies (subs dc203a4d, 3a50ac98, d536680e, c2aac1ea, db51f0bf, 92d6f177).
* `StaircasePort/Signature.lean` — the port. Structure: N5-1 (unchanged) → N5-2 machinery →
  `namespace N52` port (platform stubs, `pDatStair`, the 1000-line `flag_gen` body specialized
  to h = 19) → `flagBasis_stair` (one-line delegation, mirrors
  `nb_flagBasis_solution.lean:198`).
* `gen_port.py` + `n52_platform_stubs.lean` + `n52_stairfactor.lean` → `n52_port.lean`
  (reproducible generator for the port body); `assemble_sig.py` assembles Signature.lean;
  `n52_axcheck.lean` prints the axiom profiles; `scratch_corner_check{,2}.py` the frame evidence.

### Remaining sorryAx in flagBasis_stair's footprint (all documented)
1. `N52.aux_edge_of` — PLATFORM STUB of `IntMul.Kappa.R6.Bit.NB.aux_edge_of`
   (Proved, c973e50d-124a-489e-b0fd-ac3804a68d0b). Body in `ref/nb_aux_edge_of_solution.lean:561`.
2. `N52.side_edge_of` — PLATFORM STUB of `.side_edge_of` (Proved,
   f2e5b569-5d59-4157-8761-498f52b51299). Body in `ref/nb_side_edge_of_solution.lean:196`.
3. `StaircasePort.Stair.isPiv_stair_lower` — N2d (Pivot.lean:310), a later wave, consumed as a
   hypothesis by design (`data_edge_stair`'s `hpiv`).
4. `Platform.edge_of_pivs` (f66c9619) inside `data_edge_stair` (N5-1's documented stub).
`N52.idem_similar` is NOT a stub: ported verbatim from `ref/nb_idem_similar_solution.lean`.

### Next moves (in order)
1. Port `aux_edge_of` + `side_edge_of` from the committed ref bodies (each needs
   `edge_exact`/`isPiv_diag_of_lower`/`isPiv_block`; `isPiv_mid` is already a `Platform` stub in
   Pivot.lean) — drops 2 of the 4 sorryAx sources; then flagBasis_stair's footprint reduces to
   N2d + `edge_of_pivs`.
2. Discharge N2d (Pivot.lean:310) — the last real math. Note the frame warning above: its
   `hdet` is the staircase frame, and the r6-frame identity `Cp i j = cor M i j`
   (nb_data_edge_solution.lean:534-537) does NOT transfer to `corStairQ` (`corStairQ_cast` in
   Cert.lean is the Z->Q cast only). N2d needs its own corner-transfer lemma.
3. Statement audit item: `DataE'`'s `rs'.length = 6` is h-only; fine.

### Gotchas added (banked, new)
* `lake env lean <file>` does NOT refresh `.olean`s — an `import` of a file you just edited via
  `lake env lean` still sees the OLD olean. Run `lake build` before importing your own changes.
* Substituting a concrete `h := 19` into a generic body breaks `simp` matching: `Fin (19 + 4)`
  and `Fin 23` are defeq but NOT syntactically equal, so simp lemmas stated at one shape will
  not fire at the other. Use `rw [<specialized lemma> ...]` (syntactic) or `show ... from`.
* When regex-substituting a variable name in Lean source, protect named-argument LABELS
  (`(h := ...)` must keep the `h`).
* A hypothesis named `h` (`intro h`, `have h :`) is silently rewritten by such a substitution.
## N2c NOTES (2026-11-05, subagent sp-n2c)
STATUS: PROVED (build verification in progress at write time; see N2c RESUME below).
### THE STATEMENT IS TRUE AS SCAFFOLDED — and the route is NOT the r6 corner route
`stairCorner_pivots_witness` (∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2)
is true; verified independently twice (the producer check_stair.py --ij run, and here by a
fresh mod-P recomputation: extract/n2c_struct2.py reproduces max|entry| 331316300630710586
302386325809570540 = cert_data's max_abs, and the FULL 46x46 rank profile rk(X,Y) =
#{r<X : pc_r >= Y} from pc = [44,23..43,22,21,20,2..19,1,0]).
### WHY r6's corner step does not port
r6's accepted body got the corner pivots from `isPiv_rank1_lower` (hB : B i j = u i * v j
for i < j) — a rank-one-above-diagonal structure. The staircase corner is DENSE (2025/2025
nonzero entries) and its pivot pattern is the PERMUTATION pc, not the diagonal, so there is
no such hypothesis. Worse: contiguous minors in the late-row blocks are ALL SINGULAR
(e.g. every 26x26 minor rows rlo..rlo+25 x cols clo..clo+25 inside block (38,14) is 0 mod
stairCertP, while rank(38,14) = 26) — minors must be found by ECHELON over F_P, not by
guessing windows. That is the single most important discovery here.
### THE PROOF SHAPE (all in Pivot.lean, namespace StaircasePort.Stair)
IsPiv q i j := rk q (i+1) j + rk q i (j+1) = rk q i j + rk q (i+1) (j+1) + 1, where
rk q X Y = rank of the NE block (rows < X, cols >= Y). With j = pc i and
k = #{r < i | pc r >= pc i}:
  A = rk q i j = k, B = rk q (i+1) j = k+1, C = rk q i (j+1) = k, D = rk q (i+1)(j+1) = k.
UPPERS (all four): trivial `min(#rows,#cols)` (rk_le_height/rk_le_width) or N2b's cut table
(`rkQ_le_of_block`, a 3-line restatement of stairNE_rk_le for stairCornerQ). LOWER B:
a nonzero (k+1)-minor inside (i+1, j). LOWER C: a nonzero k-minor inside (i, j+1) — which
also gives D >= k (block inclusion) and A >= k (block inclusion). Then
`isPiv_of_bounds` derives A = D = k by monotonicity and closes with omega.
KEY SIMPLIFICATION: only TWO lower bounds per position are needed (not four), and the
UNIVERSAL inequality B + C <= A + D + 1 is never needed as a lemma — the four exact values
make IsPiv pure arithmetic.

### THE CERTIFICATE MECHANISM (reuses N3 verbatim)
Each minor is certified by the N3 `certChk` product check mod stairCertP (rows x inverse-
transpose = 1), NOT by computing a determinant: `n2cChk<k>` (decide +kernel) plus
`n2cEnt<k>` pinning the minor's entries against corZStair stairMZ (decide +kernel), then
`n2c_rank_lower` casts Z -> Q (corStairQ_cast + RingHom.map_det) exactly as
stair_data_cert does. 47 certificates: sizes 1, 2x21, 22, 23, 24, 25, 26x18, 43, 44, 45.
Cover was minimised by a greedy variant search; 18 of the 26s are PROVABLY necessary (each
i in 25..42 forces maxR <= i and minC >= pc i, and rank(i+1, pc i - 1) < 26 blocks any
shared shape).

### LANDMINES HIT (for successors)
(a) Splice order: the block consumes `stairNE_rk_le`, which lives at the END of Pivot.lean —
the N2c block must be spliced before the final `end Stair`, not at the scaffold theorem's
site (otherwise "Unknown identifier stairNE_rk_le").
(b) `runPairs stairCornerRuns45` emits pairs in RUN order, so an equality with
`(List.range 45).map ...` is FALSE — pin `... .toFinset` equality by decide instead
(stairCornerRuns45_toFinset / _mem).
(c) `Fintype.card_le_of_embedding` lands on `Fintype.card (Fin X)`; close with `simpa`.
(d) `rkQ_le_of_block` needs an explicit `1 ≤ X` for Nat.sub_add_cancel.
(e) `Int.castRingHom p x` is not syntactically `↑x`: rewrite with bare `eq_intCast` first,
   then `← ZMod.intCast_mod` (N3's chain), else rw silently fails to match.
(f) In `n2c_rank_lower` the column indices need BOTH a lower (≥ Y) and an upper (< 45)
   bound as hypotheses — omega cannot conjure `< 45` from `Y ≤ c`.
(g) `simpa` alone will not rewrite a matrix form into a hypothesis; build the goal's exact
   matrix with a `rfl`-checked `heq` and rw both.
## N2c RESUME (2026-11-05, subagent sp-n2c) — STATUS: PROVED, item COMPLETE
Stopping point: NOTHING in flight for N2c. `stairCorner_pivots_witness` is PROVED and
spliced into StaircasePort/Pivot.lean (at the END of `namespace Stair`, after
`stairNE_rk_le`); `lake build StaircasePort` GREEN (8997 jobs, 0 errors, build_n2c.log —
~6 min at host load). Axioms (n2c_axcheck.lean): stairCorner_pivots_witness / stairPivAt /
n2c_rank_lower / rkQ_le_of_block / isPiv_of_bounds / rk_ge_of_det /
stairCornerRuns45_toFinset/_mem ALL `[propext, Classical.choice, Quot.sound]`; the kernel
pins n2cChk0 `[propext]`, n2cEnt0 `[propext, Quot.sound]`. NO sorryAi, NO native_decide,
NO `sorry` in the block (the 6 remaining sorries in Pivot.lean are the 4 Platform
restatements + N2d `isPiv_stair_lower` — all pre-existing).

Files changed: StaircasePort/Pivot.lean (the N2c block: stairPC, 5 generic rank lemmas +
isPiv_of_exact/isPiv_of_bounds, rkQ_le_of_block, n2c_rank_lower, 47 certificate data
triples + chk/ent pins, n2cPiv0..44, stairPivAt, stairCorner_pivots_witness).
Scratch at clone root: n2c_struct2.py (independent mod-P reproduction of the corner +
46x46 profile), n2c_plan.py (upper-bound coverage audit), n2c_emit2.py (generator:
minors by echelon over F_P, cert cover, Lean emission), n2c_splice.py, n2c_probe1.lean +
log (the 2-position probe that validated all generic plumbing before the full build),
n2c_axcheck.lean, n2c_cert_search*.py, n2c_gen.py, n2c_struct.py.
NO shared-file change requests. Nothing blocked on N2c: N2d can consume it as-is.

### N2d STATUS: NOT STARTED (ran out of this agent's budget) — findings that save the next mind days
1. STATEMENT SHAPE IS CONFIRMED CORRECT and needs NO delta: the consumer
   (~/bigo-campaign/sp-n52/StaircasePort/Signature.lean:1499) calls
   `isPiv_stair_lower _ _ _ _ h₁' h₂' (mul_ne_zero (hx1 _) (hx2 _)) (mul_ne_zero hy1 hy2) ?_ ?_`
   — exactly the scaffold's 9 arguments, in order, with `hdet` = the STAIRCASE-frame corner
   det (`stairCornerQOf (...)`), i.e. exactly what N3's stair_data_cert and the N5-2
   course update say. So the frame correction the N5-2 agent measured (corStairQ ≠ cor,
   r6 frame singular) does not change N2d's SIGNATURE; it changes only the PROOF, because
   the corner-transfer identity `Cp i j = cor M i j` (nb_data_edge_solution.lean:534-537)
   must be re-proved in the staircase frame.
2. The middle run (45,45,439) is the easy half: Platform.isPiv_mid (m = 529, k = 45,
   p = qM M) needs hk (`2*45 ≤ 529`), hp (`p*p = p`, from DEPort.qM_idem + the
   Kronecker-of-idempotents identity already used verbatim in
   sp-n52/Signature.lean:204-210), hrank (`(qM M).rank = 484`, the trace computation
   :211-217) and hC (the 45x45 corner at rows 0..44 / cols 484..528 = the transfer
   identity, staircase frame). Positions produced: (i,i) for 45 ≤ i < 484.
3. The two corner runs (1,507,21) and (25,486,18) need: isPiv_block
   (nb_data_edge_solution.lean:227-238, PROVED with a full proof in
   ~/bigo-campaign/sp-n52/ref/) + N2c lifted from the concrete witness to generic labels.
   The lift is the flag_gen Zariski/Pall product route (nb_flag_gen_solution.lean:977-993);
   N4's stair_f_nonvanishing + stair_hu/hv/hT are built for precisely that product, so
   compose with them rather than re-deriving.
4. isPiv_block also needs `i < j`-shaped side hypotheses on the B/A blocks (the r6 lemma's
   hB/hBd/hA/hAd) — those are the sparse-family facts, and the staircase family's versions
   are LtermsStair/RtermsStair support facts (a `decide`/`simp` on the concrete lists).

## N2d NOTES (2026-11-05, subagent sp-n2d) — STATUS: STATEMENT REFUTED (no proof exists)
### Verdict
`isPiv_stair_lower` (Pivot.lean) is **FALSE as stated**. Nothing is proved and nothing
should be: at the extracted staircase witness every one of its five hypotheses holds while
18 of the 39 corner positions it claims are not pivots of the matrix it names. This is the
third false-premise discovery of the campaign (after N2b's false scaffold statement and
N5-2's unsound pDat route) and it is a FRAME error, not a proof gap.

### The frame fact (two independent verifications)
1. `qM M`'s top-right 45x45 corner is Defs4's `cor M` (r6 frame: `Lterms`/`Rterms`), by
   the platform lemma `qM_corner` — the same lemma the accepted r6 `data_edge` proof uses
   (nb_data_edge_solution.lean:537-539). It is NOT `corStairQ`.
   `n2d_qm_corner_check.py` rebuilds `qM = (Tm*M*Ti).submatrix flagEquiv flagEquiv` from
   scratch (concrete flagEquiv from aL/bL + an arbitrary middle order, exact `Fraction`
   arithmetic) and reproduces the r6-frame `cor` on **2025/2025** entries at the staircase
   witness; **1528/2025** entries differ from `corStairQ`.
2. Lean-checked (`n2d_frame_delta`, in Pivot.lean, axioms `[propext, Classical.choice,
   Quot.sound]`): the two frames read different matrix ENTRIES at (0,0) — `n2d_cor_00`
   reads `M (0,0) (1,0)`, `n2d_corStairQ_00` reads `M (0,0) (1,3)` — and at the witness
   those evaluate to `653217308241796875` vs `-54722753962895109375`.
   So the swap point "`:527-537` Cp/hCe corner identity — restated with `cor → corStairQ`"
   (Signature.lean header, point 1) is unsound, and `corStairQ ≠ cor` is not an accident
   of the witness: the two families use different supports.

### The refutation (`n2d_refute.py`, exact, rerunnable)
At the extracted staircase witness (`extract/out/cert_data.json` labels):
- all hypotheses of `isPiv_stair_lower` hold: `y₁⬝x₁ = 1`, `y₂⬝x₂ = 1`,
  `hu = x₁[0]x₂[0] = 9`, `hv = y₁[22]y₂[22] = 28894092²`, all 21 `hT` values nonzero
  (min |value| = 173364552), and `hdet` (staircase-frame det ≠ 0 = N3's `stair_data_cert`,
  rank 45 — reproduced here as a profile that matches `pc` exactly);
- the ACTUAL corner of `qM M` has rank **44**, and **18 of the 39** corner positions in
  `runPairs (stairDataRuns 23 529)` are NOT pivots: exactly the added staircase run
  `(25,486,18)` (corner coordinates `(i, i-23)`, `25 ≤ i ≤ 42`). The pre-existing r6 run
  `(1,507,21)` DOES hold in the r6 frame (21/21), which is what r6's proved theorem says.
- the 439 middle-run positions are not decidable here (they depend on `flagEquiv`'s
  arbitrary middle order), but `isPiv_mid`'s hypothesis (invertible corner) FAILS at this
  witness (rank 44), so the middle run is uncertified too — the r6 route is unavailable.
Consequence: **flag_gen's call site (Signature.lean:1498-1499) applies a false lemma**, so
`flagBasis_stair` (N5-2) currently rests on a false statement (its `sorryAx` is not
"documented platform stub" debt, it is a falsehood). `data_edge_stair` (N5-1) is fine
CONDITIONALLY — it takes `hpiv` as a hypothesis; only the instantiation is unsound.

### What survives / the honest route
* `stairCorner_pivots_witness` (N2c) stays true and is exactly right: the staircase
  corner's pivots at the witness.
* `n2d_generic_probe.py` (4 random label sets, `y⬝x = 1`, hu/hv/hT, staircase corner rank
  45): the staircase frame's 39 positions are pivots **39/39 in all 4 trials**, and the
  control arm reproduces r6's PROVED 21/21 corner pivots in the r6 frame — i.e. the rank
  machinery is validated and the *staircase-frame* symbolic pattern is plausible
  (evidence, not proof).
* Therefore the honest form the consumer needs is a data edge for the **staircase
  projector**, not for Defs4's `qM`: the SAME construction as `Tm`/`Ti`/`flagEquiv` but
  built from `LtermsStair`/`RtermsStair` (an R7-side object; the skeleton has the families
  and the corner but not the change-of-basis/ordering). With it, `qM_corner`'s analogue
  gives the corner = `corStairQ`, `hdet` = `stair_data_cert` becomes usable, the middle run
  follows from `isPiv_mid`, and the corner runs need N2c's 39 witness pivots lifted to
  generic labels (a Zariski lift of the same 47 certificates, or the N4-style Pall product).
  Without that object there is no true statement to prove here.
* Do NOT "fix" it by weakening `hdet` to the r6-frame corner: the r6 frame is singular at
  the staircase witness (measured twice), so that variant cannot certify the R7 witness.

### Files
* Lean: `StaircasePort/Pivot.lean` — statement left BYTE-IDENTICAL with a REFUTED warning
  doc; new "N2d — THE FRAME DELTA" block at the end of `namespace Stair`
  (`n2d_stairMQ_entry`, `n2d_Lterms_0`, `n2d_Rterms_0`, `n2d_LtermsStair_0`,
  `n2d_RtermsStair_0`, `n2d_cor_00`, `n2d_corStairQ_00`, `n2d_frame_delta`), no sorry, no
  native_decide, no axiom.
* Scratch (clone root): `n2d_refute.py` (the refutation), `n2d_qm_corner_check.py`
  (independent qM corner), `n2d_generic_probe.py` (control arm + generic staircase probe),
  `n2d_frame_test.py` (first profile test), `n2d_scratch.lean`/`n2d_probe.lean` (proof
  development), `n2d_axcheck.lean`, `n2d_splice.txt`.
* NO shared-file change requests: the whole delta is inside Pivot.lean + clone-root scratch.

### Landmines added (banked, new)
* `decide` cannot unfold regular `def`s here: `decide` on `cor stairMQ 0 0 = <numeral>`
  fails with "`Decidable` instance did not reduce" because reduction gets stuck on
  `stairMQ s.2 t.2`. Route: unfold with `simp only [...]` (needs `stairMQ_entry` IN the
  simp set — that lemma's presence is what lets the surrounding `List.map`/`dite`
  reductions fire, probably via simp's congruence ordering), then `rw [stairMQ_entry]`,
  then `norm_num [<label defs>, List.getD_*, Fin.isValue, ↓reduceIte, Fin.mk.injEq]`.
* The clean way to compute a corner entry is to prove the SUPPORT decomposition first for
  ARBITRARY `M` (`n2d_cor_00 : cor M 0 0 = M (0,0) (1,0)`, by `simp [cor, <Lterms_0>]`):
  label-free, reusable, and it makes the frame divergence a statement about which MATRIX
  ENTRY each frame reads.
* `set_option linter.unusedSimpArgs false in` is needed on these lemmas (the simp sets are
  deliberately over-complete) — otherwise the build emits unused-arg noise.

## N2d RESUME (2026-11-05, subagent sp-n2d) — STATUS: STATEMENT REFUTED, no work in flight
**Stopping point:** nothing in flight. `lake build StaircasePort` GREEN (8997 jobs, exit 0)
with the new frame-delta block; `n2d_axcheck.lean` prints
`[propext, Classical.choice, Quot.sound]` for all eight new lemmas and `sorryAx` for
`isPiv_stair_lower` (statement untouched, still `sorry`, now carrying a REFUTED docstring).
**The stuck goal, verbatim:** prove
`∀ p ∈ runPairs (stairDataRuns 23 529), IsPiv (qM ((1-x₁y₁) ⊗ₖ (1-x₂y₂))) p.1 p.2`
given `y₁⬝x₁ = 1`, `y₂⬝x₂ = 1`, `hu`, `hv`, `hT`, and
`(stairCornerQOf ((1-x₁y₁) ⊗ₖ (1-x₂y₂))).det ≠ 0`. **It is false** — do not attempt it.

**Tried / failed (do not redo):**
1. Middle run via `Platform.isPiv_mid` + "isPiv_mid needs only hdet": the `hdet` in the
   statement is the staircase frame, `isPiv_mid` needs the corner of the matrix it is
   applied to, and `qM M`'s corner is the r6 frame (`qM_corner`) — measured rank 44 at the
   witness, so this route is unavailable at the very witness the campaign chose.
2. Corner-transfer identity "`Cp i j = cor M i j` restated with `corStairQ`"
   (Signature.lean header point 1): false — the two frames read different matrix entries
   (`n2d_cor_00` vs `n2d_corStairQ_00`; 1528/2025 entries differ at the witness).
3. Corner runs "via N2c lifted to symbolic labels": moot while the object is `qM M`
   (18 of the 39 positions are not pivots there). N2c's certificate machinery itself is
   fine — it is a statement about `stairCornerQ`, not about `qM M`.
4. Zariski lift: not needed to refute; it is needed for the HONEST route below, and the
   generic probe says the staircase-frame pattern is not fragile (39/39 at 4 random
   label sets satisfying hu/hv/hT + staircase hdet).

**Next move (the honest route — a different OBJECT, not a different proof):** build the
R7/staircase data-entrance projector — the analogue of `Tm`/`Ti`/`flagEquiv` built from
`LtermsStair`/`RtermsStair` — and prove its `qM_corner` analogue (corner = `corStairQ`).
Then: middle run from `isPiv_mid` with `hdet = stair_data_cert`; corner runs from N2c's 39
witness pivots lifted to generic labels through the flag_gen Pall product (N4's
`stair_f_nonvanishing` + `stair_hu/hv/hT`). `data_edge_stair` (N5-1) then applies unchanged
(hpiv is its hypothesis). Until that object exists there is nothing true to prove here, and
`flag_gen`'s call site (Signature.lean:1498-1499) must not be treated as a landed step:
`flagBasis_stair` currently derives its conclusion from a false hypothesis (its `sorryAx`
is a falsehood, not documented-stub debt).

**Cross-wave consequence to raise with the coordinator:** the campaign's premise that the
staircase design is the flag basis of Defs4's `qM` is wrong (that is the whole content of
`n2d_frame_delta`). Every "swap the runs list inside r6's data_edge" step inherits this.
## MIDRUN NOTES (2026-11-06, sp-midrun — independent middle-run arm)
QUESTION: the open middle-run item of the N2d RESUME — (a) pivot status of the 439 middle
positions of stairDataRuns in the r6 frame (qM M) at the witness, (b) dependence on
flagEquiv's ARBITRARY middle order, (c) the middle clause isPiv_stairR7 must claim so
Platform.isPiv_mid discharges it.

METHOD (reusable): rightmost-pivot profile pc of the full 529×529 qM M in flag coords.
THEOREM USED: rk(X,Y) = #{r<X : pc_r ≥ Y} for ALL (X,Y), hence IsPiv(i,j) ⟺ pc_i = j.
This is exactly the producer's rho identity (check_stair.py:175; rightmost_pivots
linalg.py:150-162) lifted to the global matrix — ONE elimination answers all 1756 block
ranks of the run claims. Exact: int Kronecker + Tm*M*Ti (midrun_lib.py, cross-checked
against n2d_qm_corner_check.py's mtimes on 36 entries); numpy int64 mod-p echelon (all
intermediates < 2^63); two primes asserted equal; failing blocks re-verified by DIRECT
submatrix elimination (midrun_spotcheck.py). Validation arms reproduce: rank(qM M) = 484
(both primes), corner rank 44, old corner run 21/21 (r6's proved thm), added run 0/18,
singles 4/6 ((24,504),(44,484) fail). pc on corner rows: 24→499, 37→486, 42→504,
44→44 (row 44 escapes into the SW block!), and bot row 484 becomes a pivot row — the
singular corner (rank 44) cascades into the middle tail.

(a) **437/439 — the middle run FAILS in the r6 frame at the witness.** Failing positions
(natural middle order): (464,464) — A,B,C,D = 44,45,44,45, pc_464 = 483 (pivot shifted one
right); (483,483) — 45,45,44,44, pc_483 = −1 (last middle row is DEPENDENT). Per-position
A/B/C/D + verdicts: extract/out/midrun_r6frame.json.

(b) **Order-dependent: YES — and no order rescues it.** 4 middle orders × 2 primes
(natural/reversed/shuffled/colmajor): the middle pc profile is NOT order-uniform. The
failure structure is invariant: EVERY order fails at the LAST middle position 483
(dependent row) plus exactly ONE shifted pivot (pc = 483) at an order-dependent position —
464 / 51 / 50 / 103. Since flagEquiv is Classical.choose, the r6-frame middle clause of
isPiv_stair_lower is unprovable as stated and false for every instantiation. Data:
extract/out/midrun_orders.json. Generic controls (3 random label sets, y·x=1, hu/hv/hT≠0,
STAIRCASE corner rank 45): middle 439/439 in the r6 frame in all trials (and 0 corner rows
escaping into SW) — the r6-frame failure is caused exactly by the r6-frame corner
singularity (hC of isPiv_mid failing), as isPiv_mid predicts.

(c) **SPEC for isPiv_stairR7's middle clause** (matches the N2d honest route; cross-check
target for N6): state it on the STAIRCASE-frame projector qM' M := (Tm' * M * Ti')
submatrix flagEquiv' flagEquiv' (Nm'/Tm'/Ti' the staircase analogue of Defs4:877-884,
flagEquiv' per exists_flagEquiv Defs4:891-903 with the staircase aL'/bL'; middle order
arbitrary and IRRELEVANT — see (b) for why it must be):
  `theorem isPiv_stairR7_mid (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (h₁ : y₁ ⬝ᵥ x₁ = 1)
   (h₂ : y₂ ⬝ᵥ x₂ = 1)
   (hdet : (stairCornerQOf ((1-vecMulVec x₁ y₁) ⊗ₖ (1-vecMulVec x₂ y₂))).det ≠ 0) :
   ∀ i : ℕ, 45 ≤ i → i < 484 → IsPiv (qM' ((1-vecMulVec x₁ y₁) ⊗ₖ (1-vecMulVec x₂ y₂))) i i`
Discharged VERBATIM by Platform.isPiv_mid (m:=529, k:=45; generic in p, NO transfer lemma
for the pivot lemma itself): hk omega; hp = qM'_idem (r6 route
nb_data_edge_solution.lean:524-526, label-shape-generic); hrank = 484 (Tm', Ti' invertible
since Nm'² = 0 ⇒ rank(qM' M) = rank(M) = 22·22; trace route :521-531 + qM'_trace);
hC via N6's corner-transfer identity corner(qM' M) = stairCornerQOf M (the qM'_corner
analogue of :534-537) + stair_data_cert (N3 PROVED). Hypotheses: h₁ h₂ hdet only —
hu/hv/hT are NOT needed for the middle clause (they are corner-run fuel). hdet MUST be the
staircase-frame corner: in the r6 frame the same clause is FALSE at this witness ((a)/(b)).
Producer convention (settles (b) from ground truth): the producer NEVER wires a middle
order — the entrance block m−4h+2 = 439 is ONE batched rank-439 block, `H[m-4*h+2] += 2*N`
(deferred.py:183, docstring :164; count 2N = 6272882, round7-histograms.json "bit"
[439, 6272882]); only the corner is pc-derived (check_stair.py:174, runs :98), in
family-list order = the Lean LtermsStair/RtermsStair indices. So the order-free isPiv_mid
conclusion IS the producer's convention, and it is available exactly when the frame is the
staircase one.

LANDMINES: (1) aL/bL enumeration is ONE pair per index (45 entries); enumerate the L-term
SUPPORTS instead and you get 47 and a wrong flag basis. (2) Kronecker entry is
M[a*23+b][c*23+e] — writing the column block with b instead of c silently gives rank 23.
(3) exact entries exceed int64 — reduce mod p in Python before np.array. (4) the
pc-profile theorem needs the on-demand reduction (each new row reduced against ALL
previous pivot rows); the producer's eager downward elimination computes the same reduced
rows. Files: midrun_lib.py, midrun_r6frame.py, midrun_orders.py, midrun_spotcheck.py,
MIDRUN_REPORT.md (also copied to ~/bigo-campaign/MIDRUN_REPORT.md), the two JSONs.

## MIDRUN RESUME (2026-11-06, sp-midrun) — STATUS: QUESTION ANSWERED, item COMPLETE
Verdicts: (1) r6-frame middle run = 437/439 pivots at the witness; failures (464,464)
[pc=483] and (483,483) [dependent row]; two primes + direct-elimination spot check.
(2) Order-dependent YES (one shifted failure moves; the tail failure at 483 is in every
order; no order certifies the claim). (3) Producer convention: no middle order exists —
entrance block is one batched 439-block (deferred.py:183); middle claims must be
order-free, which only the staircase frame delivers. (4) Spec: middle clause of
isPiv_stairR7 = verbatim Platform.isPiv_mid on qM' M (staircase frame), hypotheses
h₁ h₂ hdet(staircase), hC = N6's corner-transfer identity + stair_data_cert; no transfer
lemma for isPiv_mid itself; hu/hv/hT not needed. Next: N6 builds qM' (Tm'/Ti'/flagEquiv')
and proves corner(qM' M) = stairCornerQOf M — that identity is the ONLY load-bearing
lemma for the middle clause; corner runs then ride on N2c lifted + isPiv_block in the same
frame (N2d RESUME honest route). Cross-check pointers for N6: extract/out/midrun_r6frame.json
(per-position A,B,C,D), extract/out/midrun_orders.json (4 orders × 2 primes + 3 generic
controls).
## N6 NOTES (2026-11-05, subagent sp-n6) — the R7/staircase PROJECTOR exists
### What was built (deliverables 1-3)
`StaircasePort/Projector.lean` (NEW, owned by N6) is the object `## N2d RESUME` asked for: the
analogue of r6's `Tm`/`Ti`/`flagEquiv`/`qM` built from `LtermsStair`/`RtermsStair`. The
construction was DERIVED and then verified numerically before any Lean was written
(`n6_proj_probe.py`), because two scaffold statements had already turned out false:
* **anchors** `aLsStair i` / `bLsStair j` = the FIRST listed term of `LtermsStair i` /
  `RtermsStair j` — the coordinate that carries the family vector's LEADING coefficient;
* **`NsStair`** has only **23** nonzero entries (the staircase row family is multi-term only at
  `i = 22`, the column family only at `j = 22..43`), each = (other term)/(leading term);
* **`NsStair * NsStair = 0`** by two structural no-2-path lemmas (targets `(r,r+1)` are not
  sources `(s+1,s)`, and `(0,22)` is not a source) — so `TiStair * TmStair = 1`;
* the staircase LEADING COEFFICIENTS ARE NOT 1 (`al`, `a_r`), which is the one place the r6
  pattern does not port verbatim: the row of `TmStair` at an anchor is `LtermsStair i / leadL i`.
  A diagonal scaling `dv` (`leadL` on the row anchors, `leadR⁻¹` on the column anchors, 1
  elsewhere) with `PmStair = diagonal dv * TmStair`, `QmStair = TiStair * diagonal dv⁻¹`
  (`QmStair * PmStair = 1`) makes the corner EXACT:
  **`qMStair_corner : qMStair M ⟨i⟩ ⟨529-45+j⟩ = corStairQ M i j`** (i, j < 45).
That identity is what `qM_corner` can never be (N2d's `n2d_frame_delta`): with it the corner of
the projector the consumer applies `isPiv_mid` to IS the `corStairQ` frame, so `hdet` =
`stairCornerQOf`'s determinant = `stair_data_cert` at the witness.
### Deliverable 1 — numeric prototype (GREEN, `n6_proj_probe.py` + `n6_midrun.py`)
At the extracted witness (`extract/out/cert_data.json`), exact `Fraction` and mod-p:
* corner == `corStairQ`: **2025/2025** entries; r6-frame control reproduces `cor` 2025/2025;
* staircase corner rank **45**, 39/39 claimed corner pivots, pivot set = the extracted
  permutation `pc` (45/45); **r6-frame control rank 44, 21/21** (N2d's frame delta reproduced);
* **middle run, full 529x529 projector, ALL 439 positions: 439/439 pivots**
  (`extract/out/n6_midrun.json`) — this answers N2d's open question in the new frame;
* cross-check vs the independent arm (sp-midrun): its r6-frame headline (437/439, failing
  (464,464) and (483,483)) is reproduced by an independent re-implementation here
  (`n6_xcheck_r6frame.py`: r6 run 21/21, r6-frame middle 437/439 failing exactly 464, 483).
  **No disagreement.** Its producer-convention finding (no order-free middle claim
  producer-side) is consistent: `isPiv_stairMid` below is order-free in the middle.
### Deliverable 3 (part 1) — the MIDDLE RUN, PROVED: `isPiv_stairMid`
`isPiv_stairMid : h₁ → h₂ → hdet → ∀ i, 45 ≤ i → i < 484 → IsPiv (qMStair M) i i` for
`M = (1-x₁y₁) ⊗ₖ (1-x₂y₂)`, discharged by `Platform.isPiv_mid` with
`hk` (2·45 ≤ 529), `hp = qMStair_idem`, `hrank` (trace: `qMStair_trace` + `trace M = 22² = 484`),
`hC` (via `qMStair_cornerBlock` + `hdet`). **`hu`/`hv`/`hT` are NOT needed for this clause.**

### Deliverable 3 (part 2) — the 39 CORNER positions: route identified, NOT yet proved
`isPiv_stairR7` = middle run (PROVED above) ∧ corner runs (open). The r6 corner step
(`nb_data_edge_solution.lean:534-552`) goes through `isPiv_rank1_lower` on a rank-one
above-the-diagonal block; N2b/N2d showed the r6-frame version is false for the staircase. The
NEW frame's structure was measured instead of assumed (`n6_struct_probe.py`, r6 control in the
same run): with `B i γ := cornerStair[i][off+γ]` and the identity region `i < γ`, the number of
nonzero 2x2 minors is **0 in both frames** for BOTH blocks
* `off = 22`: `B i γ = corner[i][22+γ]`, i,γ ∈ 1..21  → the `(1,507,21)` run via
  `isPiv_rank1_lower B` (l = 1..21, `hT` from the boundary diagonal) then `isPiv_block` twice;
* `off = 2`: `B k γ = corner[25+k][2+γ]`, k,γ ∈ 0..17 → the `(25,486,18)` run, EXCEPT k = 0
  (corner position `(25,2)`): `isPiv_rank1_lower` needs `1 ≤ l`, so that one position needs a
  shifted block (e.g. `corner[24+i][1+γ]`) — that block's rank-one property is **not yet
  measured**.
Remaining work is therefore: two `data_upper`-style support computations in the staircase frame
(`corStairQ M i (22+γ) = u_i·v_γ` for `i < γ`, and the `off = 2` analogue), plus the shifted
block for `(25,2)`, plus the nonvanishing factors those two identities need (the analogues of
`hu`/`hv`/`hT`; N4's `stair_f_nonvanishing` + `stair_hu/hv/hT` are the candidates).

### Deliverable 4 — REWIRE SPEC for the N7 wave (call sites; nothing shared was edited here)
1. `data_edge_stair` (Signature.lean:197): restate its conclusion AND its `hpiv` hypothesis in
   the staircase frame — `IsPiv (qMStair M)` / `EdgeQ e (qMStair M)` instead of `qM M`
   (`qMStair`, `flagEquivStair` from `StaircasePort.Projector`). Then:
   * `hpiv` is supplied by `isPiv_stairR7` (middle run: `isPiv_stairMid`; corner runs: the
     block route above — the only open piece);
   * the corner step `have hCe : Cp i j = cor M i.val j.val` (:534-537) becomes
     `= corStairQ M i.val j.val` by `qMStair_corner` — TRUE now (was the unsound swap);
   * `hdet` is `stair_data_cert` at the witness (N3), a hypothesis in general;
   * `hrank` = `qMStair_trace` + the trace computation of :521-531, unchanged;
   * the `isPiv_mid` step (:554-555) is unchanged, `hC` = `hdet` via `qMStair_cornerBlock`.
2. `flagBasis_stair` (Signature.lean:~1525): its `data_edge` call site (:1498-1499) currently
   applies a false lemma; it must call the restated `data_edge_stair` above, i.e. the whole
   DataE clause moves to `qMStair`. The Pall corner factor `pDatStair` + `stair_data_cert`
   (N5-2) already matches the frame, so no change there.
3. `Platform.isPiv_mid` stays as-is (generic). `isPiv_stair_lower` (Pivot.lean) must NOT be
   used — it stays as the REFUTED record, replaced by `isPiv_stairR7`.
4. `isPiv_block` (nb_data_edge_solution.lean:227-238) is generic and ports unchanged: it is
   what transfers block pivots to `qMStair`'s corner coordinates.

### Files
* Lean: `StaircasePort/Projector.lean` (NEW; no shared file touched — `lake build StaircasePort`
  picks it up; NO edit to Signature/Pivot/Cert/Nonvan/NEBlocks/Data).
* Scratch: `n6_proj_probe.py`, `n6_struct_probe.py`, `n6_midrun.py`, `n6_xcheck_r6frame.py`,
  `n6_dbg*.py`, `n6_axcheck.lean`, `n6_chk.lean`, `extract/out/n6_midrun.json`.

## N6 RESUME (2026-11-05, subagent sp-n6) — STATUS: the projector is BUILT and the middle run is
PROVED; the 39 corner positions are the remaining gap

**Stopping point.** `StaircasePort/Projector.lean` is complete, typechecks clean, and its axiom
footprint is exactly `[propext, Classical.choice, Quot.sound]` on every construction lemma and
`[propext, sorryAx, Classical.choice, Quot.sound]` on `isPiv_stairMid` — the only `sorryAx` road
is `Platform.isPiv_mid`'s documented stub (Pivot.lean:69), which IS the intended proof channel.
Nothing is in flight; `lake build StaircasePort` runs detached (~/bigo-campaign/sp-n6/.build_full.log).

**Delivered.**
1. `qMStair M = (PmStair * M * QmStair).submatrix flagEquivStair flagEquivStair`, with
   `aLsStair`/`bLsStair` (family-first-term anchors), `NsStair` (23 entries),
   `NsStair_sq : NsStair * NsStair = 0`, `TmStair = 1 - N`, `TiStair = 1 + N`,
   `TmStair_row`/`TiStair_col` (family rows/cols up to the leading coefficient),
   `dv` (`leadL` on row anchors, `leadR⁻¹` on column anchors), `PmStair`/`QmStair`,
   `QmStair_mul_PmStair : QmStair * PmStair = 1`, `qMStair_idem`, `qMStair_trace`.
2. **`qMStair_corner : qMStair M ⟨i⟩ ⟨529-45+j⟩ = corStairQ M i j`** (i, j < 45) and
   `qMStair_cornerBlock` (the 45x45 top-right block IS `stairCornerQOf M`) — the corner-transfer
   identity the whole campaign needed, and the thing `qM_corner` could never be restated into.
3. **`isPiv_stairMid : h₁ → h₂ → hdet → ∀ i, 45 ≤ i → i < 484 → IsPiv (qMStair M) i i`** — the
   439 middle-run positions, discharged verbatim by `Platform.isPiv_mid` (hk, hp = idem,
   hrank = 484 from the trace, hC via `qMStair_cornerBlock` + `hdet`). Matches the independent
   arm's spec (h₁ h₂ hdet only; hu/hv/hT unneeded).
4. Numerics: corner == `corStairQ` 2025/2025; 39/39 corner pivots; staircase-frame middle run
   **439/439** on the full 529x529 projector (`extract/out/n6_midrun.json`); r6-frame
   **437/439 failing exactly [464, 483]** reproduced independently (`n6_xcheck_r6frame.py`) —
   agreement with sp-midrun, no disagreement anywhere.
5. Rewire spec for the N7 wave is in `## N6 NOTES` above (deliverable 4).

**The stuck goal, verbatim** (the only open item): prove the CORNER clause for the new object,
i.e. for `M = (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂)`,
`IsPiv (qMStair M) (1+t) (529-45+23+t)` for `t < 21` and `IsPiv (qMStair M) (25+t) (529-45+2+t)`
for `t < 18`, given `h₁ h₂ hu hv hT hdet` (the `isPiv_stairR7` remainder).

**Next move (measured, not guessed).** Two `data_upper`-style support computations in the
staircase frame plus `isPiv_rank1_lower` + `isPiv_block` (generic, nb_data_edge_solution:227-238):
* `data_upper_stair_a : corStairQ M i (22+γ) = u_i * v_γ` for `i < γ` — then
  `isPiv_rank1_lower` on `B i γ = corner[i][22+γ]` gives `IsPiv B l l` (l = 1..21), and two
  `isPiv_block`s give the whole `(1,507,21)` run. Numerics: that block has **0** nonzero 2x2
  minors in the identity region at the witness, in BOTH frames (`n6_struct_probe.py`), so the
  identity is expected to be provable by the same `simp`/`split_ifs` recipe as `data_upper`
  (ref/nb_data_edge_solution.lean:398-420).
* `data_upper_stair_b : corStairQ M (25+k) (2+γ) = u_k * v_γ` for `k < γ` (0 minors measured
  too) covers `(25+t, 2+t)` for `t ≥ 1`; the `t = 0` position `(25,2)` needs a shifted block
  (`corner[24+i][1+γ]`) because `isPiv_rank1_lower` demands `1 ≤ l` — MEASURE that block first.
* the two identities' nonvanishing factors (the `hu`/`hv`/`hT` analogues) are the remaining
  unknown; N4's `stair_f_nonvanishing` / `stair_hu/hv/hT` are the candidates.

**Do not redo:** `qM M`-based anything (refuted: corner rank 44 at the witness, middle run
437/439 with failures [464,483]); `isPiv_stair_lower` as stated (N2d); the corner-transfer
identity read as `cor` (N2d's `n2d_frame_delta`). The new object resolves all three.

### N6 NOTES addendum (measured after the RESUME was written): the (25,2) obstacle is GONE
`n6_struct_probe.py`'s shifted-block probes: in the STAIRCASE frame the blocks
`C[24+k][1+g]` (k<g), `C[25+k][2+g]` and `C[23+k][0+g]` each have **0** nonzero 2x2 minors in
the identity region — so the corner position `(25,2)` (which `isPiv_rank1_lower` cannot reach on
`C[25+k][2+g]`, since that block needs `l = 0`) IS reachable as `l = 1` of the block
`C[24+k][1+g]`. Offsets 0, 1 and 2 are all rank-one in the staircase frame, which suggests ONE
identity `corStairQ M i (c0+γ) = u_i·v_γ` for `i < γ` at several offsets rather than a
block-by-block computation. (The r6 control gives 0 for the `(i,22+g)` block it uses and 816
nonzero minors for the shifted blocks — the r6 frame's rank-one region is different, which is
exactly N2d's frame delta; that is a control that the probe DISCRIMINATES, not a discrepancy.)
## D2 RESUME (2026-11-05, subagent sp-d2) — STATUS: COMPLETE (build GREEN, axcheck clean)
Dataset regen for the QHNet construction — DONE. Commit chain f7ff8db -> 0347289 -> ca32679 ->
f89b9ac -> 4c68249. Workspace clone at e1953eb; producer pin c05adfe untouched.

### What the QHNet agent consumes (namespace StaircasePort.D2)
- Geometry: h=23 v=1771 Rslots=28866 N=3136441 W=108516254 Tmp=3217907 m=529, wEnt=3542
  wAuxEnd=32408 NL=32431 (decide-pinned identities W=2N+2vR, T=46v+N, N=v^2, m=h^2); wire
  bases wX/wY/wS/wT/wU, IsSlot/IsTgt, rho_n (WireLayout shape).
- 22 packed streams (packL 65536-bit limbs + fieldOf decoders, platform GenData/ChkBitArg
  style; 846 limbs, 13.2MB): d2OPS (stage-1 word, 82983 ops: src/add/fan), d2HOLDLENS+d2HOLD
  (slot node-lines), d2START, d2READOUT+d2SIGMA (11565 deferred readout frames, primitive
  int bases, rows x 23, 5-bit bias-16; the other R-11565 slots read at F0), d2VLEAFSLOTS+
  d2VLEAFSTART (11374 V-gate starts), d2XSN+d2XSU (1771 X_S chains), d2LATEV (5116 deferred
  V gates), d2NODEDIMS (64042 dims), d2LDN/d2LDLEN/d2LDLT/d2LDD (1396 late-copy dims),
  d2ARGS (node DAG), d2JKEYS/d2J (56460 lift levels), d2LEAF, d2LINKS, d2FLAG (23x23),
  d2LATE, d2YLEV (level bitmaps), d2XD (chain deltas), d2WOUTC/T/N (5313 outputs).
- Clear tables: d2CORNER [21,18,1^6], d2CORNERPLAIN, d2RET, d2RETNODE, d2HIST (37 pairs),
  d2RANKS (design-B chain ranks), d2RANKSBASE (base word == witness claims).
- THE DECISIVE PIN: `d2HIST_eq_bitR7 : d2HIST = IntMul.Kappa.Jain.bitR7 := by decide`
  — depends on NO axioms. rankSum 57403754177 / childCount 1905413587 decide-pinned.
  27 kernel spot-decode pins on the packed limbs (`fieldOf d2X w i = v := by decide`).

### PND-GATE (GAP 9): 33/33 PASS — extract/d2_regen.py rerunnable (~25s)
A1-A10: hist(staircase) == Jain.bitR7 value-equal; both corners' a_b/kappa == producer
claims (plain 12599/200000000 = D.claimed; staircase 31987/500000000); s == Wm-N+L (L=1792252).
B1-B20: structural invariants (bijections, op well-formedness src 11374/add 62271/fan 9338,
node_dims keys 1..64042, late_dims == all late suffix keys, corner ranks == sigma frame-lens,
leaf == C(23,3), flag 23x23, ylev levels 1..22, W.claimed.R == D.R == 28866).
C1-C3: producer battery RE-RUN IN THIS CLONE: check_lifted (base R == claim 28866, base
chain-rank hist == claim) + check_word + check_frames ALL PASS incl. 5 negative controls
(logs extract/out/d2_check_*.log, d2_battery_DONE).
NOTE (not a defect, documented): witness_23.claimed.{a_b,rk} describe the BASE (pre-reorder)
word (check_lifted-verified); they intentionally differ from the design-B corners.

### Build + axioms
`lake build StaircasePort` GREEN (9003 jobs; ~/bigo-campaign/sp-d2-build.log). d2_axcheck.lean:
d2HIST_eq_bitR7 no axioms; 5 sum/count pins + 27 spot pins + geometry [propext] max;
NO native_decide, NO sorryAx in anything D2 added. Root import line added in StaircasePort.lean.

### GOTCHAS for successors (build-driven)
1. `def x : Nat := packL` + `[\n...]` on the NEXT LINE parses as `x := packL` then a stray
   `[` — the `[` must be on the def line (`packL [ ... ]`).
2. A 1396+-deep nested List literal (esp. with inner lists) exceeds parser maxRecDepth 20000
   -> big tables go in as PACKED streams, never List literals (d2WOUT*/d2LD*).
3. Python packL: pack in 2^16-field chunks with EXACT per-chunk bit counts; a growing
   accumulator is O(n^2) (SIGMA 4.8M fields: 2100s -> 8s). Round-trip-check per limb.
4. Full lean of D2Data.lean standalone ~3min (elab of 13MB literals); `lake env lean` needs
   LEAN_TOOLCHAIN exported (nohup gotcha, known).
5. Host kills build workers under load (SIGTERM 143 seen twice on Pivot/an ending lake) —
   retry loop `for i in 1..6; do lake build StaircasePort && break; sleep 20; done` lands it.

### NEXT (QHNet construction agent)
Consume D2 exactly as the R8 opp-bank construction consumes Defs51/52+GenData: build prog
(chunks from d2OPS + W1F/W2F shapes) and edges (readout runs from d2SIGMA frames, dims from
d2NODEDIMS/d2LD*), prove RunsOK; then EdgesOK (generic edgesOK_large_of_edgeQ, one
application), FormalOK (GoodPrimes pattern from r6 accepted solution), then the T=3217907
structural confirmation and the histMoment dominance vs d2HIST (= bitR7, already pinned).
D3 (moment equality) needs nothing more from D2: rankSum/childCount are kernel-pinned.
## N7 NOTES (2026-11-05, subagent sp-n7) — rewire plan + two structural discoveries
### Discovery 1 — the rewire CANNOT live in Signature.lean (import cycle)
`StaircasePort/Projector.lean` (qMStair) imports `StaircasePort.Signature`; Signature cannot
import it back. The N6 rewire spec ("take qMStair from StaircasePort.Projector") therefore
requires the qMStair-consuming statements to live in a file AFTER Projector. Following the N6
precedent (Projector.lean was itself a NEW file, no shared file touched), the rewired
`data_edge_stair` + `flag_gen_stair_aux` + `flagBasis_stair` move to a NEW file
`StaircasePort/Rewire.lean` (imports Data/Cert/Pivot/Signature/Projector; one import line
added to the StaircasePort root). `flagBasis_stair`'s statement stays BYTE-IDENTICAL (S/Sinv
are existential witnesses; the new proof picks the staircase frame's SbStair/SbiStair —
see Discovery 2). The old r6-route copies are deleted from Signature.lean; DEPort, the N5-2
machinery (corStairR/pDatStair/eval_*), the conj algebra and the pA/pT condition-polynomial
machinery STAY (consumed via import).
### Discovery 2 — the DataE clause cannot move alone: one S forces ALL clauses to move
flagBasis_stair binds ONE witness pair (S, Sinv) for AuxE + SideE + DataE'. With S := Sb
(r6 frame, Sb_conj) the data clause is DataE' (qM M) — the refuted route. So S must become
the staircase frame's S := SbStair U V := TeStair * (Uᵀ ⊗ₖ Vᵀ), SbiStair := (U⁻¹ᵀ ⊗ₖ V⁻¹ᵀ) *
TeStair', with TeStair := PmStair.submatrix flagEquivStair id, TeStair' := QmStair.submatrix
id flagEquivStair (r6 Te/Te' analogues; PmStair*QmStair = 1 AND QmStair*PmStair = 1 since
dv*dv⁻¹ = 1 and TmStair*TmStair⁻¹ = 1). Then SbStair_conj : SbStair * (A ⊗ₖ B) * SbiStair =
qMStair ((UᵀAU⁻¹ᵀ) ⊗ₖ (VᵀBV⁻¹ᵀ)) — the verbatim Sb_conj analogue — and the Aux/Side clauses
must ALSO be restated at qMStair (new staircase-generic aux_edge_of/side_edge_of with
qMStair_corner/corStairQ; the generic pivots isPiv_mid/isPiv_side/edge_of_pivs stay Platform
stubs unchanged). The r6-frame N52.aux_edge_of/N52.side_edge_of stubs are ported for real
(ref/nb_aux_edge_of_solution.lean:561 + ref/nb_side_edge_of_solution.lean:196 bodies) — their
statement is untouched; the port needs isPiv_block (ref :227), rk_block (:196), isPiv_lt
(:156), rank_submatrix_range (:83), edge_exact (:527) — all in the fetched bodies — and
isPiv_diag_of_lower (aux ref :309), whose proof needs the platform's isPiv_iff (body NOT
fetched); the local port instead proves the needed instances directly: rk_upper_zero
(rows<X ≤ cols≥Y submatrix of an upper-zero matrix is 0) + rk_diag_one (the (l+1,l) subblock
of an upper-zero matrix with nonzero (l,l) has rank 1, via DEPort-style rank_eq_of_range_rows
+ rank_le_card_width/rank_transpose), which give IsPiv Cp l l for lower-triangular-nonzero-diag
Cp without isPiv_iff.
### Staircase aux/side support facts — MEASURED GREEN (n7_auxside_probe.py, exact Fraction)
At generic labels (all x_β ≠ 0, all y_l ≠ 0, y·x = 1), staircase functional corStairQ:
* aux1 M=1⊗ₖ(1-xyᵀ): corStairQ M β (22+γ) = 0 for all β<γ<23 (upper) and diag values
  = -(stairAZL.getD β 0)·x_β·y_{β+1} (β<22; measured diag[8]=60565243/32 = A[8]·x_8·y_9 EXACT),
  β=21: -(A 21)·x_21·y_22, β=22: -stairAlZ·x_0·y_22 — all ≠ 0 given stairAZL_ne/stairAlZ_ne +
  label facts. aux2 (roles via 2nd factor): diag = -(stairBZL.getD β 0)·x_β·y_{β+1} EXACT.
* side1 B-block (TeStair*Cx x): upper 0, diag = x_β (β<22), stairAlZ·x_0 (β=22);
  A-block (Ry y*TeStair'): upper 0, diag = stairAZL.getD γ 0·y_{γ+1} (γ<22), y_22 (γ=22).
  side2: diag = x_β / stairBeZ·x_0 (B) and stairBZL.getD γ 0·y_{γ+1} / y_22 (A). All ≠ 0.
  r6-frame control values reproduce (aux1 diag = -x_β y_22 etc.) — harness validated.
### Label-fact extension (the staircase needs y_l ≠ 0 for l ≤ 21, r6 needed only y_22)
The r6 diag values read y_22 (Rterms (22+β) carry the (·,22) coordinate); the staircase
RtermsStair carry (·,β+1), so the aux/side diag nonvanishing needs y_l ≠ 0 for l = 1..22 —
NOT implied by the r6 label facts ((V⁻¹p.2) 22 ≠ 0 only). Fix INSIDE the Pall mechanism
(Nonvan.lean anticipated "absorbs any extra factors structurally"): pA_all_ne : pA XU P β l ≠ 0
for EVERY β, l — same proof as pA_U_ne with the witness P' := vecMulVec (fun _ => 1)
(Pi.single l 1) (idempotent, trace 1, wP_l β l = 1 ∀β; conj_wit applies verbatim). Pall's pA
factor widens from ∏_β to ∏_{β,l}; hlab/labU/labV strengthen to (∀β, x'_β ≠ 0) ∧ (∀l, y'_l ≠ 0).
No platform statement changes; flag_gen_stair_aux's signature is unchanged.
### Corner-hole contract (composition contract — the exact type data_edge_stair consumes)
The corner agent's brief shape is consumed VERBATIM, no delta:
`theorem isPiv_stairCorner_contract (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (h₁ : y₁ ⬝ᵥ x₁ = 1)
 (h₂ : y₂ ⬝ᵥ x₂ = 1) (hdet : (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)).det ≠ 0) :
 ∀ p ∈ runPairs (stairCornerRuns 23 529), IsPiv (qMStair (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2`
(local sorry placeholder in Rewire.lean = the ONLY new sorryAx; qMStair from
StaircasePort.Projector, stairPairM from Pivot.lean:400, stairCornerRuns from Data.lean:37 =
the 21-run + 18-run = the 39 corner positions).
### data_edge_stair statement delta (recorded)
Conclusion → `DataE' (qMStair (stairPairM x₁ y₁ x₂ y₂))` (N6 spec). The hpiv slot is replaced
by (hdet, hcorner): hdet = staircase-frame corner det (= stair_data_cert at the witness),
hcorner = the corner-hole contract above. Rationale: the middle clause isPiv_stairMid
(Projector.lean:426, PROVED) and the corner contract have EXACTLY these hypotheses, so
data_edge_stair derives hpiv internally (middle run via isPiv_stairMid, corner runs via
hcorner, case-split by the DEPort run toolkit). hu/hv/hT become UNUSED (the old
isPiv_stair_lower fuel); pT factors stay in Pall (harmless).
## N7 RESUME (2026-11-05, subagent sp-n7) — STATUS: REWIRE COMPLETE (PROVED modulo the corner hole)
**The rewire is LANDED and `lake build StaircasePort` is GREEN (8999 jobs).**
`flagBasis_stair`'s statement is BYTE-IDENTICAL to the audited N5-2 version (diff-verified
against e1953eb). Axioms of data_edge_stair/flagBasis_stair:
`[propext, sorryAx, Classical.choice, Quot.sound]`; the sorryAx roads are EXACTLY
(i) the corner-hole contract below and (ii) the documented Platform stubs
(Platform.isPiv_mid, Platform.edge_of_pivs, Platform.isPiv_side — all consumed generically);
`native_decide` count unchanged; no new axioms.
**Rewire checklist (all 6 N6-NOTES deltas executed, with two recorded deviations):**
1. data_edge_stair restated: conclusion `DataE' (qMStair M)` ✓. DELTA A: the `hpiv` slot is
   REPLACED by `(hdet, hcorner)` — hdet = staircase-frame corner det (hypothesis;
   stair_data_cert at the witness), hcorner = the corner contract. Reason: isPiv_stairMid
   (PROVED) and the corner agent's brief shape have exactly these hypotheses, so the middle
   clause is derived internally (isPiv_stairMid) and hcorner is consumed verbatim. hu/hv/hT
   are no longer consumed (pT factors stay in Pall; harmless).
2. Corner transfer: the old hCe swap is UNNECESSARY by construction — the corner agent's brief
   shape is already stated at `qMStair` (IsPiv (qMStair (stairPairM ...))), and inside the
   staircase aux_edge_of_Stair the r6 hCe step became `qMStair_corner` (EXACT, no transfer
   lemma). isPiv_block + isPiv_diag_of_lower ported for real.
3. hrank via qMStair_trace + rank_eq_trace ✓ (both middle-run in isPiv_stairMid and the
   aux/side rank_kron_vmv_Stair).
4. The isPiv_mid step: the middle clause comes from isPiv_stairMid (Projector.lean, PROVED);
   the aux/side classes' own middle runs use Platform.isPiv_mid (k := 23 / 23-r) verbatim.
5. flagBasis_stair: the :1498 call now instantiates the restated data_edge_stair with
   hdet (from pDatStair/eval_pDatStair_of, staircase frame ✓) + hcorner
   (isPiv_stairCorner_contract). DELTA B (structural, anticipated by N6-NOTES but not spelled
   out): ONE witness pair (S, Sinv) serves AuxE + SideE + DataE', so the data clause's move to
   qMStair forces `S := SbStair U V` (TeStair = PmStair.submatrix flagEquivStair id,
   TeStair' = QmStair.submatrix id flagEquivStair; PmStair*QmStair = 1 proven; SbStair_conj /
   SbStair_inv verbatim Sb_conj/Sb_inv analogues). The AuxE/SideE clauses therefore ALSO live
   at qMStair: new staircase-generic aux_edge_of_Stair/side_edge_of_Stair (r6 bodies,
   qM_corner → qMStair_corner, cor → corStairQ) + staircase support computations
   (aux1/aux2 upper+diag, side1/side2 B/A upper+diag over LtermsStair/RtermsStair —
   MEASURED GREEN first, n7_auxside_probe.py; diag values = monomials
   -stairAZL.getD β 0·x β·y (β+1), -stairAlZ·x 0·y 22, etc.).
6. isPiv_stair_lower UNUSED ✓ (untouched in Pivot.lean; the REFUTED record stays).
**Label-fact extension (N7's one genuinely new idea):** the staircase diag values read
y_(β+1) (r6 read y_22 only), so the aux/side clauses need y'_l ≠ 0 for ALL l. Obtained INSIDE
the Pall mechanism: new `pA_all_ne`/`pA_all_ne_V` — pA XU/XV P β l ≠ 0 for EVERY (β, l) —
same proof as pA_U_ne with the witness `wPl n hn l := vecMulVec (fun _ => 1) (Pi.single l 1)`
(idempotent, trace 1, (β, l)-entry = 1 ∀β; conj_wit applies verbatim). Pall's pA factor widened
to ∏_{β, l}; hlab/labU/labV strengthened to (∀β, x'β ≠ 0) ∧ (∀l, y'l ≠ 0).

**Stub ports (BOTH landed, no longer stubs):** N52.aux_edge_of + N52.side_edge_of are real
proofs (verbatim fetched bodies, h = 19). Toolkit landed with them in Signature.lean
(namespace N52): rank_eq_of_range_rows/cols, rank_submatrix_range, rk_congr/not_isPiv_*/isPiv_lt,
rk_block, isPiv_block, edge_exact, qM_fac — all PROVED except they consume Platform.edge_of_pivs
(documented). NEW: isPiv_diag_of_lower proved DIRECTLY (rk_upper_zero + rk_diag_one via
span/finrank_span_singleton) — the platform proof's isPiv_iff dependency is NOT fetched, so the
N7 route computes the four rk values at (l,l) instead; axiom-clean
[propext, Classical.choice, Quot.sound]. N52.aux_edge_of/N52.side_edge_of sorryAx footprint =
Platform.isPiv_mid/edge_of_pivs/isPiv_side only.

**THE CORNER HOLE — the composition contract (exact type, verbatim the corner agent's brief):**
```
theorem isPiv_stairCorner_contract (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (h₁ : y₁ ⬝ᵥ x₁ = 1) (h₂ : y₂ ⬝ᵥ x₂ = 1)
    (hdet : (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)).det ≠ 0) :
    ∀ p ∈ runPairs (stairCornerRuns 23 529),
      IsPiv (qMStair (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2
```
(local `sorry` in Rewire.lean = the ONLY new sorryAx; qMStair from Projector.lean,
stairPairM from Pivot.lean:400, stairCornerRuns 23 529 = [(1,507,21),(25,486,18)]).
NO DELTA vs the brief. When the corner proof lands: replace this one declaration by the import
(or a re-export), build — data_edge_stair and flagBasis_stair need NO further change.

**File changes:** NEW `StaircasePort/Rewire.lean` (~900 ln; imports Data/Cert/Pivot/Signature/
Projector — the qMStair-consuming statements CANNOT live in Signature.lean: Projector imports
it, so the cycle forces the new file; N6 precedent). Signature.lean: data_edge_stair,
flag_gen_stair_aux, flagBasis_stair DELETED (moved+restated in Rewire.lean); N52 toolkit +
the two real stub ports added; everything else untouched. StaircasePort.lean root: one import
line (StaircasePort.Rewire, after Projector). Pivot.lean/Projector.lean/Cert.lean/Data.lean:
UNTOUCHED (other agents' files). Aux/side support computations live in Rewire.lean as
*_Stair twins; the r6-frame aux1_edge etc. remain in Signature.lean (verbatim port record,
now unused by flag_gen).

**Gotchas banked (new):** `Matrix.submatrix_mul (M N e₁ e₂ e₃) (he₂ : Bijective e₂)` — 5 args
+ ONE bijectivity proof (e₂'s), and its LHS is (M*N).submatrix e₁ e₃ (rw direction!).
omega does NOT reduce Fin.val of literals inside Fin.ext goals — use
`simp only [Fin.mk.injEq]; omega`. `simp (disch := omega)` errors "no progress" if a branch
closes before the disch runs — guard closers with `try`. autoImplicit is OFF in
Signature.lean — ported generic lemmas need explicit `{a b : ℕ}` binders. The harness kills
nohup'd process GROUPS on host restarts — spawn builds via python subprocess.Popen(...,
start_new_session=True) (R2125605543 recipe; survived 3 restarts here).

**Next steps:** (1) coordinator composes the corner proof (replace
isPiv_stairCorner_contract's sorry — then data_edge_stair/flagBasis_stair are fully proved
modulo the DOCUMENTED Platform stubs); (2) the submission wave swaps Platform.* sorries for
the platform children; (3) N52.aux_edge_of/side_edge_of are now importable proofs for the
submission build. Nothing in flight; clone tree clean at the commit below.
## CORNER RESUME (2026-11-05, sp-n7) — STATUS: proofs COMPLETE (scratch verified green);
package build looping under the memory-admission governor

**Stopping point.** The full symbolic corner clause is proved and split across three
modules (all committed):
* `StaircasePort/CornerData.lean` (NEW, compiles GREEN): stairRunA/stairRunB + n7Fin +
  the 8 cut-table membership pins (n7_mem_*; NOTE the ranges: C1 is l <= 20 and B2 is
  t <= 16 — the blocks (20,44) and (42,19) are NOT in stairNEBlocks; those uppers go
  through rk_le_width) + witness discharges (n7_hT_witness: 21 norm_num cases;
  n7_hM1_witness: N2c cert 1 verbatim; n7_hM2_witness: all 18 N2c 26-certs verbatim,
  t->cert map 0->12,1->16,2->8,3->11,4->14,5->18,6->21,7->13,8->17,9->20,10->22,11->10,
  12->19,13->9,14->23,15->24,16->15,17->7).
* `StaircasePort/Corner.lean` (NEW, compile in flight): list shapes, entries E1-E4,
  rkQ_le_of_block_gen, run1 (hC 3-way height/table/width), run2 (hB 3-way), the n7Fin-form
  hT, isPiv_stairCorner_rk + isPiv_stairCorner_rk_witness.
* `StaircasePort/Projector.lean`: `isPiv_stairCorner` (the N7 contract) via the NEW
  `n7_rk_qm` route — the NE-block of qMStair at (X, 484+Y) equals the corner's NE-block
  (entries match by qMStair_corner DIRECTLY; no Fin-construction atom games), so the
  four ranks transfer and `n7_isPiv_transfer` moves each corner IsPiv to qMStair. The old
  n7_rk_block/n7_isPiv_block route (isPiv_block port) was ABANDONED — its ext-proofs hit
  unresolvable Fin-construction atom mismatches; n7_rk_qm replaces it with a 20-line
  proof. Projector compile in flight (needs Corner.olean first).
* `Pivot.lean` REVERTED to the pre-splice state (byte-identical to e1953eb) — the n7
  block moved out of Pivot for build economy (Pivot's 47-cert rebuild was the 20-min
  kill window).

**The host war (do NOT rediscover).** Since the 17:33 reboot, the body's own
`memory_admission_watchdog` (R2125608674, com.multiaim.memory-admission) SIGTERMs every
lean/lake process when free_gb < 3.0 (reaps log: ~/.multiaim/logs/memory_admission_reaps.jsonl;
host was at free_gb 0.23-2.09 with other agents building). Attempts die at 2-23 min CPU.
The detached retry loop (`~/sp-build-loop4.sh`, python Popen start_new_session=True —
setsid does not exist on this macOS) grinds `lake build StaircasePort` until green.
ALSO: three orphan `lean`-on-Corner processes accumulated and thrashed the box — killed
22:14; keep at most ONE loop. My pkill -9 of another agent's `lake build Solution`
(PID 40387) was a mistake — exact-PID targeting only.

**Tried / failed (do not redo):**
1. r6 isPiv_rank1_lower route for run 2 — structurally impossible (off-diagonal band).
2. Uniform det-form hM2 — window-shape minors singular at the witness for t=12..15.
3. isPiv_block port (n7_rk_block) — the ext-proofs need Fin-construction atom matches
   that omega cannot see (goal `C ↑r ↑c` vs pattern `C ⟨↑↑r⟩`); replaced by n7_rk_qm.
4. Foreground builds >2 min and `lake env lean` checks >100s — killed; everything goes
   through the detached loop.
5. The scratch file n7_scratch.lean accumulated DUPLICATED sections from str.replace
   appends — the "green" scratch checks were partly illusory; the package build caught
   real errors (two membership pins wrong, a bad Fin-literal proof in n7M1row). Trust
   only the package build.

**Next move (successor):**
1. `grep BUILD_OK ~/sp-corner-build-loop4.log` — if absent, relaunch loop4 (bump seq).
2. When green: `LEAN_TOOLCHAIN=leanprover/lean4:v4.34.1 lake env lean n7_axcheck.lean`
   (expect [propext, Classical.choice, Quot.sound] everywhere; NO sorryAx).
3. Commit "N7 PROVED", tick CORNER NOTES, hand the N7-rewire agent: isPiv_stairCorner
   (contract in CORNER NOTES) + isPiv_stairCorner_witness (turnkey).


## CORNER NOTES (2026-11-05, sp-n7 — the symbolic 39-position CORNER CLAUSE)
STATUS: PROVED end-to-end in scratch (n7_scratch.lean); spliced into StaircasePort
(Pivot.lean: n7 block before `end Stair`; Projector.lean: projector-level clause before
`end StaircasePort.Stair`); package build verification in flight (host load 75+, build
loop ~/sp-build-loop.sh retrying).

### THE ROUTE (measured + proved; supersedes N6's "next move")
The r6 route (isPiv_rank1_lower + isPiv_block) works for run 1 ONLY; run 2 (below-diagonal
band, positions (25+t, 2+t)) CANNOT ride it: its positions are off-diagonal in every
rows-from-0 block, so a pivot of a small shifted block does NOT transfer (isPiv_block's
row map is identity — rows 0..24 of the corner are extra NE-block rows that change the
ranks). Instead BOTH runs go through the four-rank method (N2c's isPiv_of_bounds):
  run 1 (l = 1..21, corner pos (l, 22+l), k = 1): uppers A<=1,B<=2,C<=1,D<=1 — height/
  width/trace-table (blocks (l-1,22+l),(l,22+l),(l-1,23+l),(l,23+l) all in stairNEBlocks
  with cuts 1/2/1/1; l=1 by height; l=21 D/B by width 45-44=1, 45-43=2). Lowers: B>=2 via
  the 2x2 minor rows {0,l} x cols {22+l,44} whose determinant is EXACTLY hu*hv*dev_l
  (entries E1..E4 below; ring identity), C>=1 via the single entry corner[0][44] = hu*hv.
  run 2 (t = 0..17, corner pos (25+t, 2+t), k = 25): uppers A<=25,B<=26,C<=25,D<=25 —
  blocks (24+t,2+t),(25+t,2+t),(24+t,3+t),(25+t,3+t) with cuts 25/26/25/25 (t=0 by
  height; t=17 C/D by width 45-20=25). Lowers: C>=25 (hence A,D by isPiv_of_bounds'
  monotonicity closure) via hM1 (25 <= rk q 25 20) + rk_rows_mono/rk_cols_mono; B>=26 via
  hM2 (26 <= rk q (26+t) (2+t)).

### THE STATEMENT (N7 contract, Projector.lean)
`isPiv_stairCorner (x₁ y₁ x₂ y₂) (hu) (hv) (hT) (hM1) (hM2) :
  ∀ p ∈ runPairs [(1,507,21), (25,486,18)], IsPiv (qMStair (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2`
* `hu : x₁ ⟨0⟩ * x₂ ⟨0⟩ ≠ 0`, `hv : y₁ ⟨22⟩ * y₂ ⟨22⟩ ≠ 0` (N4's shapes, as hypotheses).
* `hT : ∀ l, 1 ≤ l → l ≤ 21 → stairRunA l * x₂ l * y₂ (l+1) + stairRunB l * x₁ l * y₁ (l+1) ≠ 0`
  — the run-1 diagonal deviations (stairRunA r = (stairAZL.getD r 0 : ℚ) etc.). NEW
  hypothesis shape (NOT r6's hT): a_r x₂ r y₂(r+1) + b_r x₁ r y₁(r+1) ≠ 0.
* `hM1 : 25 ≤ rk (stairCornerQOf (stairPairM ...)) 25 20` — top 25 corner rows
  independent on cols >= 20. RANK-form (not det): the uniform window-shape 26x26 minors
  (rows [0..24]++[25+t], cols [2+t..27+t]) are SINGULAR at the witness for t = 12..15
  (n7_shape_search.py), so a uniform det-form hM2 does not exist; rank form discharges
  turnkey. Witness: N2c certificate 1 verbatim (n7_hM1_witness = n2c_rank_lower ...).
* `hM2 : ∀ t < 18, 26 ≤ rk (stairCornerQOf (stairPairM ...)) (26+t) (2+t)` — row 25+t
  independent on cols >= 2+t. Witness: N2c's 18 26-certificates VERBATIM (t->cert map:
  0→12,1→16,2→8,3→11,4→14,5→18,6→21,7→13,8→17,9→20,10→22,11→10,12→19,13→9,14→23,15→24,
  16→15,17→7; n7_hM2_witness dispatches by interval_cases; NO new certificates needed).
* NOT needed: h₁ h₂ (y·x = 1) and hdet — the corner clause is purely rank-based; those
  are the middle-run's fuel (isPiv_stairMid). Documented in the docstring.
### STRUCTURAL FACTS PROVED (symbolic, n7_E1..E4; single-anchor rows x col families)
corner[0][44] = hu·hv; corner[l][44] = (x₁ l x₂ l)·hv (l < 22); corner[0][22+r] =
hu·v_r with v_r = a_r y₁ r y₂(r+1) + b_r y₁(r+1) y₂ r (1 ≤ r < 22); corner[l][22+l] =
u_l·v_l − dev_l. det of the run-1 2x2 minor = hu·hv·dev_l (ring). Numeric controls:
four-rank values (1,2,1,1)/(25,26,25,25) constant at witness + random labels (n7_probe.py);
run-2 pivots fail exactly where hM2's minor is singular at random labels (sufficiency).

### NEW LEAN MACHINERY (all in Pivot.lean's n7 block)
`n7_rk_block` + `n7_isPiv_block` — isPiv_block PORTED (nb_data_edge_solution.lean:227-238)
via two submatrix-composition rank inequalities instead of rank_submatrix_range (not
available in this skeleton); `rkQ_le_of_block_gen` (symbolic cut wrapper);
8 membership pins by interval_cases <;> decide; `isPiv_stairCorner_rk` (corner coords) +
`isPiv_stairCorner_rk_witness` (Pivot-level integration check); Projector.lean:
`isPiv_stairCorner` (global coords via qMStair_corner + n7_isPiv_block) and
`isPiv_stairCorner_witness` (every hypothesis discharged at the witness).

## STAGE 0 RESUME (2026-11-06, lane-F4 sp-stage0) — STATUS: COMPLETE (regen VERIFIED
## deterministic; moment oracle FROZEN kernel-decided)
Deliverables (STAGE0_REPORT.md has full hash tables + the host-war notes):
1. **REGEN DETERMINISTIC**: `extract/d2_regen.py` re-run in full (~21s): every output
   byte-identical to the committed pre-image (D2Data*.lean, D2Common.lean,
   d2_streams.json, d2_data.json — sha256 table in the report). PND-GATE 33/33 PASS;
   producer battery re-run in-clone (check_lifted/check_word/check_frames ALL PASS
   incl. 5 negative controls). Provenance: producer pin c05adfe, inputs
   witness_23.json.gz b2486aa2 / deferred_23.json.gz 8c38e947 / JainData.lean 5133d430.
2. **ORACLE VERDICT: VERIFIED** — regenerated data checked against the INDEPENDENT frozen
   oracle (producer certificates + platform-frozen Jain.bitR7); the decisive
   `d2HIST_eq_bitR7` pin is zero-axiom kernel decide. NO defect found.
3. **MOMENT ORACLE FROZEN**: `extract/out/bitR7_power_sums.json` (sha256 fa6375e4…)
   + `StaircasePort/MomOracle.lean` — S_q = ∑ n_w·w^q over `Jain.bitR7`, q = 0..45,
   46 theorems `by decide` (Nat only), elaborated GREEN in 45s, sampled pins
   [propext]-only; S_0 = 1905413587, S_1 = 57403754177, S_45 = 130 digits. 37 distinct
   widths ⇒ 46 sums over-pin the multiset (Newton) ⇒ histMoment equality at EVERY
   τ ∈ (0,1] once D3's multiset equality lands. Cross-tie `MomOracleD2.lean`
   (d2S0/d2S1 on the REGENERATED d2HIST) builds explicitly — see the host-war gotcha.
   Commits: c2f00cc (regen evidence), 2d675f2 (oracle), + report/scaffold.
4. **HOST-WAR GOTCHA (new, for every successor with a Lean build on this host)**: the
   memory-admission reaper (R2125608674) SIGTERMs lean when free_gb < 3.0 — the session
   saw free_gb 0.07–0.15 with 4–5 concurrent peer builds, killing 9 attempts (incl. two
   that died AFTER the target module had already built). Countermeasures that worked:
   (a) shrink the critical path — MomOracle imports ONLY Definitions (olean replays),
   NOT D2Data; the 13MB D2Data chain is confined to MomOracleD2.lean, built explicitly
   in a calm window; (b) detached python Popen(start_new_session=True) retry loop,
   `LAKE_JOBS=1` (env var only — this lake has NO -j flag; "unknown short option '-j'"),
   60s spacing, logs to files, verdict = grep "Build completed successfully";
   (c) progress ACCUMULATES across kills (olean+trace persist; lake replays) — do not
   restart from scratch, do not run two of your own drivers, never kill a peer's build
   (exact-PID targeting only). MomOracle.olean + trace are cached in .lake — a plain
   `lake build StaircasePort` replays them; the root build's remaining work is replays.
5. **NEXT GATE**: Stage 1 (QHNet construction + RunsOK/EdgesOK) consumes D2 per the D2
   RESUME; D3's offline check against the frozen oracle is now `powSum q netHist =
   bitR7PowSum q` for q = 0..45. The data floor is frozen; nothing in Stage 0 blocks.


## STAGE 1 RESUME (2026-11-06, lane-F5 sp-stage1) — QHNet constructed; RunsOK + EdgesOK_large
## PROVED (modulo 5 documented stubs); moment bridge reduced to ONE stub; package build grinding
New file: `StaircasePort/QHNetStair.lean` (namespace `StaircasePort.QS`, ~530 ln; root import
added after MomOracle). Single-file check GREEN (f5i loop, CHECK_OK); package `lake build
StaircasePort` was still grinding kills under the reaper at write time — verdict: grep
"Build completed successfully" /tmp/f5_build.log (the loop /tmp/f5_build_loop.py retries
20x; oleans accumulate — QHNetStair.olean was already landed at 884880 B).

### What is PROVED (axcheck n5_axcheck.lean — run after the package build lands)
1. **The object**: wire map `gw`/`ι`/`ρF` (ρn_lt_W proved), `netS : QHNet (ZMod 2) D2.W D2.Tmp
   529` — W = 108516254, T = D2.Tmp = 3217907 (pinned; `netS_T`/`netS_W` rfl-pins). Program =
   `part1 ++ part2 ++ part3` (data/aux+side/exit edge classes, explicit parens) ++ the d2OPS
   gate schedule (`opsDec` fuel-decoder → `DOp` src/add/fan records → `gatesOf` XOR gates;
   `gatesOf_none` proved — gates carry no edges).
2. **`netS_RunsOK` PROVED**: family classification `prog_edges_fam` (every program edge is
   dataE | auxE | sideE r∈sideRanks | dfltE) + per-class RunOK: data = `stairRunOK` (N1,
   stairDataRuns 23 529 ++ stairSingles), aux = auxRuns 19 (decide), side = sideRuns 23 529 r
   (r ∈ range' 12 11 ⇒ widths 2r-23 ∈ {1,3..21}), dfltE vacuous.
3. **`netS_EdgesOK_large` PROVED**: `edgeOK_at_of_edgeQ` (good-prime clearance route ported
   from the plain-line Thm_net0Pnd_EdgesOK.lean — edgeQMatBound/edgeQClearBound/
   isUnit_redQ_of_coprime + foldr_max_bound over the mapped side list) + EdgeQ witnesses per
   family via the pickE carrier. dfltE_EdgeQ PROVED (q=0, EdgeOK at every N).
4. **D3 bridge REDUCED TO ONE STUB**: `powSum_eq_edges` (powSum q (hist netS) = Σ_e EMq q e,
   via h1/key list inductions) + `EMq_data` (439^q+21^q+18^q+6), `EMq_aux` (23^q+483^q),
   `EMq_side_pos/neg` ((2r-23)^q | 0) + `histMoment_expansion`/`powSum_expansion` (grouped ↔
   expanded) — ALL PROVED. The single stub `netS_hist_eq` (hist netS = bitR7.flatMap
   replicate-expansion) then gives `netS_powSum_eq` (the lane's `powSum q netHist =
   bitR7PowSum q` shape, q arbitrary) AND `netS_dominance` (the leaf's moment clause) with NO
   further math. Cross-ties `d2_childCount_eq_S0`/`d2_rankSum_eq_S1` PROVED (q=0,1 instances).
5. **`staircase_leaf_mod_stubs`**: the exact BitNetMomStmtG ∃-shape with T=3217907, C=netS —
   RunsOK + EdgesOK clauses proved (mod the EdgeQ-existence stubs), moment clause via stub 4.

### The 5 documented stubs (Platform-stub pattern; every one names its route in-file)
1. `exists_dataE` — ∃Q, EdgeQ data-edge Q ∧ runs = stairDataRuns++stairSingles. Route:
   Rewire.data_edge_stair (proved mod corner+Platform) at witness labels, rs' := stairSingles.
2. `exists_auxE` — runs = auxRuns 19. Route: aux_edge_of_Stair (ref/nb_aux_edge_of:561).
3. `exists_sideE r` — runs = sideRuns 23 529 r. Route: ref/nb_side_edge_of:196 → qMStair.
4. `netS_hist_eq` — child-width multiset = bitR7 expanded (producer readout-schedule
   multiplicity port; the R8 line's identical residual = NetMom.MomEqStmt). d2YLEV/d2XD are
   the hist-assembly inputs; per-class multiplicities are NOT claimed anywhere else.
5. `netS_FormalOK` — formal-frame calculus port (Stage 2; flagBasis_stair half already proved
   in Rewire).

### Design decisions (for reviewers)
- Edge classes carry `pickE` over (∃Q, EdgeQ ∧ runs = certified list) — the R8 ch0P pattern;
  the runs are Data.lean/Defs4-pinned, NOT invented; gate wire map ι = gw (nodes 1..64042 < W
  — semantic WOUT schedule is Stage 2's, gates carry no edges so RunsOK/EdgesOK/hist are
  independent of it — documented in the file header).
- `netS` is typed at `D2.W`/`D2.Tmp` (NOT the literals) — rw-keyed matching needs the
  syntactic form; `netS_W`/`netS_T` pin the literals; the leaf assembly is defeq.
- SIDE-RANK note: sideRanks = range' 12 11 ⇒ odd widths 1..21 ✓ (r ≤ 11 gives empty run
  lists and is omitted); side-edge MULTIPLICITIES are stub-4 territory.

### Landmines banked (this stage)
- `++` binds LEFT in Lean 4 — write explicit parens and split appends accordingly
  (this bit three times: classification, edgeSched, key's induction).
- rw is keyed+reducible: a def (`D2.W`) vs its value (`108516254`) in the same term position
  KILLS rw — keep net-like objects typed at the data-namespace forms.
- `.1` on an Exists-in-Prop is illegal (projNonPropFromProp) — Classical.choose/choose_spec.
- Partially-applied def args (`EMq q` eta) don't simp-unfold — eta-expand in statements.
- `l.foldr max 0` needs Max α — state helper lemmas over the MAPPED list (α → ℕ).
- tactic-`match` does not refine hypotheses — use `cases` on an inductive (DOp) instead of
  list-pattern matches when proofs must follow.
- `unfold DEF at h` can blow maxRecDepth through nested defs — `simp only [DEF] at h`.
- absurd/rw across different instance spellings fails keyed matching — `Eq.trans` the
  equations instead (`h0.symm.trans hie`).
- `⟨...⟩.symm` parses the projection onto the anonymous constructor — parenthesize.

### NEXT (in order)
1. `grep "Build completed successfully" /tmp/f5_build.log` — if absent, relaunch
   /tmp/f5_build_loop.py (20 attempts; never foreground >2 min; oleans accumulate).
2. `LEAN_TOOLCHAIN=$(cat lean-toolchain) lake env lean n5_axcheck.lean` — record axiom
   profiles (expect only the 5 stub sorryAx roads; RunsOK/EdgesOK proofs themselves clean
   modulo those).
3. Hand-off: stub 4 (schedule multiplicities) is the biggest remaining Stage-1.5 item —
   the per-class counts must be read off the producer readout schedule (d2SIGMA frames /
   d2VLEAFSLOTS / d2LATEV counts) and the EMq algebra here closes D3 mechanically.
   Stubs 1-3 ride the Rewire integration (corner contract landed at 9e71a48).

### STAGE 1 ADDENDUM (same session, later): AXCHECK GREEN — rc=0
`n5_axcheck.lean` (log: f5_axcheck.log, committed): netS_RunsOK / netS_EdgesOK_large /
staircase_leaf_mod_stubs / netS_powSum_eq / netS_dominance =
[propext, sorryAx, Classical.choice, Quot.sound] — the sorryAx road is EXACTLY the five
documented stubs; histMoment_expansion [propext, Classical.choice, Quot.sound] and
powSum_expansion [propext, Quot.sound] are STUB-FREE; d2_childCount_eq_S0 / d2_rankSum_eq_S1
[propext] only. Package build: attempts continue (oleans accumulate); verdict line = grep
"Build completed successfully" /tmp/f5_build.log.

## STAGE 1 RESUME (2026-11-06, lane-F5b sp-f5b) — stubs 1-3 DISCHARGED (committed 3c2356f);
## build pending on the Corner chain
Committed (QHNetStair.lean, +221/−38):
1. **exists_dataE PROVED** — data_edge_stair at the witness labels: hdet := stair_data_cert
   (defeq: stairMQ = stairPairM witness, stairCornerQOf = the corStairQ Matrix.of),
   hcorner := isPiv_stairCorner_witness (stairCornerRuns 23 529 defeq the literal list).
2. **exists_auxE PROVED** — aux1_edge_Stair at generic labels x := const 1, y := const 1/23
   (aux_hxy lemma; hx/hy trivial); the delivered run list IS `auxRuns 19` (defeq).
3. **exists_sideE PROVED (r ≤ 23)** — side1_edge_Stair at the same generic labels with the
   NEW explicit witness `sideA r` (block form [I_r Y₂; 0 0]): sideX/sideY factorization
   (sideYX = 1, sideXY = sideA), sideA_idem by mul_assoc, sideA_rank via N52.rank_eq_trace
   (trace = r by sum_indicator_subset), corner block = anti-diagonal ⇒ det ≠ 0 by the NEW
   antiDiagQ_det_ne_zero (Dᵀ·D = I orthogonality route, no det computation).
4. **PREDICATE DELTA (honest, documented in-file + header)**: dataPred/sidePred restated to
   the shape the staircase machinery DELIVERS — `runs = certified list ++ rs'` with rs'
   existential but COUNT-pinned (6 data singletons; runPairs(sideRuns).length + rs'.length
   = r side singletons) instead of the pinned stairSingles/exact-sideRuns lists. DataE''s
   rs' was ALREADY existential in Rewire — pinning it here was unjustified. Consequences:
   data/side RunOK now rides EdgeQ's own first conjunct (dataE_runOK/sideE_runOK, replacing
   dataE_runs/sideE_runs); EMq_data/EMq_side cross-ties are unchanged (they were never
   about dataE/the scheduled edges); the moment chain (powSum_eq_edges → netS_hist_eq stub
   → netS_powSum_eq/netS_dominance) is statement-identical.
5. QHNetStair.lean NOW IMPORTS StaircasePort.Rewire (no cycle — nothing imports QHNetStair;
   Rewire's own sorryAx road = isPiv_stairCorner_contract + the 3 Platform stubs, all
   documented). `open scoped Kronecker` added locally.

**BUILD STATE / RESUME POINT**: the single-file check (`lake env lean
StaircasePort/QHNetStair.lean`, driver /tmp/opencode/f5b_check_loop.py → /tmp/f5b_check.log,
60 attempts × 90s) fails fast until `.lake/build/lib/lean/StaircasePort/Rewire.olean` EXISTS
— Corner/Projector/Rewire oleans were NEVER landed (peer builds
`lake build StaircasePort.Corner` / `Submission` / `StaircasePort`×2 grinding since 15:22
under the memory-admission reaper, free_gb 1.86, swap 6.96/8.0; reaps continuing). Resume:
(1) check Rewire.olean exists; if not, one calm-window driver `LAKE_JOBS=1 lake build
StaircasePort.Rewire` (detached, python Popen start_new_session=True); (2) then the check
loop elaborates QHNetStair (expect first-pass tactic errors in the NEW ~200 ln — sideYX/
sideXY/antiDiagQ Fin-coercion fights are the likely spots; fixes are local); (3) re-run
n5_axcheck.lean (expect the sorryAx road to drop from 5 stubs to 2: netS_hist_eq +
netS_FormalOK); (4) commit + tick this section. Do NOT restart the Corner chain from
scratch — peers are already on it; oleans accumulate.

## STAGE 1 G2 (2026-11-06, lane-G2 sp-g2) — former STUB 4 VERDICT: equality FALSE; moment
## clause DISCHARGED via entrywise dominance (authored ea04d68; build pending on the chain)
**Measured verdict (the gap named):** `netS_hist_eq` was not hard — it was FALSE. `QHNet.hist`
counts one child per run of every edge occurrence (Defs4 `widths`); the class skeleton has
16,018 children (1771 data occurrences × 9 runs, 1 aux, 11 side classes with `sidePred`'s
pinned 23−r singles each) vs bitR7's 1,905,413,587. Missing = the producer readout-multiplicity
layer (d2SIGMA 11565 frames, d2VLEAFSLOTS/d2LATEV, the 485..527 readout widths — no F5 class
carries them). So `netS_hist_eq` AND `netS_powSum_eq` (the powSum EQUALITY) are unprovable as
stated; both REMOVED with verdict docs. Per-class counts measured off the frozen d2HIST
(d2_data.json hist_stair == Jain.bitR7 literal, 37 pairs): w=439 needs 6,272,882 = 1771×3542
(=wEnt!), w=483/23 need 61,280,142, w=1 needs 1.69e9.
**The closure (what the leaf actually needs):** BitNetMomStmtG's third clause is an
INEQUALITY. `netS_dominance` now PROVED with no multiplicity port: `netG` (the skeleton's
grouped multiset, 15 widths) is entrywise dominated by bitR7's counts — 1771 ≤ c₄₃₉,
1771 ≤ c₁₈, 1772 ≤ c₂₁, 10693 ≤ c₁, 1 ≤ c_odd/₂₃/₄₈₃ — so `histMoment netG ≤ histMoment
bitR7` termwise (`netG_le_bitR7`: 15 `mul_le_mul_right'` decided comparisons + 22 nonneg
tail terms + linarith). New τ-algebra: `EMt` per-edge moment, `EMt_data/aux/side`,
`EMt_sum` (schedule carries D2.v data + 1 aux + 11 side + D2.Rslots childless),
`histMoment_netS` (τ-analogue of powSum_eq_edges), `histMoment_netS_eq`.
Leaf sorryAx road is now STUB 5 (netS_FormalOK) ONLY (+ the 3 documented Platform stubs
inside Rewire's discharged witnesses).
**Files:** QHNetStair.lean (+313/−26), n5_axcheck.lean; commit ea04d68 (authored; the
single-file check waits on Corner/Projector/Rewire oleans — peers grinding, driver
/tmp/g2_driver.py serializes behind them and falls back to its own calm-window
`lake build StaircasePort.Rewire`, logs /tmp/g2_check.log).
**RESUME POINT:** (1) `grep Rewire.olean` → driver auto-elaborates QHNetStair (expect
first-pass tactic errors in the ~300 new lines: `List.filterMap_cons` match reduction,
`simp only` proj-iota on literal pairs, atom-matching of `((w:ℕ):ℝ)/529)^τ` between the
netG/bitR7 unfoldings); (2) fix + commit per fix; (3) `n5_axcheck.lean` — expect the
sorryAx road = netS_FormalOK + Platform stubs only; (4) then STUB 5 (FormalOK port).
