# SCAFFOLD.md — staircase witness-1 Lean port skeleton (r7 leaf e27d1a90, bounded first increment)

Date: 2026-11-04. Skeleton only: definitions + sorry'd statements + extracted data.
Every statement elaborates against the REAL platform definitions (Defs4 closure below).

## Environment
- Toolchain v4.34.1 + Mathlib d13f23b7 (project copied from the intmult-sol development, its
  `.lake` cache cloned; intmult-sol itself untouched).
- `Definitions/` = exact 64-file import closure of `Def_IntMul_Kappa_R6_Defs4` (source:
  the platform Definitions workspace, bodies identical to intmult-sol's migrated copies —
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
certificate_round7 @ c05adfe, from the producer recon copy — jain-verify NOT touched).

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
## N4 NOTES (2026-11-04)
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
## N3 RESUME (2026-11-04) — STATUS: PROVED, item COMPLETE
Stopping point: ALL six N3 statements proved in StaircasePort/Cert.lean, zero sorry in the
file; `lake build StaircasePort` GREEN (8997 jobs); commit e91cda8 (+ final axcheck commit).
stair_data_cert axioms: [propext, Classical.choice, Quot.sound] — kernel-checked, no
native_decide, no sorryAx (n3_axcheck.lean prints all 6 + 3 ported helpers).

GAP-7 TIMING (decide +kernel; wall via /usr/bin/time -l; baseline import ≈60s wall):
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
## N2b NOTES (2026-11-05/06)
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
Found INDEPENDENTLY twice (the numeric check + the earlier counterexample in
recovery/sp-n2b-r2:RESCUE_RESUME.md), so it is not a measurement artefact.

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
## N52 RESUME (2026-11-05) — STATUS: PROVED, item COMPLETE
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
## N2c NOTES (2026-11-05)
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
## N2c RESUME (2026-11-05) — STATUS: PROVED, item COMPLETE
Stopping point: NOTHING in flight for N2c. `stairCorner_pivots_witness` is PROVED and
spliced into StaircasePort/Pivot.lean (at the END of `namespace Stair`, after
`stairNE_rk_le`); `lake build StaircasePort` GREEN (8997 jobs, 0 errors, build_n2c.log —
~6 min). Axioms (n2c_axcheck.lean): stairCorner_pivots_witness / stairPivAt /
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

### N2d STATUS: NOT STARTED (budget exhausted) — findings that save the next mind days
1. STATEMENT SHAPE IS CONFIRMED CORRECT and needs NO delta: the consumer
   (StaircasePort/Signature.lean:1499) calls
   `isPiv_stair_lower _ _ _ _ h₁' h₂' (mul_ne_zero (hx1 _) (hx2 _)) (mul_ne_zero hy1 hy2) ?_ ?_`
   — exactly the scaffold's 9 arguments, in order, with `hdet` = the STAIRCASE-frame corner
   det (`stairCornerQOf (...)`), i.e. exactly what N3's stair_data_cert and the N5-2
   course update say. So the frame correction N5-2 measured (corStairQ ≠ cor,
   r6 frame singular) does not change N2d's SIGNATURE; it changes only the PROOF, because
   the corner-transfer identity `Cp i j = cor M i j` (nb_data_edge_solution.lean:534-537)
   must be re-proved in the staircase frame.
2. The middle run (45,45,439) is the easy half: Platform.isPiv_mid (m = 529, k = 45,
   p = qM M) needs hk (`2*45 ≤ 529`), hp (`p*p = p`, from DEPort.qM_idem + the
   Kronecker-of-idempotents identity already used verbatim in
   Signature.lean:204-210), hrank (`(qM M).rank = 484`, the trace computation
   :211-217) and hC (the 45x45 corner at rows 0..44 / cols 484..528 = the transfer
   identity, staircase frame). Positions produced: (i,i) for 45 ≤ i < 484.
3. The two corner runs (1,507,21) and (25,486,18) need: isPiv_block
   (nb_data_edge_solution.lean:227-238, PROVED with a full proof in
   ref/) + N2c lifted from the concrete witness to generic labels.
   The lift is the flag_gen Zariski/Pall product route (nb_flag_gen_solution.lean:977-993);
   N4's stair_f_nonvanishing + stair_hu/hv/hT are built for precisely that product, so
   compose with them rather than re-deriving.
4. isPiv_block also needs `i < j`-shaped side hypotheses on the B/A blocks (the r6 lemma's
   hB/hBd/hA/hAd) — those are the sparse-family facts, and the staircase family's versions
   are LtermsStair/RtermsStair support facts (a `decide`/`simp` on the concrete lists).

## N2d NOTES (2026-11-05) — STATUS: STATEMENT REFUTED (no proof exists)
### Verdict
`isPiv_stair_lower` (Pivot.lean) is **FALSE as stated**. Nothing is proved and nothing
should be: at the extracted staircase witness every one of its five hypotheses holds while
18 of the 39 corner positions it claims are not pivots of the matrix it names. This is the
third false-premise discovery (after N2b's false scaffold statement and
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

## N2d RESUME (2026-11-05) — STATUS: STATEMENT REFUTED, no work in flight
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
   witness, so this route is unavailable at the very witness chosen.
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

**Cross-wave consequence:** the premise that the
staircase design is the flag basis of Defs4's `qM` is wrong (that is the whole content of
`n2d_frame_delta`). Every "swap the runs list inside r6's data_edge" step inherits this.

## N6 NOTES (2026-11-05) — the R7/staircase PROJECTOR exists

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

## N6 RESUME (2026-11-05) — STATUS: the projector is BUILT and the middle run is
PROVED; the 39 corner positions are the remaining gap

**Stopping point.** `StaircasePort/Projector.lean` is complete, typechecks clean, and its axiom
footprint is exactly `[propext, Classical.choice, Quot.sound]` on every construction lemma and
`[propext, sorryAx, Classical.choice, Quot.sound]` on `isPiv_stairMid` — the only `sorryAx` road
is `Platform.isPiv_mid`'s documented stub (Pivot.lean:69), which IS the intended proof channel.
Nothing is in flight; `lake build StaircasePort` runs detached (patient retry loop).

**Delivered.**
1. `qMStair M = (PmStair * M * QmStair).submatrix flagEquivStair flagEquivStair`, with
   `aLsStair`/`bLsStair` (family-first-term anchors), `NsStair` (23 entries),
   `NsStair_sq : NsStair * NsStair = 0`, `TmStair = 1 - N`, `TiStair = 1 + N`,
   `TmStair_row`/`TiStair_col` (family rows/cols up to the leading coefficient),
   `dv` (`leadL` on row anchors, `leadR⁻¹` on column anchors), `PmStair`/`QmStair`,
   `QmStair_mul_PmStair : QmStair * PmStair = 1`, `qMStair_idem`, `qMStair_trace`.
2. **`qMStair_corner : qMStair M ⟨i⟩ ⟨529-45+j⟩ = corStairQ M i j`** (i, j < 45) and
   `qMStair_cornerBlock` (the 45x45 top-right block IS `stairCornerQOf M`) — the corner-transfer
   identity the whole port needed, and the thing `qM_corner` could never be restated into.
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
