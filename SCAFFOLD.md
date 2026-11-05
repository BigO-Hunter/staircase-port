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
