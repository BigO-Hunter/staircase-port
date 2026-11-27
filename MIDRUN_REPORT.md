# MIDRUN_REPORT — sp-midrun (independent middle-run arm, witness-1 staircase port)

Snapshot: 49b69f8 (this repo's independent middle-run arm). JSONs: `extract/out/midrun_r6frame.json`,
`extract/out/midrun_orders.json`. Method: rightmost-pivot profile pc of qM M (one 529×529
elimination; `rk(X,Y) = #{r<X : pc_r ≥ Y}`, `IsPiv(i,j) ⟺ pc_i = j` — the producer's own
identity, check_stair.py:175). All ranks double-prime (1000000007, 998244353, asserted
equal); failing blocks re-verified by direct submatrix elimination (midrun_spotcheck.py).

**HEADLINE: the r6-frame middle run is 437/439 at the witness — NOT all pivots.**

1. **439 middle positions, r6 frame (qM M), witness** (midrun_r6frame.json): rank(qM M)=484
   (both primes ✓ port's trace), corner rank 44 ✓ N2d. Failing: **(464,464)** (A,B,C,D =
   44,45,44,45; pc=483, pivot shifted one right) and **(483,483)** (45,45,44,44; pc=−1, row
   dependent). Validation: old run 21/21 ✓ (r6's proved thm), added run 0/18, singles 4/6.
2. **Order-dependent: YES.** 4 orders × 2 primes (natural/reversed/shuffled/colmajor):
   middle pc profile NOT uniform; EVERY order fails at the last middle position 483
   (dependent row) + exactly one order-dependent shifted pivot (pc=483) at 464/51/50/103.
   No flagEquiv choice rescues qM; the r6-frame clause is false for every instantiation.
3. **Producer convention**: NO middle order exists producer-side. The entrance block
   m−4h+2 = 439 is ONE batched rank-439 block, `H[m-4*h+2] += 2*N` (deferred.py:183,
   docstring :164; count 2N=6272882, round7-histograms.json "bit" [439,6272882]). Only the
   corner is pc-derived (check_stair.py:174 `rightmost_pivots`, :98 runs(pc)), corner order
   = family-list order = Lean LtermsStair/RtermsStair indices. flagEquiv's arbitrary
   middle is a Lean-side artifact; the matching convention is an ORDER-FREE middle claim.
4. **Spec (deliverable for N6/N7)**: middle clause of isPiv_stairR7, stated on the
   **staircase-frame projector** qM' M := (Tm' * M * Ti').submatrix flagEquiv' flagEquiv':
   `∀ i, 45 ≤ i → i < 484 → IsPiv (qM' M) i i`, with M = (1−x₁y₁) ⊗ₖ (1−x₂y₂).
   Discharged VERBATIM by Platform.isPiv_mid (m:=529, k:=45, generic in p — no transfer
   lemma for isPiv_mid itself): hk omega; hp = qM'_idem (r6 route
   nb_data_edge_solution.lean:524-526, label-shape-generic); hrank = 484 (Tm'/Ti'
   invertible since Nm'²=0, rank = rank(M) = 22·22); **hC = N6's corner-transfer identity**
   corner(qM' M) = stairCornerQOf M (analogue of qM_corner, :534-537) + stair_data_cert
   (N3, PROVED). Hypotheses needed: h₁ h₂ hdet only (staircase-frame hdet; hu/hv/hT NOT
   needed for the middle clause). Controls: 3 random label sets (y·x=1, hu/hv/hT≠0, stair
   corner rank 45): middle 439/439 in r6 frame — failure tracks hC failure exactly, as
   isPiv_mid predicts. The load-bearing lemma is N6's corner identity, nothing numeric.
