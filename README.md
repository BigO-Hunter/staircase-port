# staircase-port

Independent Lean verification of the **witness-1 staircase certificate** — round 7 of the
Kappa-framework integer-multiplication formalization (529×529 elimination, W = 108516254).
The port extracts the rightmost-pivot rank profile of the elimination and re-verifies it
independently of the certificate's producer. AI-assisted; disclosed.

**Result.** 437/439 middle positions double-prime verified at the witness (ranks computed
mod 1000000007 and mod 998244353, asserted equal; the two failures re-checked by direct
submatrix elimination). The 39-position corner clause is proved symbolically
(`isPiv_stairCorner`, hypothesis-shaped for composition). The middle clause is order-free:
no middle elimination order exists producer-side, and the r6-frame middle run is
order-dependent — every order fails at position 483. Full verdicts:
[MIDRUN_REPORT.md](MIDRUN_REPORT.md).

**Board state.** The staircase certificate is an independent result, not a
[Big O Speedrun](https://bigospeedrun.com) race (board fetched 2026-11-26). This repo is a
verification arm: independence from the producer is the value. It cross-checks the primary
receipt; it claims no new bound.

## Contents

| path | what |
|---|---|
| `StaircasePort/` | the port: Data, Cert, Nonvan, Pivot, Signature, Corner, Projector, Rewire, D2 (QHNet dataset), Top |
| `Definitions/` | platform r6/r8 vocabulary (import closure; bodies as upstream, provenance headers only) |
| `Theorems/` | round-7 framework theorem |
| `ref/` | fetched platform solution bodies + the r7 formal statement (provenance) |
| `extract/` | Python extraction/verification tooling; `extract/out/` holds the data receipts (JSON) |
| `SCAFFOLD.md` | proof skeleton: N-item map, proof routes, gotchas, per-item findings |
| `MIDRUN_REPORT.md` | independent middle-run verdicts |
| `RECOVERY.md` | index of preserved source branches (unfinished items, original history) |
| root `n*.lean`, `n*_axcheck.lean`, `*_probe.py`, `midrun_*.py` | probes, axiom audits, certificate generators used during the port |

## Reproduce / verify

Lean (toolchain `leanprover/lean4:v4.34.1`, Mathlib pinned in `lake-manifest.json`):

```sh
lake build StaircasePort          # ~9000 jobs; CI runs this on every push — allow hours
lake env lean n7_axcheck.lean     # axiom audit: expect [propext, Classical.choice, Quot.sound], no sorryAx
```

Python middle-run (stdlib only, run from the repo root; reads the vendored
`extract/out/cert_data.json`, writes the `extract/out/midrun_*.json` receipts):

```sh
python3 midrun_r6frame.py         # 439 middle positions, two primes
python3 midrun_orders.py          # order-dependence: 4 orders × 2 primes
python3 midrun_spotcheck.py       # direct submatrix elimination of the failing blocks
python3 extract/gen_lean_data.py  # regenerate CertData.lean / NEBlocks.lean from the receipts
```

External inputs (not vendored): the `extract/extract_*.py`, `d2_*.py` and
`verify_n2b_statement.py` scripts need the producer chain (`check_stair.py`, `deferred.py`,
`certificate_round7.py`, frozen witness JSONs) on `extract/jainroot/` (gitignored);
`extract/fetch_statements.py` needs prove2.me credentials in `$PROVE2ME_WORKSPACE`.
The committed `extract/out/` receipts are the verifiable artifacts of those runs.

## Next steps

1. **Composition** — integrate the proved corner clause into the flag-basis chain:
   `recovery/sp-compose` has the surgery complete in source; the integration gate is unfinished.
2. **Middle-run completion** — the remaining corner positions at the witness; merge the
   double-prime verification into the primary receipt.
3. **Stage-2 formalok port** — `recovery/stage2`: FormalCalc/DenseProg/LabGen/PackCore proved;
   the chain is blocked on the Rec derivation (audit in that branch's SCAFFOLD).
4. **Platform stubs** — `Platform.isPiv_mid` etc. are documented sorries (the intended proof
   channel); discharge them by importing the platform's proved children (ids in `Pivot.lean`).

See `SCAFFOLD.md` for the full N-item map, proof routes, and banked gotchas before starting.

## Recovery branches

[RECOVERY.md](RECOVERY.md) indexes the `recovery/` branches preserving unfinished source
items with original history. They are source branches, not claims that every item is
complete; do not fast-forward main from them without a fresh proof-tree merge and build.

## License

[Copy-Free/Stays-Free (CFSF)](LICENSE) — copy-free (use for any purpose) and stays-free
(nobody may fence this work).

[BigO-Hunter](https://github.com/BigO-Hunter) is the tracking & packaging org for
contributions toward [Big O Speedrun](https://bigospeedrun.com).
Org story: [profile](https://github.com/BigO-Hunter/.github) ·
[bigo-hunter.github.io](https://bigo-hunter.github.io).
