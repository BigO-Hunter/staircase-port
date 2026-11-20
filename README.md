# staircase-port

Independent middle-run verification arm ("sp-midrun"): a port of the witness-1 staircase certificate, extracting the rightmost-pivot rank profile of the 529×529 elimination.
Construction: producer's own pivot identity (`check_stair.py:175`); port and double-prime rank verification (mod 1000000007 / 998244353, asserted equal) ours. AI-assisted (darkhipo swarm), disclosed.
Status: headline 437/439 middle positions verified at the witness (failures re-checked by direct submatrix elimination); corner clause proved at pre-verification merge. See `MIDRUN_REPORT.md`.

---

## Why this repo is up

Public verification evidence: an independent middle-run port of the witness-1 staircase certificate (437/439 positions double-prime verified) — cross-checks the primary receipt.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: the remaining corner positions at the witness; full middle-run arm completion; merging the double-prime verification into the primary receipt.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard.

## Recovery branches

See [RECOVERY.md](RECOVERY.md) for the private `recovery/` branches preserving the stage-two integrated local main and ten N-/composition recovery lanes. These are source branches with original history, not claims that every lane is complete.

