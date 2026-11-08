# staircase-port

Independent middle-run verification arm ("sp-midrun"): a port of the witness-1 staircase certificate, extracting the rightmost-pivot rank profile of the 529×529 elimination.
Construction: producer's own pivot identity (`check_stair.py:175`); port and double-prime rank verification (mod 1000000007 / 998244353, asserted equal) ours. AI-assisted (darkhipo swarm), disclosed.
Status: headline 437/439 middle positions verified at the witness (failures re-checked by direct submatrix elimination); corner clause proved at pre-verification merge. See `MIDRUN_REPORT.md`.
