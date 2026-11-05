"""Spot-check: recompute A,B,C,D by direct submatrix elimination (exact mod p) at the two
failing middle positions (464, 483) and one passing position (100), natural order, and
compare with the pc-profile values in extract/out/midrun_r6frame.json."""
import json
import numpy as np
import midrun_lib as L

x1, y1, x2, y2, d = L.witness()
Q = L.qM_pair_coords(x1, y1, x2, y2)
flag = L.flag_order('natural')
p = L.P1
idx = [flag[u][0] * L.N + flag[u][1] for u in range(L.M529)]
Qm = np.array([[v % p for v in row] for row in Q], dtype=np.int64)[np.ix_(idx, idx)]

def rk_direct(X, Y):
    R = Qm[:X, Y:].copy()
    m, nn = R.shape
    r = 0
    for c in range(nn):
        col = np.nonzero(R[r:, c])[0]
        if col.size == 0: continue
        piv = r + int(col[0])
        R[[r, piv]] = R[[piv, r]]
        inv = pow(int(R[r, c]), p - 2, p)
        rows = [i for i in range(m) if i != r and R[i, c]]
        for i in rows:
            f = int(R[i, c]) * inv % p
            R[i] = (R[i] - f * R[r]) % p
        r += 1
        if r == m: break
    return r

o = json.load(open('extract/out/midrun_r6frame.json'))
mid = {m['i']: m for m in o['middle']}
ok = True
for i in (464, 483, 100, 45):
    A, B, C, D = (rk_direct(i, i), rk_direct(i + 1, i), rk_direct(i, i + 1), rk_direct(i + 1, i + 1))
    v = B + C == A + D + 1
    m = mid[i]
    match = (A, B, C, D) == (m['A'], m['B'], m['C'], m['D']) and v == m['ispiv']
    ok &= match
    print(f'i={i}: direct (A,B,C,D)=({A},{B},{C},{D}) IsPiv={v} | profile '
          f'({m["A"]},{m["B"]},{m["C"]},{m["D"]}) IsPiv={m["ispiv"]} | match={match}')
print('ALL MATCH' if ok else 'DISAGREEMENT')
