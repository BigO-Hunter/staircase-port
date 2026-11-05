#!/usr/bin/env python3
"""N3 timing prep: recompute the Z corner from cert_data.json (same formula as
extract_cert.py main) and report the argmax entry + worst row, so the kernel
decide timing tests target the heaviest cells. Read-only; prints JSON."""
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(HERE, 'out', 'cert_data.json')))
H = 23
pZ, xiZ, vZ, nuZ = d['labels']['x1'], d['labels']['y1'], d['labels']['x2'], d['labels']['y2']
alZ, beZ, aZ, bZ = d['coeffs']['al'], d['coeffs']['be'], d['coeffs']['a'], d['coeffs']['b']
RC = [tuple(c) for c in d['RC']]
CC = [tuple(c) for c in d['CC']]

# rows/cols dicts, same construction as extract_cert.py (design(23,'stair'))
rows = [{(b, b): 1} for b in range(H - 1)] + [{(H - 1, 0): alZ, (0, H - 1): beZ}] + \
       [{c: 1} for c in RC]
cols = [{c: 1} for c in CC] + [{(j, j + 1): aZ[j], (j + 1, j): bZ[j]} for j in range(H - 1)] + \
       [{(H - 1, H - 1): 1}]
assert len(rows) == len(cols) == 45, (len(rows), len(cols))

q1 = [[int(i == k) - pZ[i] * xiZ[k] for k in range(H)] for i in range(H)]
q2 = [[int(i == k) - vZ[i] * nuZ[k] for k in range(H)] for i in range(H)]
n = 2 * H - 1
CZ = [[0] * n for _ in range(n)]
for j, col in enumerate(cols):
    G = [[0] * H for _ in range(H)]
    for (a, b), val in col.items():
        G[a][b] = val
    qG = [[sum(q1[i][k] * G[k][l] for k in range(H)) for l in range(H)] for i in range(H)]
    Y = [[sum(qG[i][l] * q2[k][l] for l in range(H)) for k in range(H)] for i in range(H)]
    for i, row in enumerate(rows):
        CZ[i][j] = sum(val * Y[a][b] for (a, b), val in row.items())

# cross-check against the dumped certRows (CZ mod P)
P = d['certP']
assert [[x % P for x in r] for r in CZ] == d['certRows'], 'CZ mod P != certRows'
mxA = max(max(abs(x) for x in r) for r in CZ)
assert mxA == d['cornerZ_entry_sizes']['max_abs'], 'max_abs mismatch'
argmax = next((i, j) for i in range(n) for j in range(n) if abs(CZ[i][j]) == mxA)
rowcost = [(sum(len(str(abs(x))) for x in CZ[i]), i) for i in range(n)]
worstrow = max(rowcost)[1]
print(json.dumps(dict(
    max_abs=mxA, max_digits=len(str(mxA)), argmax=list(argmax),
    argmax_mod_P=CZ[argmax[0]][argmax[1]] % P,
    certRow_at_argmax=d['certRows'][argmax[0]][argmax[1]],
    worst_row=worstrow,
    top5_rows=sorted(rowcost, reverse=True)[:5],
    digits_hist={k: sum(1 for r in CZ for x in r if len(str(abs(x))) == k)
                 for k in sorted({len(str(abs(x))) for r in CZ for x in r})},
)))
