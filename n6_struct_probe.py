"""N6 structural probe (deliverable 3 input): which corner blocks are rank-one above the
diagonal in each frame?  Blocks are written B i gamma = corner[i][off+gamma]; the r6
`data_upper` shape is B i gamma = u_i * v_gamma for i < gamma (r6 control must give 0)."""
import json
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
n = 23
alZ, beZ = d['coeffs']['al'], d['coeffs']['be']
aZ, bZ = d['coeffs']['a'], d['coeffs']['b']


def Lz(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(alZ, (22, 0)), (beZ, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i - 22, i - 24))]
    return []


def Rz(j):
    if j < 20: return [(1, (j + 1, j + 3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(aZ[j - 22], (j - 22, j - 21)), (bZ[j - 22], (j - 21, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []


def Lr6(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(1, (22, 0)), (-1, (0, 22))]
    if i < 44: return [(1, (i - 23, i - 22))]
    if i == 44: return [(1, (22, 1)), (-1, (1, 22))]
    return []


def Rr6(j):
    if j < 21: return [(1, (j + 1, j))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(1, (j - 22, 22)), (1, (22, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []


def make_M(x1, y1, x2, y2):
    A1 = [[(1 if a == c else 0) - x1[a] * y1[c] for c in range(n)] for a in range(n)]
    A2 = [[(1 if a == c else 0) - x2[a] * y2[c] for c in range(n)] for a in range(n)]
    return {(a * n + b, c * n + e): A1[a][c] * A2[b][e]
            for a in range(n) for b in range(n) for c in range(n) for e in range(n)}


def corner_of(M, Lf, Rf):
    C = [[F(0)] * 45 for _ in range(45)]
    for i in range(45):
        for j in range(45):
            s = F(0)
            for cs, (a, b) in Lf(i):
                for ct, (c, e) in Rf(j):
                    s += cs * ct * M[(a * n + b, c * n + e)]
            C[i][j] = s
    return C


def rank1_bad(C, rows, gam, off):
    """#nonzero 2x2 minors of B i g = C[i][off+g]; only minors whose FOUR entries all lie in
    the identity region i < g (so i2 < g1 is the binding condition)."""
    bad = []
    for i1 in rows:
        for i2 in rows:
            if i2 <= i1: continue
            for g1 in gam:
                for g2 in gam:
                    if g2 <= g1: continue
                    if not (i2 < g1): continue
                    det = C[i1][off + g1] * C[i2][off + g2] - C[i1][off + g2] * C[i2][off + g1]
                    if det != 0: bad.append((i1, g1, i2, g2))
    return bad


x1 = [F(v) for v in d['labels']['x1']]
y1 = [F(v) for v in d['labels']['y1']]
x2 = [F(v) for v in d['labels']['x2']]
y2 = [F(v) for v in d['labels']['y2']]
M = make_M(x1, y1, x2, y2)
Cs = corner_of(M, Lz, Rz)
Cr6 = corner_of(M, Lr6, Rr6)

print('rank-one-above-diagonal probes (0 = the r6-style structure holds)')
for nm, C in (('r6-ctrl', Cr6), ('stair', Cs)):
    for label, rows, gam, off in (
            ('r6 run block  B i g = C[i][22+g], i,g in 1..21', list(range(1, 22)), list(range(1, 22)), 22),
            ('18-run block   B k g = C[25+k][2+g], k,g in 0..17', list(range(0, 18)), list(range(0, 18)), 2),
            ('anti block     B i g = C[i][44-i-?]', list(range(0, 23)), list(range(0, 23)), 0)):
        if off == 0:
            continue
        bad = rank1_bad(C, rows, gam, off)
        print(f'  [{nm}] {label}: {len(bad)} nonzero minors' + (f' e.g. {bad[:4]}' if bad else ''))
