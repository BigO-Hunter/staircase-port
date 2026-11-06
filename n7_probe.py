"""N7 probe: validate the symbolic four-rank proof plan for the 39 corner positions.

Plan under test:
  run1 (l=1..21, corner pos (l,22+l), k=1): uppers A<=1,B<=2,C<=1,D<=1 (cuts/height/width);
    lowers B>=2 via 2x2 minor rows{0,l} x cols{22+l,44} det = hu*hv*dev_l; C>=1 via entry
    corner[0][44] = hu*hv.
  run2 (t=0..17, corner pos (25+t,2+t), k=25): uppers A<=25,B<=26,C<=25,D<=25;
    lowers B>=26 via 26x26 minor rows[0..24]+[25+t] x cols[2+t..27+t] (hM2);
    C>=25 via 25x25 minor rows[0..24] x cols[20..44] (hM1) + monotonicity.
Also: cut-table membership for every needed upper; dev_l != 0 at witness; cert-shape match.
"""
import json, random
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
n = 23
alZ, beZ = d['coeffs']['al'], d['coeffs']['be']
aZ, bZ = d['coeffs']['a'], d['coeffs']['b']
PR = [18446744073709551557, 18446744073709551533]

def Lterms(i):
    if i < 22: return [(F(1), (i, i))]
    if i == 22: return [(F(alZ), (22, 0)), (F(beZ), (0, 22))]
    if i == 23: return [(F(1), (0, 3))]
    if i < 45: return [(F(1), (i - 22, i - 24))]
    return []
def Rterms(j):
    if j < 20: return [(F(1), (j + 1, j + 3))]
    if j == 20: return [(F(1), (0, 20))]
    if j == 21: return [(F(1), (0, 21))]
    if j < 44: return [(F(aZ[j-22]), (j - 22, j - 21)), (F(bZ[j-22]), (j - 21, j - 22))]
    if j == 44: return [(F(1), (22, 22))]
    return []

def corner(x1, y1, x2, y2):
    A1 = [[(1 if a == c else 0) - x1[a] * y1[c] for c in range(n)] for a in range(n)]
    A2 = [[(1 if a == c else 0) - x2[a] * y2[c] for c in range(n)] for a in range(n)]
    M = lambda a, b, c, e: A1[a][c] * A2[b][e]
    C = [[sum(sl * M(a, b, c, e) * cl for sl, (a, b) in Lterms(i) for cl, (c, e) in Rterms(j))
          for j in range(45)] for i in range(45)]
    return C

def frac_mod(v, p):
    return (v.numerator % p) * pow(v.denominator % p, -1, p) % p

def rank_ne_mod(C, X, Y, p):
    rows = [[frac_mod(v, p) for v in C[r][Y:]] for r in range(min(X, 45))]
    rk = 0; m = len(rows[0]) if rows else 0
    for c in range(m):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], p - 2, p)
        rows[rk] = [(v * inv) % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(rows[i][j] - f * rows[rk][j]) % p for j in range(m)]
        rk += 1
    return rk

def ranks4(C, i, j):
    return [(rank_ne_mod(C, X, Y, p)) for (X, Y) in [(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)]
            for p in PR[:1]] , [(rank_ne_mod(C, X, Y, p)) for (X, Y) in [(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)] for p in PR[1:]]

def ranks4_2p(C, i, j):
    v1 = [rank_ne_mod(C, X, Y, PR[0]) for (X, Y) in [(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)]]
    v2 = [rank_ne_mod(C, X, Y, PR[1]) for (X, Y) in [(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)]]
    assert v1 == v2, (v1, v2)
    return v1

def det_mod(C, rows, cols, p):
    return None if False else __import__('functools').reduce(lambda a, b: a, [1])
def minor_det_mod(C, rl, cl, p):
    M = [[frac_mod(C[r][c], p) for c in cl] for r in rl]
    rk = 0; m = len(cl)
    for c in range(m):
        piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
        if piv is None: return 0
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [(v * inv) % p for v in M[rk]]
        for i in range(rk + 1, len(M)):
            if M[i][c]:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[rk][j]) % p for j in range(m)]
        rk += 1
    return 1  # nonsingular

# ---- cut table from NEBlocks.lean ----
import re
txt = open('StaircasePort/NEBlocks.lean').read()
m = re.search(r'def stairNEBlocks[^=]*:= \[(.*?)\]\n\ntheorem', txt, re.S)
cuts = {}
for tup in re.findall(r'\((\d+), (\d+), (\d+), (\d+)\)', m.group(1)):
    i, j, rho, cut = map(int, tup)
    cuts[(i, j)] = (rho, cut)

def upper_ok(X, Y, val):
    """is there a label-free upper bound rk(X,Y) <= val ?"""
    if X <= val: return True            # height
    if 45 - Y <= val and Y <= 45: return True  # width (Y <= 44)
    b = cuts.get((X - 1, Y))
    return b is not None and b[1] <= val

L = d['labels']
W = ( [F(v) for v in L['x1']], [F(v) for v in L['y1']], [F(v) for v in L['x2']], [F(v) for v in L['y2']] )

def dev(l, x1, y1, x2, y2):
    return F(aZ[l]) * x2[l] * y2[l+1] + F(bZ[l]) * x1[l] * y1[l+1]

def hu_of(x1, x2): return x1[0] * x2[0]
def hv_of(y1, y2): return y1[22] * y2[22]

print("=== witness ===")
C = corner(*W)
hu, hv = hu_of(W[0], W[2]), hv_of(W[1], W[3])
print("hu != 0:", hu != 0, " hv != 0:", hv != 0)
devs = [dev(l, *W) for l in range(1, 22)]
print("all dev_l != 0 (l=1..21):", all(v != 0 for v in devs), " min |dev|:", min(abs(v) for v in devs))
# entry identities at witness
for l in [1, 7, 21]:
    v = F(aZ[l]) * W[2][l] * W[3][l+1] + F(bZ[l]) * W[0][l] * W[1][l+1]
    assert C[0][22+l] == hu * (F(aZ[l]) * W[1][l] * W[3][l+1] + F(bZ[l]) * W[1][l+1] * W[3][l]) , l
    assert C[l][44] == (W[0][l] * W[2][l]) * hv, l
    assert C[0][44] == hu * hv
    assert C[l][22+l] == (W[0][l] * W[2][l]) * (F(aZ[l]) * W[1][l] * W[3][l+1] + F(bZ[l]) * W[1][l+1] * W[3][l]) - v, l
print("entry identities E1-E4 at witness: OK")
# 2x2 minor det == hu*hv*dev_l
for l in [1, 5, 21]:
    det2 = C[0][22+l] * C[l][44] - C[0][44] * C[l][22+l]
    assert det2 == hu * hv * dev(l, *W), l
print("2x2 minor det == hu*hv*dev_l: OK")

ok = True
for l in range(1, 22):
    A, B, Cc, D = ranks4_2p(C, l, 22 + l)
    okk = (A, B, Cc, D) == (1, 2, 1, 1)
    up = all(upper_ok(*xy, v) for xy, v in [((l, 22+l), 1), ((l+1, 22+l), 2), ((l, 23+l), 1), ((l+1, 23+l), 1)])
    if not (okk and up): print("run1 FAIL l=", l, (A, B, Cc, D), "uppers:", up); ok = False
print("run1 four-rank (1,2,1,1) + uppers for l=1..21:", ok)

ok = True
for t in range(18):
    A, B, Cc, D = ranks4_2p(C, 25 + t, 2 + t)
    okk = (A, B, Cc, D) == (25, 26, 25, 25)
    up = all(upper_ok(*xy, v) for xy, v in [((25+t, 2+t), 25), ((26+t, 2+t), 26), ((25+t, 3+t), 25), ((26+t, 3+t), 25)])
    if not (okk and up): print("run2 FAIL t=", t, (A, B, Cc, D), "uppers:", up); ok = False
print("run2 four-rank (25,26,25,25) + uppers for t=0..17:", ok)

# hM1 / hM2 minors nonsingular at witness
rl1 = list(range(25)); cl1 = list(range(20, 45))
print("hM1 minor nonsingular (both primes):",
      all(minor_det_mod(C, rl1, cl1, p) for p in PR))
okm = True
for t in range(18):
    rl = list(range(25)) + [25 + t]; cl = list(range(2 + t, 28 + t))
    if not all(minor_det_mod(C, rl, cl, p) for p in PR):
        print("hM2 FAIL t=", t); okm = False
print("hM2 minors nonsingular t=0..17:", okm)

# cert shape match: n2c certs 7..24 rows/cols
certs = re.findall(r'def n2cR(\d+) : List ℕ := \[([0-9, ]*)\]\ndef n2cC\1 : List ℕ := \[([0-9, ]*)\]', open('StaircasePort/Pivot.lean').read())
cd = {int(idx): (rl.strip(), cl.strip()) for idx, rl, cl in certs}
match = {}
for idx in range(7, 25):
    rl = [int(v) for v in cd[idx][0].split(',')]; cl = [int(v) for v in cd[idx][1].split(',')]
    if len(rl) == 26 and len(cl) == 26 and rl[:25] == list(range(25)):
        t = rl[25] - 25
        if cl == list(range(2 + t, 28 + t)): match[t] = idx
print("cert t->index map (expect all 0..17):", sorted(match.items())[:20], "count", len(match))

print()
print("=== random labels ===")
def rand_labels(seed):
    rnd = random.Random(seed)
    x1 = [F(rnd.randint(-40, 40)) for _ in range(n)]
    y1 = [F(rnd.randint(-40, 40)) for _ in range(n)]
    x2 = [F(rnd.randint(-40, 40)) for _ in range(n)]
    y2 = [F(rnd.randint(-40, 40)) for _ in range(n)]
    x1[0] = F(0) if x1[0] == 0 else x1[0]; x2[0] = F(3) if x2[0] == 0 else x2[0]
    # y.x = 1: y1[0] := (1 - sum_{c>0} y1[c] x1[c]) / x1[0]
    def fix(y, x):
        s = sum(y[c] * x[c] for c in range(1, n))
        y[0] = (F(1) - s) / x[0]
    fix(y1, x1); fix(y2, x2)
    return x1, y1, x2, y2

allsame1 = allsame2 = True
for seed in range(6):
    x1, y1, x2, y2 = rand_labels(seed)
    if hu_of(x1, x2) == 0 or hv_of(y1, y2) == 0: continue
    if any(dev(l, x1, y1, x2, y2) == 0 for l in range(1, 22)): continue
    Cr = corner(x1, y1, x2, y2)
    bad = []
    for l in range(1, 22):
        A, B, Cc, D = ranks4_2p(Cr, l, 22 + l)
        if (A, B, Cc, D) != (1, 2, 1, 1): bad.append((l, (A, B, Cc, D)))
    for t in range(18):
        A, B, Cc, D = ranks4_2p(Cr, 25 + t, 2 + t)
        if (A, B, Cc, D) != (25, 26, 25, 25): bad.append((25 + t, (A, B, Cc, D)))
    if bad: print("seed", seed, "rank deviations:", bad); allsame1 = False
    # hM1/hM2 nonsingular
    if not all(minor_det_mod(Cr, rl1, cl1, p) for p in PR): print("seed", seed, "hM1 singular!"); allsame2 = False
    for t in range(18):
        rl = list(range(25)) + [25 + t]; cl = list(range(2 + t, 28 + t))
        if not all(minor_det_mod(Cr, rl, cl, p) for p in PR):
            print("seed", seed, "hM2 singular t=", t); allsame2 = False
print("random labels: four-rank values constant:", allsame1, "; M1/M2 minors nonsingular:", allsame2)
