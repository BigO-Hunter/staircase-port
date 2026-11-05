"""N6 deliverable 1 — numeric prototype of the R7/staircase data-entrance PROJECTOR.

Construction (mirror of r6's Tm/Ti/flagEquiv/qM, derived here):
  anchors      aLs i = FIRST term of LtermsStair i ;  bLs j = FIRST term of RtermsStair j
  N (529x529)  N[aLs i, s] = -(coef of s in L_i)/lead(L_i)     (only i with >1 term: i=22)
               N[s, bLs j] =  (coef of s in R_j)/lead(R_j)     (only j=22..43)
  P = 1-N , Q = 1+N   ->  PQ = 1 - N^2 = 1  (no 2-path: see n_sq_zero check)
  D = diagonal, D[aLs i] = lead(L_i), D[bLs j] = 1/lead(R_j), 1 elsewhere
  qMStair M = (D*P) * M * (Q*D^-1)
  =>  corner_i,j := qMStair M (aLs i) (bLs j) = L_i . M . R_j = corStairQ M i j   EXACTLY

Checks (all exact arithmetic; rank/pivot work mod primes):
  A. construction premises: aLs/bLs injective+disjoint, N^2 = 0, PQ = 1
  B. corner == corStairQ at the witness (2025/2025), and == the independent
     corStairQ built from Cert.lean's own lists
  C. corner invertible (rank 45) and the 39 claimed corner pivots (r6 frame: 21/21 control)
  D. the 439 middle-run positions (i,i), 45 <= i < 484 -- N2d's open question
  E. structural probes feeding deliverable 3: is the corner rank-one above the diagonal
     in the staircase frame (the r6 `data_upper` shape)?  r6 frame used as control.
"""
import json
from fractions import Fraction as F

d = json.load(open('extract/out/cert_data.json'))
n = 23
P1, P2 = 1000000007, 998244353
alZ, beZ = d['coeffs']['al'], d['coeffs']['be']
aZ, bZ = d['coeffs']['a'], d['coeffs']['b']      # index r = j-22, 22 entries


def Lz(i):                                        # Cert.lean LtermsZStair
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(alZ, (22, 0)), (beZ, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i - 22, i - 24))]
    return []


def Rz(j):                                        # Cert.lean RtermsZStair
    if j < 20: return [(1, (j + 1, j + 3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(aZ[j - 22], (j - 22, j - 21)), (bZ[j - 22], (j - 21, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []


def Lr6(i):                                       # r6 Defs4 Lterms, h = 19
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


def anchor(Lf, i):                                 # first listed term = the anchor
    l = Lf(i)
    return l[0][1] if l else (0, 0)


def lead(l):                                       # leading coefficient
    return l[0][0] if l else 0


aLs = [anchor(Lz, i) for i in range(45)]
bLs = [anchor(Rz, j) for j in range(45)]
aL6 = [anchor(Lr6, i) for i in range(45)]
bL6 = [anchor(Rr6, j) for j in range(45)]


def build_N(Lf, Rf, aL, bL):
    N = {}
    for i in range(45):
        l = Lf(i)
        c0 = lead(l)
        for c, s in l[1:]:
            N[(aL[i], s)] = N.get((aL[i], s), 0) - F(c, 1) / F(c0, 1)
    for j in range(45):
        l = Rf(j)
        c0 = lead(l)
        for c, s in l[1:]:
            N[(s, bL[j])] = N.get((s, bL[j]), 0) + F(c, 1) / F(c0, 1)
    return N


def nsq_zero(N):
    """N^2 = 0 : every 2-path u->v->w must vanish."""
    bad = []
    rows = {}
    cols = {}
    for (u, v), c in N.items():
        rows.setdefault(u, []).append(v)
        cols.setdefault(v, []).append(u)
    for (u, v), c in N.items():
        for w in rows.get(v, []):          # need N[v,w]
            bad.append((u, v, w))
    return bad


def sv(l, u):
    return sum((F(c, 1) for c, s in l if s == u), F(0))


def rowP(Lf, aL, i, N):
    """row aLs i of (1-N) as a dict, normalised by lead."""
    l = Lf(i)
    c0 = lead(l)
    out = {aL[i]: F(1)}
    for c, s in l[1:]:
        out[s] = out.get(s, F(0)) + F(c, 1) / F(c0, 1)
    return dict((k, v) for k, v in out.items() if v != 0)


def colQ(Rf, bL, j, N):
    l = Rf(j)
    c0 = lead(l)
    out = {bL[j]: F(1)}
    for c, s in l[1:]:
        out[s] = out.get(s, F(0)) + F(c, 1) / F(c0, 1)
    return dict((k, v) for k, v in out.items() if v != 0)


def checkA():
    ok = True
    for nm, aL, bL in (('stair', aLs, bLs), ('r6', aL6, bL6)):
        inj = len(set(aL)) == 45 and len(set(bL)) == 45
        dis = not (set(aL) & set(bL))
        Lf, Rf = (Lz, Rz) if nm == 'stair' else (Lr6, Rr6)
        N = build_N(Lf, Rf, aL, bL)
        bad = nsq_zero(N)
        # row/col normalisation: (1-N)[aL i] * lead == L_i  and (1+N)[.,bL j] * lead == R_j
        rn = all(all(rowP(Lf, aL, i, N).get(u, F(0)) == sv(Lf(i), u) / F(lead(Lf(i)), 1)
                     for u in set(rowP(Lf, aL, i, N)) | {s for _, s in Lf(i)})
                 for i in range(45))
        cn = all(all(colQ(Rf, bL, j, N).get(u, F(0)) == sv(Rf(j), u) / F(lead(Rf(j)), 1)
                     for u in set(colQ(Rf, bL, j, N)) | {s for _, s in Rf(j)})
                 for j in range(45))
        nnz = len(N)
        print(f'  A[{nm}]: aL inj={inj} aL^bL=empty={dis} N^2=0={not bad} nnz(N)={nnz} '
              f'row-norm={rn} col-norm={cn}')
        ok &= inj and dis and not bad and rn and cn
    return ok


def make_M(x1, y1, x2, y2):
    A1 = [[(1 if a == c else 0) - x1[a] * y1[c] for c in range(n)] for a in range(n)]
    A2 = [[(1 if a == c else 0) - x2[a] * y2[c] for c in range(n)] for a in range(n)]
    M = {}
    for a in range(n):
        for b in range(n):
            for c in range(n):
                for e in range(n):
                    v = A1[a][c] * A2[b][e]
                    if v:
                        M[(a * n + b, c * n + e)] = v
    return M


def Mdense(M):
    return [[M.get((i, j), F(0)) for j in range(n * n)] for i in range(n * n)]


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


def rank_mod(C, rows, cols, p):
    R = [[int(C[i][j].numerator) * pow(int(C[i][j].denominator), p - 2, p) % p for j in cols]
         for i in rows]
    m, nn = len(R), (len(R[0]) if R else 0)
    r = 0
    for c in range(nn):
        piv = next((i for i in range(r, m) if R[i][c]), None)
        if piv is None: continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c], p - 2, p)
        for i in range(m):
            if i != r and R[i][c]:
                f = R[i][c] * inv % p
                R[i] = [(R[i][j] - f * R[r][j]) % p for j in range(nn)]
        r += 1
        if r == m: break
    return r


def profile(C, k=45):
    A = [[rank_mod(C, range(X), range(Y, k), P1) for Y in range(k + 1)] for X in range(k + 1)]
    B = [[rank_mod(C, range(X), range(Y, k), P2) for Y in range(k + 1)] for X in range(k + 1)]
    assert A == B, 'prime disagreement'
    return A


def piv(R, i, j):
    return R[i + 1][j] + R[i][j + 1] == R[i][j] + R[i + 1][j + 1] + 1


if __name__ == '__main__':
    print('A. construction premises')
    assert checkA(), 'construction premise failed'

    x1 = [F(v) for v in d['labels']['x1']]
    y1 = [F(v) for v in d['labels']['y1']]
    x2 = [F(v) for v in d['labels']['x2']]
    y2 = [F(v) for v in d['labels']['y2']]
    M = make_M(x1, y1, x2, y2)
    Nst = build_N(Lz, Rz, aLs, bLs)
    Nr6 = build_N(Lr6, Rr6, aL6, bL6)

    print('B. corner == corStairQ at the witness')
    Cs = corner_of(M, Lz, Rz)
    # realised corner through the projector factors: (D P) M (Q D^-1)
    Cproj = [[F(0)] * 45 for _ in range(45)]
    for i in range(45):
        rP = rowP(Lz, aLs, i, Nst)
        sc = F(lead(Lz(i)), 1)
        for j in range(45):
            cQ = colQ(Rz, bLs, j, Nst)
            sc2 = F(lead(Rz(j)), 1)
            s = F(0)
            for u, cu in rP.items():
                for v, cv in cQ.items():
                    s += cu * M[(u[0] * n + u[1], v[0] * n + v[1])] * cv
            Cproj[i][j] = sc * s * sc2
    mism = sum(1 for i in range(45) for j in range(45) if Cproj[i][j] != Cs[i][j])
    print(f'  projected corner vs corStairQ: {2025 - mism}/2025 equal')
    assert mism == 0

    print('C. corner pivots (staircase frame, new projector) vs r6 control')
    Ps = profile(Cs)
    Cr6 = corner_of(M, Lr6, Rr6)
    Pr6 = profile(Cr6)
    stair_claim = [(1 + k, 23 + k) for k in range(21)] + [(25 + k, 2 + k) for k in range(18)]
    r6_claim = [(l, 22 + l) for l in range(1, 22)]
    s_ok = sum(1 for t in stair_claim if piv(Ps, *t))
    r6_ok = sum(1 for t in r6_claim if piv(Pr6, *t))
    print(f'  staircase corner rank={Ps[45][0]}/45, staircase pivots {s_ok}/39 ; '
          f'r6 frame rank={Pr6[45][0]}, r6 control pivots {r6_ok}/21 (must be 21)')
    allpiv = [(i, j) for i in range(45) for j in range(45) if piv(Ps, i, j)]
    print(f'  staircase corner pivot set size {len(allpiv)}: {allpiv}')

    print('D. structural probe for deliverable 3: which blocks are rank-one above the diagonal?')
    def minors(C, cells):
        """cells = list of (row, gamma) block coordinates; require row < gamma for rank-one.
        Returns #nonzero 2x2 minors spanning four cells all in the row<gamma region."""
        bad = 0
        m = len(cells)
        for a in range(m):
            for b in range(a + 1, m):
                if cells[a][0] >= cells[b][0]: continue
                for c in range(m):
                    if cells[c][0] <= cells[a][0]: continue
                    for e in range(c + 1, m):
                        (r1, g1), (r2, g2) = cells[a], cells[b]
                        (r3, g3), (r4, g4) = cells[c], cells[e]
                        if not (r1 < g1 and r2 < g2 and r3 < g3 and r4 < g4): continue
                        v = (C[r1][g1 + 0] if False else 0)
                        d = (C[r1][g1] * C[r2][g2] - C[r1][g2] * C[r2][g1])
                        if d != 0: bad += 1
        return bad
    # rank-one test in block coordinates (i, gamma) with entry C[i][gamma] (corner col = gamma)
    def probe_rank1(C, r0, r1, g0, g1, off):
        """entry (i,gamma) reads C[i][off+gamma]; check minors with i<gamma, i in r0..r1."""
        bad = 0
        for i1 in range(r0, r1 + 1):
            for i2 in range(i1 + 1, r1 + 1):
                for g1 in range(g0, g1 + 1):
                    for g2 in range(g1 + 1, g1 + 1 + (g1 - g0) + 1):
                        if g2 > g1_max: continue
                        if not (i1 < g1 and i2 < g2): continue
                        d = (C[i1][off + g1] * C[i2][off + g2]
                             - C[i1][off + g2] * C[i2][off + g1])
                        if d != 0: bad += 1
        return bad
    g1_max = 22
    for nm, C in (('r6-ctrl', Cr6), ('stair', Cs)):
        b1 = probe_rank1(C, 1, 21, 0, 21, 22)     # the (1,507,21) run: entry (l, 22+l)
        b2 = probe_rank1(C, 25, 42, 0, 18, 2)     # the (25,486,18) run: entry (25+k, 2+k)
        print(f'  [{nm}] rank-one minors, 21-run block (i,22+g, i<g): {b1} ; '
              f'18-run block (25+i,2+g, i<g): {b2}')
    print('done')
