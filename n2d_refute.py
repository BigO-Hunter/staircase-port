"""N2d refutation: isPiv_stair_lower as scaffolded is FALSE at the staircase witness.

Evidence chain (all exact, integer arithmetic reduced mod two primes; cross-checked):
  1. The top-right 45x45 corner of Defs4's qM M is `cor M` in the r6 frame
     (platform lemma qM_corner, consumed verbatim by the r6 data_edge proof).
  2. The staircase frame (Cert.lean corStairQ / stairCornerQOf) is a DIFFERENT matrix.
  3. At the extracted staircase witness labels, hdet (staircase frame) holds, but qM M's
     actual corner has rank 44 and 18 of the 39 corner positions claimed by
     `stairDataRuns 23 529` are NOT pivots.
"""
import json

d = json.load(open('extract/out/cert_data.json'))
L = d['labels']
n = 23
x1, y1, x2, y2 = L['x1'], L['y1'], L['x2'], L['y2']

print('hypotheses at the witness:')
print('  h1  y1.x1      =', sum(a*b for a, b in zip(y1, x1)))
print('  h2  y2.x2      =', sum(a*b for a, b in zip(y2, x2)))
print('  hu  x1[0]*x2[0]=', x1[0], '*', x2[0], '=', x1[0]*x2[0])
print('  hv  y1[22]*y2[22]=', y1[22], '*', y2[22], '=', y1[22]*y2[22])
hT = [(l, x1[l]*y1[22] + x2[l]*y2[22]) for l in range(1, 22)]
print('  hT  l=1..21 all nonzero:', all(v != 0 for _, v in hT), 'min|v|=', min(abs(v) for _, v in hT))

def P(a, b):
    return a * n + b

A1 = [[(1 if a == c else 0) - x1[a]*y1[c] for c in range(n)] for a in range(n)]
A2 = [[(1 if a == c else 0) - x2[a]*y2[c] for c in range(n)] for a in range(n)]
M = [[0]*(n*n) for _ in range(n*n)]
for a in range(n):
    for b in range(n):
        for c in range(n):
            for e in range(n):
                M[P(a, b)][P(c, e)] = A1[a][c] * A2[b][e]

def Lterms(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(1, (22, 0)), (-1, (0, 22))]
    if i < 44: return [(1, (i-23, i-22))]
    return [(1, (22, 1)), (-1, (1, 22))]

def Rterms(j):
    if j < 21: return [(1, (j+1, j))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(1, (j-22, 22)), (1, (22, j-22))]
    return [(1, (22, 22))]

def cor_of(Lt, Rt):
    C = [[0]*45 for _ in range(45)]
    for i in range(45):
        for j in range(45):
            s = 0
            for cs, (a, b) in Lt(i):
                for ct, (c, e) in Rt(j):
                    s += cs * ct * M[P(a, b)][P(c, e)]
            C[i][j] = s
    return C

def rank_mod(C, rows, cols, p):
    R = [[C[i][j] % p for j in cols] for i in rows]
    m, nn = len(R), (len(R[0]) if R else 0)
    r = 0
    for c in range(nn):
        piv = next((i for i in range(r, m) if R[i][c] % p), None)
        if piv is None: continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c], p-2, p)
        for i in range(m):
            if i != r and R[i][c]:
                f = R[i][c]*inv % p
                R[i] = [(R[i][j]-f*R[r][j]) % p for j in range(nn)]
        r += 1
        if r == m: break
    return r

C = cor_of(Lterms, Rterms)
primes = (1000000007, 998244353)
prof = {}
for p in primes:
    prof[p] = {(X, Y): rank_mod(C, range(X), range(Y, 45), p) for X in range(46) for Y in range(46)}
assert prof[primes[0]] == prof[primes[1]]
Rk = prof[primes[0]]
print('\nr6-frame corner rank =', Rk[(45, 0)])

def ispiv(R, i, j):
    return R[(i+1, j)] + R[(i, j+1)] == R[(i, j)] + R[(i+1, j+1)] + 1

claimed_corner = [(i, j-484) for (i, j) in
                  [(a+k, b+k) for (a, b, r) in [(45, 45, 439), (1, 507, 21), (25, 486, 18)] for k in range(r)]
                  if i < 45]
fails = [t for t in claimed_corner if not ispiv(Rk, *t)]
passes = [t for t in claimed_corner if ispiv(Rk, *t)]
print('claimed corner positions:', len(claimed_corner), ' pivot failures:', len(fails))
print('  failing positions (i, corner-col):', fails)
print('  failing == the added staircase run (25,486,18) lifted:', 
      sorted(t[0] for t in fails) == list(range(25, 43)))
print('  old r6 corner run (1,507,21) positions all pivots:',
      all(ispiv(Rk, i, 22+i) for i in range(1, 22)))

# ---- middle run with an explicit (arbitrary) ordering of the 439 unclaimed pairs ----
aL = set()
for i in range(45):
    if i < 22: aL.add((i, i))
    elif i == 22: aL |= {(22, 0), (0, 22)}
    elif i < 44: aL.add((i-23, i-22))
    else: aL |= {(22, 1), (1, 22)}
bL = set()
for j in range(45):
    if j < 21: bL.add((j+1, j))
    elif j == 21: bL.add((0, 21))
    elif j < 44: bL |= {(j-22, 22), (22, j-22)}
    else: bL.add((22, 22))
rest = [P(a, b) for a in range(n) for b in range(n) if (a, b) not in aL and (a, b) not in bL]
print('\n|aL|=', len(aL), '|bL|=', len(bL), '|rest|=', len(rest))

def rank_arb(rowsets, colsets, p):
    ixr = [P(a, b) for a, b in rowsets]
    ixc = [P(a, b) for a, b in colsets]
    R = [[M[i][j] % p for j in ixc] for i in ixr]
    m, nn = len(R), (len(R[0]) if R else 0)
    r = 0
    for c in range(nn):
        piv = next((i for i in range(r, m) if R[i][c] % p), None)
        if piv is None: continue
        R[r], R[piv] = R[piv], R[r]
        inv = pow(R[r][c], p-2, p)
        for i in range(m):
            if i != r and R[i][c]:
                f = R[i][c]*inv % p
                R[i] = [(R[i][j]-f*R[r][j]) % p for j in range(nn)]
        r += 1
        if r == m: break
    return r

# rank of a NE block of (Tm M Ti) restricted to pair sets (flagEquiv only permutes)
def rk_pair(X, Y, p):
    # rows: first 45 flag positions = aL list order, then rest[:X-45]
    rows = [(i, i) if i < 22 else None for i in range(0)]
    rs = []
    for i in range(min(X, 45)):
        rs.extend(Lterms(i) and [] or [])
    # explicit aL sequence
    aLseq = []
    for i in range(45):
        if i < 22: aLseq.append((i, i))
        elif i == 22: aLseq += [(22, 0), (0, 22)]
        elif i < 44: aLseq.append((i-23, i-22))
        else: aLseq += [(22, 1), (1, 22)]
    bLseq = []
    for j in range(45):
        if j < 21: bLseq.append((j+1, j))
        elif j == 21: bLseq.append((0, 21))
        elif j < 44: bLseq += [(j-22, 22), (22, j-22)]
        else: bLseq.append((22, 22))
    rowset = aLseq[:X] + [divmod(x, n) for x in rest[:max(0, X-45)]]
    # cols >= Y: last 45 are bL; middle block occupies flag positions 45..484
    if Y <= 45:
        colset = [divmod(x, n) for x in rest[45-Y:]] + bLseq
    else:
        colset = [divmod(x, n) for x in rest[45-Y+45:]] + bLseq
    return rank_arb(rowset, colset, p)

p = primes[0]
mid = [(i, i) for i in range(45, 484)]
mids = {}
for (i, j) in [(45, 45), (46, 45), (45, 46), (46, 46), (100, 100), (483, 483), (200, 201)]:
    mids[(i, j)] = rk_pair(i, j, p)
print('middle-run ranks (sample):', mids)
A = mids[(45, 45)]; B = mids[(46, 45)]; Cc = mids[(45, 46)]; D = mids[(46, 46)]
print('IsPiv at (45,45):', A, B, Cc, D, '->', B + Cc == A + D + 1)
bad_mid = []
for i in mid:
    a = rk_pair(i, i, p); b = rk_pair(i+1, i, p); c = rk_pair(i, i+1, p); dd = rk_pair(i+1, i+1, p)
    if b + c != a + dd + 1:
        bad_mid.append(i)
print('middle-run positions failing (with one concrete flagEquiv ordering):', len(bad_mid), bad_mid[:12])
