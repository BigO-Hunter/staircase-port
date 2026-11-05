"""N2c certificate search: pick a small set of minors (rows x cols) such that for every
IsPiv position i (j = pc_i, k = rho(i,j)) some minor of size k+1 lies in block (i+1,j) and
some minor of size k lies in block (i,j+1), each with det != 0 mod stairCertP.
Also verifies the upper-bound targets against stairNEBlocks."""
import json, re, itertools, random

P = 67108859
d = json.load(open('extract/out/cert_data.json'))
L = d['labels']; C = d['coeffs']
x1, y1, x2, y2 = L['x1'], L['y1'], L['x2'], L['y2']
al, be, a, b = C['al'], C['be'], C['a'], C['b']

def Lterms(i):
    if i < 22: return [(1, (i, i))]
    if i == 22: return [(al, (22, 0)), (be, (0, 22))]
    if i == 23: return [(1, (0, 3))]
    if i < 45: return [(1, (i - 22, i - 24))]
    return []
def Rterms(j):
    if j < 20: return [(1, (j + 1, j + 3))]
    if j == 20: return [(1, (0, 20))]
    if j == 21: return [(1, (0, 21))]
    if j < 44: return [(a[j - 22], (j - 22, j - 21)), (b[j - 22], (j - 21, j - 22))]
    if j == 44: return [(1, (22, 22))]
    return []
def MZ(u, v):
    return ((int(u[0] == v[0]) - x1[u[0]] * y1[v[0]])
            * (int(u[1] == v[1]) - x2[u[1]] * y2[v[1]]))
Q = [[sum((sum(sl * MZ(ss, tt) for (sl, ss) in Lterms(i))) * cl
          for (cl, tt) in Rterms(j)) for j in range(45)] for i in range(45)]
pc = [44] + [22 + k for k in range(1, 22)] + [22, 21, 20] + [k for k in range(2, 20)] + [1, 0]
n = 45
def rho(X, Y): return sum(1 for r in range(X) if pc[r] >= Y)

def det_mod(R, Cc, p=P):
    S = [[Q[r][c] % p for c in Cc] for r in R]; nn = len(S); det = 1
    for c in range(nn):
        piv = None
        for r in range(c, nn):
            if S[r][c] % p: piv = r; break
        if piv is None: return 0
        if piv != c: S[c], S[piv] = S[piv], S[c]; det = -det
        det = det * S[c][c] % p
        inv = pow(S[c][c], p - 2, p)
        for r in range(c + 1, nn):
            f = S[r][c] * inv % p
            if f: S[r] = [(S[r][k] - f * S[c][k]) % p for k in range(nn)]
    return det % p

# ---------- needed blocks: B (i+1,pc_i) target k+1 ; C (i,pc_i+1) target k ----------
needB, needC = [], []
for i in range(n):
    j = pc[i]; k = rho(i, j)
    needB.append((i + 1, j, k + 1))
    if k: needC.append((i, j + 1, k))

def covers(minor, X, Y):
    R, Cc = minor
    return len(R) == 1 or True  # placeholder
def ok(minor, X, Y, t):
    R, Cc = minor
    return len(R) == t and max(R) < X and min(Cc) >= Y

certs = []
def add(minor, label):
    certs.append({'label': label, 'R': list(minor[0]), 'C': list(minor[1]),
                  'det': det_mod(*minor)})
    print('%-8s size %2d rows %s..%s cols %s..%s det mod P = %d'
          % (label, len(minor[0]), min(minor[0]), max(minor[0]), min(minor[1]),
             max(minor[1]), certs[-1]['det']))
    assert certs[-1]['det'] != 0

used = []   # (kind, X, Y, t, certified?)
def uncovered(kind, need):
    return [b for b in need if not any(ok((c['R'], c['C']), b[0], b[1], b[2]) for c in certs)]

# ----- fixed structural minor = the full block (rows/cols forced) -----
# B(0): (1,44,1)  -> entry (0,44)
add(([0], [44]), 'E044')
# B: i=22..44 and C: i=22..44 forcing
for (t, label) in [(22, 'M22'), (23, 'M23'), (24, 'M24'), (25, 'M25')]:
    pass
add((list(range(0, 23)), list(range(22, 45))), 'M23')   # B(22)=23 @ (23,22); C(23)=23 @ (23,22)
add((list(range(0, 22)), list(range(23, 45))), 'M22')   # C(22)=22 @ (22,23)
add((list(range(0, 24)), list(range(21, 45))), 'M24')   # B(23); C(24)
add((list(range(0, 25)), list(range(20, 45))), 'M25')   # B(24); C(25..42)
add((list(range(0, 43)), list(range(2, 45))), 'M43')    # C(43)
add((list(range(0, 44)), list(range(1, 45))), 'M44')    # B(43); C(44)
# B(44) target 45 -> full matrix (N3 stair_data_cert)

print('\nuncovered B:', uncovered('B', needB))
print('uncovered C:', uncovered('C', needC))

# ----- search: 2x2 family covering B(1..21) -----
random.seed(7)
todo = uncovered('B', needB)
if todo:
    best = None
    for c1 in range(23, 45):
        for c2 in range(c1 + 1, 45):
            for r in ([0, 1],):
                if det_mod(r, [c1, c2]) != 0:
                    cov = [b for b in todo if ok((r, [c1, c2]), b[0], b[1], b[2])]
                    if best is None or len(cov) > len(best[1]):
                        best = (([r], [c1, c2]), cov)
    if best:
        print('\n2x2 candidates:', [x for x in todo if ok((best[0][0][0] if False else [0,1], best[0][1]), x[0], x[1], x[2])][:3])
        add(([0, 1], best[0][1]), 'M2')

print('\nuncovered B after M2:', uncovered('B', needB))
print('uncovered C after M2:', uncovered('C', needC))

# ----- 26-family: greedy search over remaining B positions -----
random.seed(11)
guard = 0
while uncovered('B', needB) and guard < 20:
    guard += 1
    todo = uncovered('B', needB)
    best = None
    # candidate structural shapes: rows 0..25, cols a 26-subset of 2..44 (vary minC, prefer small)
    for minc in range(2, 20):
        for trial in range(400):
            Cc = [minc] + sorted(random.sample(range(minc + 1, 45), 25))
            cov = [b for b in todo if ok((list(range(26)), Cc), b[0], b[1], b[2])]
            if not cov: continue
            if det_mod(list(range(26)), Cc) == 0: continue
            if best is None or len(cov) > len(best[1]):
                best = ((list(range(26)), Cc), cov)
                break
        if best and len(best[1]) == len(todo): break
    if best is None:
        # fall back: rows must extend beyond 25; search 26 rows from 0..42 with cols 19..44
        for trial in range(3000):
            R = sorted(random.sample(range(43), 26))
            Cc = list(range(19, 45))
            cov = [b for b in todo if ok((R, Cc), b[0], b[1], b[2])]
            if not cov: continue
            if det_mod(R, Cc) == 0: continue
            if best is None or len(cov) > len(best[1]):
                best = ((R, Cc), cov)
                if len(cov) == len(todo): break
    if best is None:
        print('!! no minor found for', todo); break
    add(best[0], 'M26_%d' % guard)

print('\nFINAL uncovered B:', uncovered('B', needB))
print('FINAL uncovered C:', uncovered('C', needC))
print('\nfinal certificate set:')
for c in certs:
    print(' ', c['label'], 'size', len(c['R']), 'R', c['R'][:3], '...', c['R'][-1] if c['R'] else None,
          'C', c['C'][:3], '...', c['C'][-1] if c['C'] else None, 'det', c['det'])
json.dump(certs, open('n2c_certs.json', 'w'), indent=1)
