"""N2c certificate set (final): greedy maximum-coverage search for minors, each verified
det != 0 mod stairCertP, such that every IsPiv position's B-block (needs k+1) and C-block
(needs k) is covered by a minor that sits inside it."""
import json, random

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

# ---------- B / C certificates needed ----------
needB = [(i + 1, pc[i], rho(i, pc[i]) + 1) for i in range(n)]
needC = [(i, pc[i] + 1, rho(i, pc[i])) for i in range(n) if rho(i, pc[i]) > 0]

certs = []
def covers(minor, X, Y, t):
    R, Cc = minor
    return len(R) == t and max(R) < X and min(Cc) >= Y
def unc(need):
    return [b for b in need if not any(covers((c['R'], c['C']), *b) for c in certs)]
def add(minor, label):
    assert det_mod(*minor) != 0
    certs.append({'label': label, 'R': sorted(minor[0]), 'C': sorted(minor[1]),
                  'det': det_mod(*minor)})
    R, Cc = minor
    print('%-9s size %2d rows %2d..%-2d cols %2d..%-2d det=%d' %
          (label, len(R), min(R), max(R), min(Cc), max(Cc), certs[-1]['det']))

# ---- the forced full-block minors (upper bound = min(#rows,#cols)) ----
add(([0], [44]), 'E044')                       # B(0); C(1..21)
add((list(range(22)), list(range(23, 45))), 'M22')   # C(22)
add((list(range(23)), list(range(22, 45))), 'M23')   # B(22); C(23)
add((list(range(24)), list(range(21, 45))), 'M24')   # B(23); C(24)
add((list(range(25)), list(range(20, 45))), 'M25')   # B(24); C(25..42)
add((list(range(43)), list(range(2, 45))), 'M43')    # C(43)
add((list(range(44)), list(range(1, 45))), 'M44')    # B(43); C(44)
# B(44) target 45 = full matrix: N3 stair_data_cert (det != 0), no new cert

random.seed(1)
print('\nuncovered after forced minors: B', len(unc(needB)), 'C', len(unc(needC)))

# ---- t=2 family: positions (i+1, 22+i) for i=1..21 ----
while True:
    todo = [b for b in unc(needB) if b[2] == 2]
    if not todo: break
    # try every (rows, cols) pair shape, keep the one covering the most
    best = None
    cols_pool = [(c1, c2) for c1 in range(23, 45) for c2 in range(c1 + 1, 45)]
    rows_pool = [(r1, r2) for r1 in range(0, 22) for r2 in range(r1 + 1, 22)]
    for (c1, c2) in cols_pool:
        for (r1, r2) in rows_pool:
            cov = [b for b in todo if covers(([r1, r2], [c1, c2]), *b)]
            if not cov: continue
            if best is not None and len(cov) <= len(best[1]): continue
            if det_mod([r1, r2], [c1, c2]) == 0: continue
            best = (([r1, r2], [c1, c2]), cov)
    if best is None:
        print('!! no 2x2 minor'); break
    add(best[0], 'M2_%d' % len([c for c in certs if c['label'].startswith('M2')]))

# ---- t=26 family: positions (i+1, i-23) for i=25..42 ----
random.seed(5)
while True:
    todo = [b for b in unc(needB) if b[2] == 26]
    if not todo: break
    best = None
    # structured shapes: rows 0..25 with cols of decreasing width; then general random
    shapes = []
    for minc in range(2, 20):
        shapes.append((list(range(26)), [minc] + sorted(random.sample(range(minc + 1, 45), 25))))
    for _ in range(1500):
        m = random.randint(25, 42)
        R = sorted(set(random.sample(range(m + 1), 26)))
        minc = random.randint(max(2, 19 - (42 - m)), 19)
        Cs = [minc] + sorted(random.sample(range(minc + 1, 45), 25)) if 45 - minc >= 26 else None
        if Cs: shapes.append((R, Cs))
    shapes.append((list(range(26)), list(range(19, 45))))
    for _ in range(1500):
        R = sorted(random.sample(range(43), 26))
        shapes.append((R, list(range(19, 45))))
    for (R, Cs) in shapes:
        cov = [b for b in todo if covers((R, Cs), *b)]
        if not cov: continue
        if best is not None and len(cov) <= len(best[1]): continue
        if det_mod(R, Cs) == 0: continue
        best = ((R, Cs), cov)
    if best is None:
        print('!! no 26x26 minor for', todo); break
    add(best[0], 'M26_%d' % len([c for c in certs if c['label'].startswith('M26')]))

print('\nUNCOVERED B:', unc(needB))
print('UNCOVERED C:', unc(needC))
print('\nfinal %d certificates, total modular mults %d' %
      (len(certs), sum(len(c['R']) ** 3 for c in certs)))
for c in certs:
    print(' %-9s n=%2d R=%s C=%s' % (c['label'], len(c['R']),
          (str(c['R'][:2]) + '..' + str(c['R'][-1])) if c['R'] else '[]',
          (str(c['C'][:2]) + '..' + str(c['C'][-1])) if c['C'] else '[]'))
json.dump(certs, open('n2c_certs.json', 'w'), indent=1)

# ---------- emit the per-position assignment (which cert serves B and C) ----------
assign = []
for i in range(n):
    j = pc[i]; k = rho(i, j)
    b = [c['label'] for c in certs if covers((c['R'], c['C']), i + 1, j, k + 1)]
    cc = [c['label'] for c in certs if k and covers((c['R'], c['C']), i, j + 1, k)]
    if k + 1 == 45 and not b: b = ['FULL']
    if k == 0: cc = ['TRIV']
    assign.append({'i': i, 'j': j, 'k': k, 'B': b, 'C': cc})
json.dump(assign, open('n2c_assign.json', 'w'), indent=1)
print('\nper-position assignment (i, j, k, B-certs, C-certs):')
for x in assign: print(' ', x)
