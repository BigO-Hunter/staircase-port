"""Find a uniform-ish M2 minor shape nonsingular at the witness for all t<18."""
import json
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
def corZ(i, j):
    return sum((sum(sl * MZ(ss, tt) for (sl, ss) in Lterms(i))) * cl for (cl, tt) in Rterms(j))
Q = [[corZ(i, j) for j in range(45)] for i in range(45)]

def nonsing(rl, cl):
    M = [[Q[r][c] % P for c in cl] for r in rl]
    rk = 0
    for c in range(len(cl)):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None: return False
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], P - 2, P)
        M[rk] = [(v * inv) % P for v in M[rk]]
        for i in range(rk + 1, len(M)):
            if M[i][c]:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[rk][j]) % P for j in range(len(cl))]
        rk += 1
    return rk == len(cl)

# candidate uniform shapes: rows 0..24 ++ [extra], cols a 26-window
for extra in range(25, 45):
    ok = all(nonsing(list(range(25)) + [extra_t_row(t, extra)] if False else list(range(25)) + [25 + t],
                     list(range(2 + t, 28 + t))) for t in range(18)) if False else None
# systematic: for each t, which (extra_row, col_window_start) work?
print("t : shapes (extra_row, colstart) that give a nonsingular 26x26, rows=0..24++[er]")
for t in range(18):
    good = []
    for er in list(range(25, 45)):
        for cs in range(2 + t, 45 - 26 + 1):
            if nonsing(list(range(25)) + [er], list(range(cs, cs + 26))):
                good.append((er, cs))
                if len(good) >= 4: break
        if len(good) >= 4: break
    print(t, good[:4])
