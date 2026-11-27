"""Vendored core of jainroot check_stair.py (independent/deferred-readout/check_stair.py,
certificate_round7 @ c05adfe lineage) — RECONSTRUCTED VERBATIM from session context after
the host restart wiped the scratch workspace (producer recon copy lost). Contains exactly the three
functions N2b extraction needs: design(), structure(), cut_bound(), plus P/iv. The original
file also had: sparse_params, runs, mv, flag_factors, corner_at, main (witness sampling
via linalg.rightmost_pivots + check_lifted.point_UV) — NOT vendored (not needed for cut
SETS extraction once the pc pattern is known; pc is reconstructed in rebuild_all.py from
the SCAFFOLD-documented runs+offsets).

Original docstring (check_stair.py):
Staircase data-entrance corner certificate (stdlib only).
Checks: 1. sparse flag-family membership + trace conditions + f1..f4/inner-corner
nonvanishing on every line; 2. upper bound identically in all parameters: every NE block
of the (2h-1)x(2h-1) entrance corner has rank <= min vertex cut of the rows-terms-cols
graph (max flow, cut re-verified); 3. lower bound at one point: rightmost pivots at
sampled line pairs, NE rank = upper bound on every nontrivial block, invertible, runs
(h-2, h-5, 1^6). Negative control (--control): random cells must NOT certify.
Usage: python3 check_stair.py h [npairs] [--control] [--ij]
"""
from collections import deque

P = 67108859                                   # the prime of round six's draws (sparse parameters depend on it)
def iv(x): return pow(x % P, P - 2, P)


def design(h, kind='stair'):
    if kind == 'stair':
        RC = [(0, 3)] + [(r + 1, r - 1) for r in range(1, h - 1)]
        CC = [(c + 1, c + 3) for c in range(h - 3)] + [(0, h - 3), (0, h - 2)]
        return RC, CC
    import random
    reserved = {(b, b) for b in range(h)} | {(h - 1, 0), (0, h - 1)}
    for j in range(h - 1): reserved |= {(j, j + 1), (j + 1, j)}
    free = sorted(set((i, j) for i in range(h) for j in range(h)) - reserved)
    rng = random.Random(kind); cells = rng.sample(free, 2 * h - 2)
    return cells[:h - 1], cells[h - 1:]


def structure(h, RC, CC):
    rows = [{(b, b)} for b in range(h - 1)] + [{(h - 1, 0), (0, h - 1)}] + [{c} for c in RC]
    cols = [{c} for c in CC] + [{(j, j + 1), (j + 1, j)} for j in range(h - 1)] + [{(h - 1, h - 1)}]
    for f in rows:
        for g in cols: assert not (f & g), 'identity term would not vanish'
    assert len(set().union(*rows) | set().union(*cols)) == sum(map(len, rows)) + sum(map(len, cols)), 'cells reused'
    terms = []
    for l in range(h): terms.append(({i for i, f in enumerate(rows) if any(c[1] == l for c in f)},
                                     {j for j, g in enumerate(cols) if any(c[1] == l for c in g)}))
    for k in range(h): terms.append(({i for i, f in enumerate(rows) if any(c[0] == k for c in f)},
                                     {j for j, g in enumerate(cols) if any(c[0] == k for c in g)}))
    terms.append((set(range(len(rows))), set(range(len(cols)))))
    return rows, cols, terms


def cut_bound(rows_, cols_, terms):
    T = [(sr & rows_, sc & cols_) for sr, sc in terms]
    nodes = [('r', r) for r in rows_] + [('t', t) for t in range(len(T))] + [('c', c) for c in cols_]
    idx = {nd: i for i, nd in enumerate(nodes)}
    BIG = 10**6; N = 2 * len(nodes) + 2; S_, K_ = N - 2, N - 1; cap = {}; adj = [[] for _ in range(N)]
    def add(a, b, c):
        if (a, b) not in cap: adj[a].append(b); adj[b].append(a); cap[a, b] = 0; cap.setdefault((b, a), 0)
        cap[a, b] += c
    for nd, k in idx.items(): add(2 * k, 2 * k + 1, 1)
    for r in rows_: add(S_, 2 * idx['r', r], BIG)
    for c in cols_: add(2 * idx['c', c] + 1, K_, BIG)
    for t, (sr, sc) in enumerate(T):
        if not sr or not sc: continue
        for r in sr: add(2 * idx['r', r] + 1, 2 * idx['t', t], BIG)
        for c in sc: add(2 * idx['t', t] + 1, 2 * idx['c', c], BIG)
    flow = 0
    while True:
        par = {S_: None}; dq = deque([S_])
        while dq and K_ not in par:
            a = dq.popleft()
            for b in adj[a]:
                if b not in par and cap[a, b] > 0: par[b] = a; dq.append(b)
        if K_ not in par: break
        b = K_
        while par[b] is not None: a = par[b]; cap[a, b] -= 1; cap[b, a] += 1; b = a
        flow += 1
    reach = set(par)
    cut = [nd for nd, k in idx.items() if 2 * k in reach and 2 * k + 1 not in reach]
    R0 = {x for t_, x in cut if t_ == 'r'}; T0 = {x for t_, x in cut if t_ == 't'}; C0 = {x for t_, x in cut if t_ == 'c'}
    assert len(cut) == flow
    for t, (sr, sc) in enumerate(T):                       # the cut is a certificate: every other term is covered
        if t in T0: continue
        assert not (sr - R0) or not (sc - C0), 'cut misses a term'
    return flow


def cut_bound_sets(rows_, cols_, terms):
    """N2b variant: same computation, RETURNS (flow, R0, T0, C0) sorted lists."""
    T = [(sr & rows_, sc & cols_) for sr, sc in terms]
    nodes = [('r', r) for r in rows_] + [('t', t) for t in range(len(T))] + [('c', c) for c in cols_]
    idx = {nd: i for i, nd in enumerate(nodes)}
    BIG = 10**6; N = 2 * len(nodes) + 2; S_, K_ = N - 2, N - 1; cap = {}; adj = [[] for _ in range(N)]
    def add(a, b, c):
        if (a, b) not in cap: adj[a].append(b); adj[b].append(a); cap[a, b] = 0; cap.setdefault((b, a), 0)
        cap[a, b] += c
    for nd, k in idx.items(): add(2 * k, 2 * k + 1, 1)
    for r in rows_: add(S_, 2 * idx['r', r], BIG)
    for c in cols_: add(2 * idx['c', c] + 1, K_, BIG)
    for t, (sr, sc) in enumerate(T):
        if not sr or not sc: continue
        for r in sr: add(2 * idx['r', r] + 1, 2 * idx['t', t], BIG)
        for c in sc: add(2 * idx['t', t] + 1, 2 * idx['c', c], BIG)
    flow = 0
    while True:
        par = {S_: None}; dq = deque([S_])
        while dq and K_ not in par:
            a = dq.popleft()
            for b in adj[a]:
                if b not in par and cap[a, b] > 0: par[b] = a; dq.append(b)
        if K_ not in par: break
        b = K_
        while par[b] is not None: a = par[b]; cap[a, b] -= 1; cap[b, a] += 1; b = a
        flow += 1
    reach = set(par)
    cut = [nd for nd, k in idx.items() if 2 * k in reach and 2 * k + 1 not in reach]
    R0 = sorted({x for t_, x in cut if t_ == 'r'})
    T0 = sorted({x for t_, x in cut if t_ == 't'})
    C0 = sorted({x for t_, x in cut if t_ == 'c'})
    assert len(cut) == flow, (len(cut), flow)
    for t, (sr, sc) in enumerate(T):
        if t in T0: continue
        assert not (sr - set(R0)) or not (sc - set(C0)), 'cut misses a term'
    return flow, R0, T0, C0
