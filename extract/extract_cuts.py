#!/usr/bin/env python3
"""N2b Phase 1: extract per-block cut SETS (R0, T0, C0) from a scratch copy of
check_stair.cut_bound, cross-check against the ALREADY-PINNED cut VALUES in
StaircasePort/NEBlocks.lean, dump JSON to extract/out/ne_cuts.json.

The cut_bound clone is byte-identical logic to jainroot check_stair.py:57-90 except it
RETURNS (flow, R0, T0, C0) instead of just flow. Any mismatch against the pinned values
= STOP (the pins came from the same producer; a mismatch means the clone drifted).
"""
import json, os, re, sys
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout')
sys.path.insert(0, ROOT)
import check_stair as cs

H = 23
N = 2 * H - 1  # 45


def cut_bound_sets(rows_, cols_, terms):
    """Clone of check_stair.cut_bound returning (flow, R0, T0, C0)."""
    T = [(sr & rows_, sc & cols_) for sr, sc in terms]
    nodes = [('r', r) for r in rows_] + [('t', t) for t in range(len(T))] + [('c', c) for c in cols_]
    idx = {nd: i for i, nd in enumerate(nodes)}
    BIG = 10**6; Nn = 2 * len(nodes) + 2; S_, K_ = Nn - 2, Nn - 1; cap = {}; adj = [[] for _ in range(Nn)]
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


def pinned_blocks():
    """Parse (i,j,rho,cut) tuples from StaircasePort/NEBlocks.lean (the pinned list)."""
    with open(os.path.join(HERE, '..', 'StaircasePort', 'NEBlocks.lean')) as f:
        src = f.read()
    m = re.search(r'def stairNEBlocks[^\n]*:=\s*\[([^\]]*)\]', src)
    assert m, 'stairNEBlocks list not found'
    tuples = re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)', m.group(1))
    return [tuple(map(int, t)) for t in tuples]


def main():
    RC, CC = cs.design(H, 'stair')
    _, _, terms = cs.structure(H, RC, CC)
    blocks = pinned_blocks()
    print('pinned blocks parsed:', len(blocks))
    assert len(blocks) == 689, 'expected 689 pinned NE blocks'

    # determinism control: the producer's own cut_bound must equal our clone's flow
    out = []
    mismatch = []
    for (i, j, rho, cut) in blocks:
        rows_, cols_ = set(range(i + 1)), set(range(j, N))
        flow, R0, T0, C0 = cut_bound_sets(rows_, cols_, terms)
        ref = cs.cut_bound(rows_, cols_, terms)
        if not (flow == cut == ref and len(R0) + len(T0) + len(C0) == flow):
            mismatch.append(dict(i=i, j=j, pinned=cut, clone=flow, ref=ref,
                                 R0=len(R0), T0=len(T0), C0=len(C0)))
        out.append(dict(i=i, j=j, rho=rho, cut=cut, R0=R0, T0=T0, C0=C0))

    if mismatch:
        print('STOP: %d mismatches; first 5: %s' % (len(mismatch), mismatch[:5]))
        sys.exit(1)
    print('cross-check: 689/689 clone flows reproduce pinned cut values (and producer cut_bound)')

    # structure stats for the Lean phase
    t0_hist = {}
    for b in out:
        for t in b['T0']:
            t0_hist[t] = t0_hist.get(t, 0) + 1
    print('blocks with nonempty T0:', sum(1 for b in out if b['T0']))
    print('T0 term-index histogram (term 46 = whole):', dict(sorted(t0_hist.items())))
    print('max |T0|:', max(len(b['T0']) for b in out))
    print('|R0| range:', min(len(b['R0']) for b in out), max(len(b['R0']) for b in out))
    print('|C0| range:', min(len(b['C0']) for b in out), max(len(b['C0']) for b in out))

    os.makedirs(os.path.join(HERE, 'out'), exist_ok=True)
    with open(os.path.join(HERE, 'out', 'ne_cuts.json'), 'w') as f:
        json.dump(dict(h=H, n=N, terms=[[sorted(sr), sorted(sc)] for sr, sc in terms], blocks=out), f)
    print('wrote extract/out/ne_cuts.json')

    # sample dumps for inspection
    for b in out[:3] + [x for x in out if x['i'] == 25][:2]:
        print(b)


if __name__ == '__main__':
    main()
