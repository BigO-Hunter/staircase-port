#!/usr/bin/env python3
"""Extract staircase-corner data for the Lean port (exact ints, ZMod P arithmetic).

Mirrors check_stair.py main() (jainroot/independent/deferred-readout/check_stair.py:153-188)
but CAPTURES instead of prints:
  (a) dominant rightmost-pivot pattern pc, its run decomposition with (i,j) offsets,
      and the resulting dataRuns' run triples (global m=529 coordinates);
  (c) the 45x45 corner matrix + the 45x23 staircase B block (corner cols 22..44, the
      analogue of nb_data_edge_solution.lean:536-552 B i gamma = Cp i (h+3+gamma)) at the
      first sampled line pair, det check, NE rank profile + per-block min-cut bounds;
  (d) middle-block run (45,45,439) confirmation inputs (isPiv_mid needs only k=45, rank
      484, corner det != 0; positions (i,i), i in [45,483]).
Also runs the --ij variant (U = V = I + J explicit bases) as a determinism control.
Outputs: extract/out/staircase_data.json + staircase_data_summary.txt
"""
import json, os, random, sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout')
sys.path.insert(0, ROOT)
import linalg
import check_lifted
import check_stair as cs

OUT = os.path.join(HERE, 'out')
os.makedirs(OUT, exist_ok=True)

H = 23                 # schedule h (check_stair h; = flag_gen n = hLean+4 with hLean=19)
NPAIRS = 20            # check_stair default
SEED = 1               # check_stair default
P = cs.P               # 67108859
M = 529                # network width (= H*H)
CORNER_BASE = M - (2 * H - 1)   # 484: global col of corner col 0


def sample_pairs(h, seed, npairs, ij=False):
    """Replicates check_stair.main lines 156-173: returns U,V,Ui,Vi,sp and the list of
    (corner_matrix, pc) for each sampled line pair (deterministic: same RNG order)."""
    RC, CC = cs.design(h, 'stair')
    U, V = check_lifted.point_UV(h, seed)
    if ij:
        U = [[1 + int(i == k) for k in range(h)] for i in range(h)]
        V = [r[:] for r in U]
    U = [[x % P for x in r] for r in U]
    V = [[x % P for x in r] for r in V]
    Ui, Vi = linalg.inv_mod_matrix(U, P), linalg.inv_mod_matrix(V, P)
    sp = cs.sparse_params(h, random.Random(1000 + seed))
    rows = [{(b, b): 1} for b in range(h - 1)] + \
           [{(h - 1, 0): sp['al'], (0, h - 1): sp['be']}] + [{c: 1} for c in RC]
    cols = [{c: 1} for c in CC] + \
           [{(j, j + 1): sp['a'][j], (j + 1, j): sp['b'][j]} for j in range(h - 1)] + \
           [{(h - 1, h - 1): 1}]
    trip = list(combinations(range(h), 3))
    prng = random.Random(seed + 7)
    UT = [list(c) for c in zip(*U)]
    VT = [list(c) for c in zip(*V)]
    i9, i2 = cs.iv(9), cs.iv(2)

    def line(t, AT, Ai):
        tv = [int(i in t) for i in range(h)]
        g = [(x - 3 * i9) * i2 % P for x in tv]
        return cs.mv(AT, tv), cs.mv(Ai, g)

    pairs = []
    for _ in range(npairs):
        t1, t2 = prng.choice(trip), prng.choice(trip)
        p, xi = line(t1, UT, Ui)
        v, nu = line(t2, VT, Vi)
        C = cs.corner_at(h, rows, cols, p, xi, v, nu)
        pairs.append(dict(C=C, pc=list(linalg.rightmost_pivots(C, P)), p=p, xi=xi, v=v, nu=nu))
    return dict(RC=RC, CC=CC, U=U, V=V, Ui=Ui, Vi=Vi, sp=sp, rows=rows, cols=cols), pairs


def runs_with_offsets(pc):
    """check_stair.runs (:98-104) plus the (start_row, start_col) offset of each run."""
    pts = sorted((i, c) for i, c in enumerate(pc) if c >= 0)
    out = []
    prev = None
    for i, c in pts:
        if prev and i == prev[0] + 1 and c == prev[1] + 1:
            out[-1] = (out[-1][0], out[-1][1], out[-1][2] + 1)
        else:
            out.append((i, c, 1))
        prev = (i, c)
    return out


def extract(ij=False):
    static, pairs = sample_pairs(H, SEED, NPAIRS, ij=ij)
    pats = {}
    for d in pairs:
        key = tuple(d['pc'])
        pats[key] = pats.get(key, 0) + 1
    pc = list(max(pats, key=pats.get))
    offs = runs_with_offsets(pc)
    lengths = sorted((r[2] for r in offs), reverse=True)
    n = 2 * H - 1  # 45
    # NE rank profile rho (check_stair:176) and cut bounds for nontrivial blocks (:178-183)
    rho = [[sum(1 for r in range(i + 1) if pc[r] >= j) for j in range(n)] for i in range(n)]
    _, _, terms = cs.structure(H, static['RC'], static['CC'])
    blocks = []
    for i in range(n):
        for j in range(n):
            if rho[i][j] == min(i + 1, n - j):
                continue
            ub = cs.cut_bound(set(range(i + 1)), set(range(j, n)), terms)
            blocks.append(dict(i=i, j=j, rho=rho[i][j], cut=ub, ok=ub >= rho[i][j]))
    d0 = pairs[0]
    detC = linalg.det_mod(d0['C'], P) if hasattr(linalg, 'det_mod') else None
    invertible = -1 not in pc
    return dict(
        ij=ij, pc=pc, n_distinct_patterns=len(pats), runs_lengths=lengths,
        runs_offsets=[[i, j, l] for (i, j, l) in offs],
        dataRuns_prime=[[2 * H - 1, 2 * H - 1, M - 2 * (2 * H - 1)]] +
                       [[i, CORNER_BASE + j, l] for (i, j, l) in offs if l > 1],
        singleton_runs=[[i, CORNER_BASE + j, 1] for (i, j, l) in offs if l == 1],
        rs_prime_length=sum(1 for r in offs if r[2] == 1),
        ne_blocks=blocks, ne_blocks_all_ok=all(b['ok'] for b in blocks),
        corner45=d0['C'], B45x23=[row[22:] for row in d0['C']],
        corner_invertible=invertible, det_mod_P=detC,
        witness=dict(p=d0['p'], xi=d0['xi'], v=d0['v'], nu=d0['nu']),
        sparse_params={k: (v if not isinstance(v, list) else v) for k, v in static['sp'].items()},
        RC=[list(c) for c in static['RC']], CC=[list(c) for c in static['CC']],
    )


def main():
    res = extract(ij=False)
    res_ij = extract(ij=True)
    # middle-block confirmation (d): isPiv_mid (k=45) applies iff 2*45 <= 529, rank = 484,
    # corner det != 0; positions (i,i) i in [45,483]; run (45,45,439).
    res['middle_run'] = dict(
        triple=[45, 45, 439], two_k_le_m=(2 * 45 <= M),
        rank_target=M - 45,
        positions_diagonal=[[i, i] for i in range(45, 484)][:3] + ['...484-1'],
        corner_det_nonzero=res['corner_invertible'],
        disjoint_from_corner_runs=all(
            not (45 <= i <= 483 and i == i)  # trivially true; real check below
            for (i, j, l) in [] ) or True,
    )
    # real disjointness: corner-run global positions vs middle positions
    corner_positions = set()
    for (a, b, l) in res['dataRuns_prime'][1:]:
        for k in range(l):
            corner_positions.add((a + k, b + k))
    middle_positions = {(i, i) for i in range(45, 484)}
    res['middle_run']['disjoint_from_corner_runs'] = not (corner_positions & middle_positions)
    res['middle_run']['corner_positions_count'] = len(corner_positions)
    res['ij_control'] = dict(pc=res_ij['pc'], runs=res_ij['runs_lengths'],
                             offsets=res_ij['runs_offsets'],
                             same_pattern_as_default=res_ij['pc'] == res['pc'],
                             certified=res_ij['ne_blocks_all_ok'] and res_ij['corner_invertible']
                             and res_ij['n_distinct_patterns'] == 1)
    res['sanity'] = dict(
        runs_expected=[21, 18, 1, 1, 1, 1, 1, 1],
        runs_match=res['runs_lengths'] == [21, 18, 1, 1, 1, 1, 1, 1],
        total_rank=sum(r[2] for r in res['runs_offsets']) + 439,
        total_rank_expected=M - 45,
        singletons_expected=6,
        singletons_match=res['rs_prime_length'] == 6,
        certified=(res['ne_blocks_all_ok'] and res['corner_invertible']
                   and res['n_distinct_patterns'] == 1),
    )
    with open(os.path.join(OUT, 'staircase_data.json'), 'w') as fh:
        json.dump(res, fh, indent=1)
    # human summary
    lines = ['staircase extraction (h=%d, P=%d, m=%d, seed=%d, npairs=%d)' % (H, P, M, SEED, NPAIRS),
             'pc (rightmost pivots, 45 rows): %s' % res['pc'],
             'runs with offsets (corner coords (i,j,len)): %s' % res['runs_offsets'],
             'dataRuns_prime (global): %s' % res['dataRuns_prime'],
             'rs_prime_length: %d (r6 was h+5=24)' % res['rs_prime_length'],
             'NE blocks: %d, all cut>=rho: %s' % (len(res['ne_blocks']), res['ne_blocks_all_ok']),
             'corner invertible: %s' % res['corner_invertible'],
             'sanity: %s' % json.dumps(res['sanity']),
             'ij control: same pc=%s certified=%s' % (res['ij_control']['same_pattern_as_default'],
                                                       res['ij_control']['certified'])]
    txt = '\n'.join(lines)
    with open(os.path.join(OUT, 'staircase_data_summary.txt'), 'w') as fh:
        fh.write(txt + '\n')
    print(txt)
    assert res['sanity']['runs_match'] and res['sanity']['certified'] and \
        res['sanity']['singletons_match'] and res['sanity']['total_rank'] == M - 45, 'SANITY FAIL'
    print('OK')


if __name__ == '__main__':
    main()
