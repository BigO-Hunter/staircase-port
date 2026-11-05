#!/usr/bin/env python3
"""D2 deliverable 1: inventory of exactly what the Lean QHNet construction consumes.

Enumerates every dataset component (roles/wires layout, deferred readouts, run/word tables,
side data, hist assembly inputs) with its producer source and its Lean-side target, mirroring
the platform's R8 opp-bank data family (Def_IntMul_Kappa_R8_Data_BitOppbank*) retargeted to
the staircase witness-1 line (h=23, R=28866, W=108516254).

Stdlib only. Writes extract/out/d2_inventory.txt + d2_inventory.json. Exact ints only.
"""
import gzip, json, os, re
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(HERE, 'jainroot', 'certificates', 'round7')
OUT = os.path.join(HERE, 'out')

W = json.load(gzip.open(os.path.join(DATA, 'witness_23.json.gz'), 'rt'))
D = json.load(gzip.open(os.path.join(DATA, 'deferred_23.json.gz'), 'rt'))

# The platform-frozen hist target (Lean: IntMul.Kappa.Jain.bitR7), parsed from the real file.
jain = open(os.path.join(ROOT, 'Definitions', 'Def_IntMul_KappaJainData.lean')).read()
m = re.search(r'def bitR7 : List \(ℕ × ℕ\) :=\s*\[(.*?)\]', jain, re.S)
BITR7 = [tuple(int(x) for x in pair) for pair in re.findall(r'\((\d+),\s*(\d+)\)', m.group(1))]

rows = []
def comp(name, n, rng, src, lean):
    rows.append(dict(name=name, n=n, range=rng, source=src, lean=lean))

# ---- geometry + wire layout (platform: BitOppbankConsts/WireLayout, retargeted) --------------
h, R, v = D['h'], D['R'], 1771
N = v * v; Wroles = 2 * N + 2 * v * R; T = 46 * v + N; mm = h * h
assert Wroles == 108516254 and T == 3217907 and mm == 529 and N == 3136441
comp('geometry (h,v,R,N,W,T,m)', 7, '23,1771,28866,3136441,108516254,3217907,529',
     "deferred_23['h','R'] + C(23,3)=1771 + identities 2N+2vR / 46v+N / h^2 (W.claimed['R'] link)",
     'D2Data: defs h v Rslots N W Tmp m + decide identity pins (Consts/WireLayout pattern)')
wEnt, wAuxEnd, NL = 2 * v, 2 * v + R, 2 * v + R + h
comp('wire layout (wX,wY,wS,wT,wU,g1,g2,rho_n)', 8, 'wEnt=%d wAuxEnd=%d NL=%d' % (wEnt, wAuxEnd, NL),
     'structural: 2v entrance, R aux slots, h centre/late wires (WireLayout.lean shape)',
     'D2Data: wX/wY/wS/wT/wU defs + IsSlot/IsTgt + g1/g2 + rho_n (copy of platform shape)')

# ---- stage-1 word + slot schedule ------------------------------------------------------------
ops = D['ops']
kinds = Counter(o[0] for o in ops)
fan_fields = sum(3 + len(o[2]) for o in ops if o[0] == 'fan')
ops_fields = 3 * kinds['src'] + 4 * kinds['add'] + fan_fields
comp('ops (stage-1 word)', len(ops), 'kinds %s; slots<=28865; nodes<=64042' % dict(kinds),
     "deferred_23['ops'] verbatim (reordered design-B word; check_word.py replays it)",
     'D2Data: packed 16-bit stream d2OPS (kind 1=src,2=add,3=fan + args; fan arity inline)')
comp('hold (slot->node time lines)', len(D['hold']), '153408 node ids 1..64042, lens 1..13',
     "deferred_23['hold'] (nodes each slot holds over time; Schedule.chain_keys consumes)",
     'D2Data: d2HOLDLENS + flattened 16-bit stream d2HOLD (%d fields)' % sum(len(x) for x in D['hold']))
comp('start (slot starts)', len(D['start']), "1771 ['src',n] + 27095 ['fresh',s,k], ints <=63336",
     "deferred_23['start'] (start_key: ('v',s) | ('n',n0) | ('c',n0,lt))",
     'D2Data: packed 16-bit d2START (tag 0=src,1=fresh + 2 args)')
comp('out (outputs c,T->slot)', len(D['out']), 'slots %d..%d, c in 0..%d' % (
    min(o[0] for o in D['out']), max(o[0] for o in D['out']), max(o[1] for o in D['out'])),
    "deferred_23['out']", 'D2Data: clear list d2OUT (slot,c,T) 5313 triples')
comp('ret (retained slot per centre)', len(D['ret']), 'centres 0..22',
     "deferred_23['ret'] (+ witness_23['retained'] node per centre)",
     'D2Data: clear list d2RET 23 pairs + d2RETNODE 23 pairs')

# ---- deferred readouts (the R=28866 readout family) -------------------------------------------
ro = D['readout_order']
sg = D['sigma']
sg_rows = sum(len(f) for f in sg)
sg_vals = [x for f in sg for r in f for x in r]
comp('readout_order (deferred slots)', len(ro), '%d..%d bijective' % (min(ro), max(ro)),
     "deferred_23['readout_order'] (the other R-11565=%d slots read at F0, corner rank h)" % (R - len(ro)),
     'D2Data: packed 16-bit stream d2READOUT')
comp('sigma (deferred readout frames)', len(sg), '%d rows x 23; values in [%d,%d]' % (
    sg_rows, min(sg_vals), max(sg_vals)),
    "deferred_23['sigma'] (primitive integer bases; frame len = h - corner rank, check_frames.py X re-derives)",
    'D2Data: packed 4-bit-bias+1 stream d2SIGMA (%d rows, row = 23 fields)' % sg_rows)
comp('corner ranks (h - dim sigma_u)', R, 'Counter: %s' % dict(sorted((Counter(h - len(f) for f in sg)
     | Counter({h: R - len(sg)})).items())),
     'derived: f[s] from sigma (dr.Schedule.f); histogram corner input',
     'D2Data: derivable from d2SIGMA row counts; pinned via hist table')

# ---- V leaves / X_S chains / deferred V gates -------------------------------------------------
vs_vals = [x for f in D['vleaf_start'] for r in f for x in r]
comp('vleaf_slots + vleaf_start', len(D['vleaf_slots']), '%d frames, values in [%d,%d]' % (
    len(D['vleaf_start']), min(vs_vals), max(vs_vals)),
    "deferred_23['vleaf_slots','vleaf_start'] (V-leaf start frames s_i)",
    'D2Data: d2VLEAFSLOTS 16-bit + d2VLEAFSTART (4/5-bit rows x 23)')
xs_tot = sum(len(x[1]) for x in D['xs_order'])
comp('xs_order (X_S chain per leaf)', len(D['xs_order']), '%d slots, chain lens %s' % (
    xs_tot, dict(Counter(len(x[1]) for x in D['xs_order']))),
    "deferred_23['xs_order']",
    'D2Data: d2XSN 16-bit leaf ids + d2XS chains 16-bit (flattened, lens derivable)')
comp('deferred_v_order (deferred V gates)', len(D['deferred_v_order']), '%d..%d' % (
    min(D['deferred_v_order']), max(D['deferred_v_order'])),
    "deferred_23['deferred_v_order']", 'D2Data: packed 16-bit stream d2LATEV')

# ---- dims --------------------------------------------------------------------------------------
comp('node_dims (dim of every node frame)', len(D['node_dims']), 'dims %d..%d, keys 1..64042' % (
    min(d for _, d in D['node_dims']), max(d for _, d in D['node_dims'])),
    "deferred_23['node_dims'] (check_frames X re-derives exactly)",
    'D2Data: packed 5-bit stream d2NODEDIMS (key = index+1)')
comp('late_dims (late-copy intersections)', len(D['late_dims']), 'dims %d..%d' % (
    min(d for _, _, d in D['late_dims']), max(d for _, _, d in D['late_dims'])),
    "deferred_23['late_dims'] (n, late tuple, dim)",
    'D2Data: clear list d2LATEDIMS 1396 triples')

# ---- witness side data -------------------------------------------------------------------------
comp('args (node DAG)', len(W['args']), 'leaves(None)=1..1771, adds [a,b] a,b<n',
     "witness_23['args'] (check_lifted A: disjoint additions)", 'D2Data: packed 32-bit x2 d2ARGS (0=None else a+1)')
comp('j (lift index of lifted additions)', len(W['j']), 'vals %s' % dict(sorted(Counter(W['j'].values()).items())),
     "witness_23['j']", 'D2Data: packed 5-bit stream d2J (keys implicit 1800..64042)')
comp('leaf (X_S triples)', len(W['leaf']), 'triples of 0..22',
     "witness_23['leaf'] (== combinations(range(23),3) order)", 'D2Data: packed 5-bit x3 d2LEAF (id = index+1)')
comp('links', len(W['links']), 'values <=63988',
     "witness_23['links'] (check_lifted nesting)", 'D2Data: packed 16-bit x3 d2LINKS')
comp('outputs (c,T -> node)', len(W['outputs']), 'nodes 2035..63996',
     "witness_23['outputs'] (out(c,T)={S: S cap T={c}})", 'D2Data: clear list d2WOUT (c,T,n)')
comp('flag (23x23 int matrix)', 23 * 23, 'values in [%d,%d]' % (
    min(x for r in W['flag'] for x in r), max(x for r in W['flag'] for x in r)),
    "witness_23['flag'] (the flag matrix)", 'D2Data: packed 8-bit-bias128 d2FLAG')
comp('late (late copies)', len(W['late']), '%d entries (e,l) pairs' % len(W['late']),
     "witness_23['late']", 'D2Data: clear list d2LATE')

# ---- hist assembly inputs (derived by the producer chain; certificate_round7.build) -------------
comp('cov (adjoint garbage coefficients)', R, 'dict per slot, rebuilt by transpose sweep',
     'derived: dr.Schedule.adjoint() over d2ops (check_word B over Z and F2)',
     'D2Data: computable in Lean from d2OPS (fold); not emitted')
comp('ylev (deferred levels per target)', v, 'levels = dim sigma_u on targets of u',
     'derived: S.ylevels(cov)', 'D2Data: packed 32-bit bitmap per target d2YLEV (bit i = level i+1)')
comp('rk (chain-step ranks, design-B)', 21, 'rankSum=%d' % 57403754177,
     'derived: dr.chain_ranks(S) (monotone chains asserted)', 'D2Data: clear list d2RANKS 21 pairs + count pin')
comp('xdata (X_S chain deltas)', v, 'deltas of vstart dims; sum x = h-1 asserted',
     'derived: S.xdata()', 'D2Data: packed 5-bit stream d2XD (lens = d2XS lens)')
comp('corner', 8, '[21,18,1,1,1,1,1,1] (staircase) / [21,1^24] (plain)',
     'STAIRCASE_CORNER(h)/ROUND6_CORNER(h) in deferred.py (check_stair.py)',
     'D2Data: clear list d2CORNER + d2CORNERPLAIN')
comp('hist (child widths, staircase)', len(BITR7), 'rankSum 57403754177, childCount 1905413587, W=108516254',
     'derived: dr.histogram(S,rk,ylev,xd,STAIRCASE_CORNER) == Jain.bitR7 (37 entries)',
     'D2Data: clear list d2HIST + childCount/rankSum decide pins + d2HIST_eq_bitR7 (decide)')

# ---- producer claims (cross-check targets) -----------------------------------------------------
comp('claims: D.claimed (a_b, kappa)', 2, "a_b=%s kappa=%s" % (D['claimed']['a_b'], D['claimed']['kappa']),
     "deferred_23['claimed'] == plain corner (certificate_round7.WITNESSES.plain)",
     'D2Data: pinned via d2HIST rankSum/childCount; kappa is proof-layer')
comp('claims: W.claimed (base word)', 3, "R=%s a_b=%s rk sum=%d" % (
    W['claimed']['R'], W['claimed']['a_b'],
    sum(int(r) * c for r, c in W['claimed']['rk'].items())),
     "witness_23['claimed'] == BASE (pre-reorder) word: check_lifted B (R==claim) + hist_ok (rk==claim) + certificate()",
     'D2Data: clear list d2RANKSBASE 21 pairs (base chain ranks, check_lifted-verified)')

os.makedirs(OUT, exist_ok=True)
txt = ['D2 INVENTORY — staircase witness-1 dataset for the Lean QHNet construction',
       '(producer pin c05adfe1dfe85326dd6dcf12bfd53f435bd49bf3; frozen certificates/round7/*.json.gz)',
       'Line constants: h=23 v=1771 R=28866 N=v^2=3136441 W=2N+2vR=108516254 T=46v+N=3217907 m=h^2=529',
       'Platform pattern: Def_IntMul_Kappa_R8_Data_BitOppbank* (Consts/WireLayout/ChkBitArg/LocSlots/',
       '  GenData/NetD_Runs/Hist/SideRanks/QHNet), retargeted R 27794->28866, W 104719230->108516254.',
       'bitR7 target parsed from Definitions/Def_IntMul_KappaJainData.lean: %d entries.' % len(BITR7),
       '']
for r in rows:
    txt.append('%-38s n=%-7d range: %s' % (r['name'], r['n'], r['range']))
    txt.append('%-38s src: %s' % ('', r['source']))
    txt.append('%-38s lean: %s' % ('', r['lean']))
    txt.append('')
with open(os.path.join(OUT, 'd2_inventory.txt'), 'w') as fh:
    fh.write('\n'.join(txt))
json.dump(dict(rows=rows, bitR7=[list(p) for p in BITR7]), open(os.path.join(OUT, 'd2_inventory.json'), 'w'))
print('\n'.join(txt[:14]))
print('... %d components; full table in extract/out/d2_inventory.txt' % len(rows))
print('PND-GATE inventory: bitR7 %d entries, first %s last %s' % (len(BITR7), BITR7[0], BITR7[-1]))
