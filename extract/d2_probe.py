#!/usr/bin/env python3
"""D2 probe: load the frozen round7 certificates and dump every component the QHNet
construction consumes (producer chain at pin c05adfe). Scratch tool — regen lives in
d2_regen.py; this file is for measuring the inventory."""
import gzip, json, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, 'jainroot', 'scripts'),
                os.path.join(HERE, 'jainroot', 'independent', 'two-stage-bit'),
                os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout')]
import moment
import deferred as dr
from certificate_round7 import build
from deferred import STAIRCASE_CORNER, ROUND6_CORNER

W, D = dr.load(23, 'witness_23.json.gz', 'deferred_23.json.gz')
print('== witness_23 keys:', sorted(W.keys()))
print('== deferred_23 keys:', sorted(D.keys()))
for k in sorted(D.keys()):
    v = D[k]
    if isinstance(v, list):
        print('   D.%-18s list len %d' % (k, len(v)))
    elif isinstance(v, dict):
        print('   D.%-18s dict  len %d' % (k, len(v)))
    else:
        print('   D.%-18s %r' % (k, v))
for k in sorted(W.keys()):
    v = W[k]
    if isinstance(v, list):
        print('   W.%-18s list len %d' % (k, len(v)))
    elif isinstance(v, dict):
        print('   W.%-18s dict  len %d' % (k, len(v)))
    else:
        print('   W.%-18s %r' % (k, v))

S, rk, ylev, xd = build()
print('\n== Schedule: h=%d v=%d R=%d  ops=%d  readout=%d  vstart=%d  xs=%d  late_v=%d  node_dims=%d  late_dims=%d'
      % (S.h, S.v, S.R, len(S.ops), len(S.readout), len(S.vstart), len(S.xs), len(S.late_v),
         len(S.node_dims), len(S.late_dims)))
print('   corner ranks (h - f_s):', sorted(Counter(23 - S.f[s] for s in range(S.R)).items()))
print('   chain_ranks:', sorted(rk.items()))
print('   ylev #targets with levels:', len(ylev), ' distinct level sets:', Counter(tuple(v) for v in ylev.values()))
print('   xdata #leaves:', len(xd), ' distinct patterns:', Counter(tuple(x) for x in xd))

for name, corner in (('plain', ROUND6_CORNER(23)), ('staircase', STAIRCASE_CORNER(23))):
    c = dr.histogram(S, rk, ylev, xd, corner)
    a, _ = moment.certify(c)
    hist = sorted(c['hist'].items())
    print('\n== %s corner %s' % (name, corner))
    print('   entries=%d  W=%d  s=%d  L=%d  N=%d  R=%d' % (len(hist), c['W'], c['s'], c['L'], c['N'], c['R']))
    print('   a_b =', a)
    print('   hist:', hist)
    rc = sum(c['hist'].values()); rs = sum(w * n for w, n in hist)
    print('   childCount(sum n_w)=%d  rankSum=%d' % (rc, rs))
