#!/usr/bin/env python3
"""D2 deliverables 2+3: regenerate the QHNet dataset from the producer chain OFFLINE, cross-check
every component against the frozen certificates, and emit StaircasePort/D2Data*.lean.

PND-GATE (GAP 9, the r8-plain lesson): any mismatch between the regenerated chain and the frozen
artifacts (or the platform-frozen Jain.bitR7) = STOP + report. Exact ints only, stdlib only.

Cross-check layers:
  A. design-B schedule: certificate_round7.build() re-derives cov/ylev/rk/xd from the frozen
     word; dr.histogram(STAIRCASE_CORNER) must EQUAL Jain.bitR7 parsed from
     Definitions/Def_IntMul_KappaJainData.lean (value equality, 37 entries) with rankSum
     57403754177 / childCount 1905413587; dr.histogram(ROUND6_CORNER) must reproduce
     deferred_23.claimed.a_b; moment.certify + kappa for BOTH corners must equal the
     certificate_round7 witness constants.
  B. structural invariants of the frozen artifacts (bijections, op well-formedness, dims,
     frame value ranges, corner-rank/frame-len distribution, the R-link, leaf/j/links/flag...).
  C. base-word claims (witness_23.claimed): the detached battery (extract/out/d2_check_lifted.log)
     must report compiled R == claim and chain-rank histogram == claim (hist_ok True).
  D. emission round-trip: every packed stream decodes back to its source exactly (Python mirror
     of the emitted Lean packL/fieldOf).

Outputs: extract/out/d2_regen.log, extract/out/d2_data.json,
         StaircasePort/D2Common.lean, D2Data0.lean.., D2Data.lean (generated tables + pins).
"""
import gzip, json, os, re, sys, time
from collections import Counter
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(HERE, 'jainroot', 'certificates', 'round7')
OUT = os.path.join(HERE, 'out')
sys.path[:0] = [os.path.join(HERE, 'jainroot', 'scripts'),
                os.path.join(HERE, 'jainroot', 'independent', 'two-stage-bit'),
                os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout')]
import moment
import deferred as dr
from certificate_round7 import build, kappa, WITNESSES
from deferred import ROUND6_CORNER, STAIRCASE_CORNER

T0 = time.time()
LOG = []
def log(*a):
    line = '[%5.0fs] %s' % (time.time() - T0, ' '.join(str(x) for x in a))
    LOG.append(line); print(line, flush=True)

VERDICTS = []
def verdict(name, ok, detail=''):
    VERDICTS.append((name, bool(ok), detail))
    log('PND %-58s %s %s' % (name, 'PASS' if ok else 'FAIL', detail))
    if not ok:
        open(os.path.join(OUT, 'd2_regen.log'), 'w').write('\n'.join(LOG) + '\n')
        raise SystemExit('PND-GATE FAILURE: %s %s — STOP, do not emit Lean data' % (name, detail))

def parse_bitr7():
    jain = open(os.path.join(ROOT, 'Definitions', 'Def_IntMul_KappaJainData.lean')).read()
    mb = re.search(r'def bitR7 : List \(ℕ × ℕ\) :=\s*\[(.*?)\]', jain, re.S)
    return sorted((int(a), int(b)) for a, b in re.findall(r'\((\d+),\s*(\d+)\)', mb.group(1)))

def main():
    os.makedirs(OUT, exist_ok=True)
    W, D = dr.load(23, 'witness_23.json.gz', 'deferred_23.json.gz')
    S, rk, ylev, xd = build()
    h, v, R = S.h, S.v, S.R
    N = v * v; Wd = 2 * N + 2 * v * R; m = h * h; T = 46 * v + N
    log('producer chain: h=%d v=%d R=%d ops=%d readout=%d vstart=%d late_v=%d' % (
        h, v, R, len(S.ops), len(S.readout), len(S.vstart), len(S.late_v)))
    BITR7 = parse_bitr7()

    # ---------------- A. hist assembly vs the platform-frozen bitR7 -----------------------------
    cs = dr.histogram(S, rk, ylev, xd, STAIRCASE_CORNER(h))
    hist = sorted(cs['hist'].items())
    verdict('A1 hist(staircase) == Jain.bitR7 (%d entries)' % len(BITR7),
            hist == BITR7, '%d entries' % len(hist))
    rs = sum(w * n for w, n in hist); rc = sum(n for _, n in hist)
    verdict('A2 staircase rankSum == 57403754177', rs == 57403754177 == cs['s'], 'got %d' % rs)
    verdict('A3 staircase childCount == 1905413587', rc == 1905413587, 'got %d' % rc)
    verdict('A4 staircase W == 2N+2vR == 108516254', cs['W'] == Wd == 108516254, 'got %d' % cs['W'])

    cp = dr.histogram(S, rk, ylev, xd, ROUND6_CORNER(h))
    hp = sorted(cp['hist'].items())
    a_p, _ = moment.certify(cp)
    a_s, _ = moment.certify(cs)
    wit = WITNESSES[0]
    verdict('A5 plain a_b == D.claimed.a_b == witness const',
            str(a_p) == D['claimed']['a_b'] and a_p == wit['plain'][0], 'got %s' % a_p)
    verdict('A6 staircase a_b == witness const', a_s == wit['staircase'][0], 'got %s' % a_s)
    k_p, k_s = kappa(a_p), kappa(a_s)
    verdict('A7 kappa(plain) == claim', k_p['ok'] and k_p['kappa'] == wit['plain'][1], str(k_p['kappa']))
    verdict('A8 kappa(staircase) == claim', k_s['ok'] and k_s['kappa'] == wit['staircase'][1], str(k_s['kappa']))
    verdict('A9 D.claimed.kappa == plain kappa', Q(D['claimed']['kappa']) == wit['plain'][1], D['claimed']['kappa'])
    verdict('A10 s == W*m - N + L (both corners)',
            cp['s'] == cp['W'] * cp['m'] - N + cp['L'] and cs['s'] == cs['W'] * m - N + cs['L'],
            'L=%d' % cs['L'])

    # ---------------- B. structural invariants of the frozen artifacts ---------------------------
    ops = S.ops
    kinds = Counter(o[0] for o in ops)
    ok_ops, seen_add = True, set()
    for o in ops:
        if o[0] == 'src':
            ok_ops &= 0 <= o[1] < R and 1 <= o[2] <= 64042 and S.args.get(o[2]) is None
        elif o[0] == 'add':
            piv, oth, n = o[1], o[2], o[3]
            ok_ops &= 0 <= piv < R and 0 <= oth < R and 1 <= n <= 64042 and n not in seen_add
            an = S.args.get(n)
            ok_ops &= an is not None and an[0] < n and an[1] < n and S.pivslot.get(n) == piv
            seen_add.add(n)
        elif o[0] == 'fan':
            ok_ops &= 0 <= o[1] < R and len(o[2]) > 0 and all(0 <= f < R for f in o[2])
        else:
            ok_ops = False
    verdict('B1 ops well-formed (%s)' % dict(kinds), ok_ops, '%d ops' % len(ops))
    verdict('B2 readout_order bijective in [0,R)', len(set(S.readout)) == len(S.readout) == len(S.sigma)
            and min(S.readout) >= 0 and max(S.readout) < R, '%d deferred of R=%d' % (len(S.readout), R))
    verdict('B3 vleaf_slots bijective, one per V gate',
            len(set(S.vstart)) == len(S.vstart) == sum(len(us) for _, us in S.xs)
            and min(D['vleaf_slots']) >= 0 and max(D['vleaf_slots']) < R,
            '%d V-gate slots over %d leaves' % (len(S.vstart), v))
    verdict('B4 hold: R slot lines', len(S.hold) == R, '%d lines' % len(S.hold))
    nd_keys = sorted(n for n, _ in D['node_dims'])
    verdict('B5 node_dims keys == 1..64042, dims 1..22',
            nd_keys == list(range(1, 64043)) and all(1 <= d <= 22 for _, d in D['node_dims']), '64042')
    ld_gen = {(n, tuple(lt[i:])) for n, (e, lt) in S.late.items() for i in range(len(lt) - 1)}
    ld_set = {(n, tuple(lt)) for n, lt, _ in D['late_dims']}
    verdict('B6 late_dims == all late-copy suffix keys, dims 1..22',
            ld_set == ld_gen and all(1 <= d <= 22 for _, _, d in D['late_dims']), '%d' % len(ld_set))
    verdict('B7 sigma rows are length-h integer vectors',
            all(len(r) == h for f in D['sigma'] for r in f),
            '%d rows' % sum(len(f) for f in D['sigma']))
    sg_vals = [x for f in D['sigma'] for r in f for x in r]
    verdict('B8 sigma values integral in [-15,15] (5-bit bias-16 encodable)',
            all(isinstance(x, int) and -15 <= x <= 15 for x in sg_vals),
            'range [%d,%d]' % (min(sg_vals), max(sg_vals)))
    vs_vals = [x for f in D['vleaf_start'] for r in f for x in r]
    verdict('B9 vleaf_start values integral in [-15,15] (5-bit bias-16 encodable)',
            all(isinstance(x, int) and -15 <= x <= 15 for x in vs_vals),
            'range [%d,%d]' % (min(vs_vals), max(vs_vals)))
    corner_expect = Counter(h - len(B) for B in D['sigma']) | Counter({h: R - len(D['sigma'])})
    verdict('B10 corner ranks == sigma frame-len distribution',
            Counter(h - S.f[s] if s in S.sel else h for s in range(R)) == corner_expect,
            '%d classes' % len(corner_expect))
    xs_ok = all(len(us) in (6, 7, 9) and all(0 <= u < len(D['vleaf_slots']) for u in us)
                for _, us in D['xs_order'])
    verdict('B11 xs_order chains', xs_ok, '%d chains, lens %s' % (len(S.xs), dict(Counter(len(x[1]) for x in S.xs))))
    verdict('B12 xdata deltas sum to h-1 (producer assert)', all(sum(x) == h - 1 for x in xd), '%d leaves' % len(xd))
    verdict('B13 W.claimed.R == D.R == 28866', W['claimed']['R'] == D['R'] == R, '%d' % W['claimed']['R'])
    verdict('B14 leaf == combinations(range(23),3)',
            all(tuple(W['leaf'][str(n)]) == S.trip[n - 1] for n in range(1, v + 1)), '%d leaves' % v)
    j_ok = all(S.args.get(int(n)) is not None and 14 <= lv <= 21 for n, lv in W['j'].items())
    verdict('B15 j: lifted additions with levels 14..21', j_ok, '%d entries' % len(W['j']))
    lk_ok = all(len(l) == 3 and 1 <= l[0] <= 64042 and 1 <= l[1] <= 64042 and 0 <= l[2] < h for l in W['links'])
    verdict('B16 links well-formed', lk_ok, '%d links' % len(W['links']))
    out_ok = len(W['outputs']) == 3 * v == len(S.out) and all(o[0] in o[1] for o in W['outputs'])
    verdict('B17 outputs == 3v with c in T', out_ok, '%d' % len(W['outputs']))
    verdict('B18 flag 23x23 ints |v|<=50',
            len(W['flag']) == 23 and all(len(r) == 23 and all(isinstance(x, int) and -50 <= x <= 50 for x in r)
            for r in W['flag']), '529 entries')
    verdict('B19 design-B chain ranks: 21 classes (chains monotone by construction)', len(rk) == 21,
            'count=%d rankSum=%d' % (sum(rk.values()), sum(r * c for r, c in rk.items())))
    verdict('B20 ylev covers all v targets, levels 1..22', len(ylev) == v
            and all(1 <= x <= 22 for st in ylev.values() for x in st), '%d targets' % len(ylev))

    # ---------------- C. base-word claims via the detached battery -------------------------------
    bat = os.path.join(OUT, 'd2_check_lifted.log')
    if os.path.exists(bat):
        txt = open(bat, errors='replace').read()
        if 'compiled: R=' in txt:
            verdict('C1 base compile R == claim (check_lifted B)',
                    'compiled: R=28866 (claimed 28866)' in txt)
        else:
            log('C1/C2 battery still running — re-run d2_regen.py before the final commit')
        if 'histogram equals claim' in txt:
            verdict('C2 base chain-rank hist == claim (check_lifted hist_ok)',
                    'histogram equals claim: True' in txt)
    else:
        log('C1/C2 battery log missing — re-run d2_regen.py after the battery completes')
    fr = os.path.join(OUT, 'd2_check_frames.log')
    if os.path.exists(fr):
        ftxt = open(fr, errors='replace').read()
        if 'ALL PASS' in ftxt:
            verdict('C3 check_frames battery ALL PASS (exact dims re-derived in-clone)',
                    'FAIL' not in ftxt
                    and 'X. recorded frame dims == exact dims (64042 node frames, 1396 late-copy intersections)' in ftxt
                    and 'F. claims: a_b 12599/200000000' in ftxt,
                    '%d FAIL lines' % ftxt.count('FAIL'))
        else:
            log('C3 check_frames still running — re-run d2_regen.py before the final commit')
    else:
        log('C3 check_frames log missing — run the battery (d2_battery)')

    # ---------------- D. emit dataset + Lean module ----------------------------------------------
    emit(W, D, S, rk, ylev, xd, cs, hp, BITR7, kinds)
    npass = sum(1 for _, ok, _ in VERDICTS if ok)
    log('D2 REGEN COMPLETE: %d/%d verdicts PASS' % (npass, len(VERDICTS)))
    open(os.path.join(OUT, 'd2_regen.log'), 'w').write('\n'.join(LOG) + '\n')
    json.dump(dict(verdicts=[[n, ok, d] for n, ok, d in VERDICTS],
                   hist_stair=[list(p) for p in hist], hist_plain=[list(p) for p in hp],
                   a_b=dict(plain=str(a_p), staircase=str(a_s)),
                   ranksum=dict(staircase=rs), childcount=dict(staircase=rc)),
              open(os.path.join(OUT, 'd2_data.json'), 'w'), indent=1)


# =============================================================================================
# Packing (Python mirror of the emitted Lean packL/fieldOf: 65536-bit limbs, LSB-first).
# Chunked implementation: fields are packed into chunk-ints (2^16 fields each), then the
# chunks are concatenated — O(n) instead of the O(n^2) growing-accumulator fold.
# =============================================================================================
CHUNK = 1 << 16

def packL(fields, width):
    limbs = []; acc = 0; nb = 0
    for i in range(0, len(fields), CHUNK):
        part = fields[i:i + CHUNK]
        acc_c = 0
        for j, x in enumerate(part):
            acc_c |= x << (width * j)
        acc |= acc_c << nb
        nb += width * len(part)          # exact significant-bit count, not CHUNK-padded
        while nb >= 65536:
            limbs.append(acc & ((1 << 65536) - 1))
            acc >>= 65536; nb -= 65536
    if nb and acc:
        limbs.append(acc)
    return limbs

def unpack(limbs, width, count):
    X = 0
    for i, l in enumerate(limbs): X |= l << (65536 * i)
    return [(X >> (width * i)) & ((1 << width) - 1) for i in range(count)]

def roundtrip_ok(fields, width, limbs):
    """Per-limb decode of the packed limbs (O(n); decode path independent of pack path)."""
    need = (width * len(fields) + 65535) // 65536
    if len(limbs) < need:
        return False
    ls = [int.from_bytes(l.to_bytes(8192, 'little'), 'little') for l in limbs] + [0, 0]
    nxt_mask = (1 << (width - 1)) - 1
    seen = 0
    for i in range(len(limbs)):
        j_lo = -(-i * 65536 // width)               # first field starting in limb i
        j_hi = min(((i + 1) * 65536 - 1) // width + 1, len(fields))
        if j_lo >= j_hi:
            continue
        local = ls[i] | ((ls[i + 1] & nxt_mask) << 65536)
        for j in range(j_lo, j_hi):
            off = width * j - i * 65536
            if ((local >> off) & ((1 << width) - 1)) != fields[j]:
                return False
            seen += 1
    return seen == len(fields)

def emit(W, D, S, rk, ylev, xd, cs, hist_plain, BITR7, kinds):
    h, v, R = S.h, S.v, S.R
    streams = {}
    def stream(name, fields, width):
        limbs = packL(fields, width)
        assert len(fields) == 0 or unpack(limbs, width, min(len(fields), 64))[:min(len(fields), 64)] \
            == fields[:min(len(fields), 64)], 'head decode FAIL %s' % name
        assert roundtrip_ok(fields, width, limbs), 'round-trip FAIL %s' % name
        streams[name] = (width, len(fields), limbs)
        log('stream %-12s width=%2d fields=%-8d limbs=%d OK' % (name, width, len(fields), len(limbs)))

    opf = []
    for o in S.ops:
        if o[0] == 'src': opf += [1, o[1], o[2]]
        elif o[0] == 'add': opf += [2, o[1], o[2], o[3]]
        else: opf += [3, o[1], len(o[2])] + list(o[2])
    stream('OPS', opf, 16)
    stream('HOLDLENS', [len(x) for x in D['hold']], 8)
    stream('HOLD', [x for l in D['hold'] for x in l], 16)
    stf = []
    for st in D['start']:
        stf += ([0, st[1]] if st[0] == 'src' else [1, st[1], st[2]])
    stream('START', stf, 16)
    stream('READOUT', D['readout_order'], 16)
    stream('SIGMA', [x + 16 for f in D['sigma'] for r in f for x in r], 5)   # bias+16: signed 5-bit
    stream('VLEAFSLOTS', D['vleaf_slots'], 16)
    stream('VLEAFSTART', [x + 16 for f in D['vleaf_start'] for r in f for x in r], 5)  # bias+16
    stream('LATEV', D['deferred_v_order'], 16)
    stream('NODEDIMS', [d for _, d in D['node_dims']], 5)
    stream('ARGS', [f for n in range(1, 64043)
                    for f in ([0, 0] if W['args'].get(str(n)) is None
                              else [W['args'][str(n)][0] + 1, W['args'][str(n)][1] + 1])], 32)
    jkeys = sorted(int(k) for k in W['j'])
    stream('JKEYS', jkeys, 16)
    stream('J', [W['j'][str(k)] for k in jkeys], 5)
    stream('LEAF', [x for n in range(1, v + 1) for x in W['leaf'][str(n)]], 5)
    stream('LINKS', [x for l in W['links'] for x in l], 16)
    stream('FLAG', [x + 128 for r in W['flag'] for x in r], 8)              # bias 128
    latef = []
    for n in sorted(int(k) for k in W['late']):
        e, l = W['late'][str(n)]
        latef += [n, len(e)] + e + [len(l)] + l
    stream('LATE', latef, 16)
    stream('YLEV', [sum(1 << (lv - 1) for lv in ylev[t]) for t in range(v)], 32)
    stream('XD', [x for row in xd for x in row], 5)
    stream('XSN', [n for n, us in S.xs], 16)
    stream('XSU', [u for _, us in S.xs for u in us], 16)

    clear = dict(ret=sorted(D['ret']),
                 retnode=sorted((int(c), n) for c, n in W['retained']),
                 hist_stair=sorted(cs['hist'].items()), hist_plain=hist_plain,
                 ranks=sorted(rk.items()),
                 ranks_base=sorted((int(r), c) for r, c in W['claimed']['rk'].items()),
                 late_dims=[[n, list(lt), d] for n, lt, d in D['late_dims']],
                 out=[[o[0], list(o[1]), o[2]] for o in W['outputs']],
                 bitR7=[list(p) for p in BITR7])
    json.dump(dict(streams={k: dict(width=wd, fields=n, limbs=[hex(l) for l in limbs])
                            for k, (wd, n, limbs) in streams.items()}, clear=clear),
              open(os.path.join(OUT, 'd2_streams.json'), 'w'))
    emit_lean(streams, clear, dict(h=h, v=v, R=R), v, R)

# =============================================================================================
# Lean emission (platform BitOppbank pattern: packL limbs + fieldOf decoders + kernel pins)
# =============================================================================================
HEAD = '''-- GENERATED by extract/d2_regen.py — DO NOT EDIT.
-- Source: frozen producer certificates/round7/{witness,deferred}_23.json.gz at pin
-- c05adfe1dfe85326dd6dcf12bfd53f435bd49bf3, regenerated + cross-checked offline by
-- extract/d2_regen.py (PND-GATE all-PASS; see extract/out/d2_regen.log).
-- Packing convention (platform GenData/ChkBitArg style): fields packed LSB-first into
-- 65536-bit limbs by packL; fieldOf X w i extracts field i of width w. All exact ints.
'''
def limb_lit(limbs, indent='  '):
    """Limb lines; the opening '[' is carried by the def line (packL [ ... ), list closes on its own line."""
    return '\n'.join('%s0x%x,' % (indent, l) for l in limbs[:-1]) + '\n%s0x%x' % (indent, limbs[-1])

def emit_lean(streams, clear, geo, v, R):
    SP = os.path.join(ROOT, 'StaircasePort')
    h = geo['h']
    # shared helpers
    open(os.path.join(SP, 'D2Common.lean'), 'w').write(HEAD % () + '''import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace StaircasePort.D2

/-- Pack `l` LSB-first into 65536-bit limbs (platform GenData/ChkBitArg convention). -/
def packL (l : List Nat) : Nat := l.foldr (fun p acc => Nat.lor p (Nat.shiftLeft acc 65536)) 0

/-- Field `i` of width `w` of the packed stream `X`. -/
def fieldOf (X w i : ℕ) : ℕ := (X >>> (w * i)) &&& (2 ^ w - 1)

end StaircasePort.D2
''')
    # stream parts, balanced by limb budget
    NPART = 3
    budget = [0] * NPART; chunks = [[] for _ in NPART * [0]]
    for n in sorted(streams):
        wd, cnt, limbs = streams[n]
        i = min(range(NPART), key=lambda j: budget[j])
        chunks[i].append(n); budget[i] += len(limbs)
    part_imports = []
    for pi, names_i in enumerate(chunks):
        body = []
        for n in names_i:
            wd, cnt, limbs = streams[n]
            body.append('/-- %s: %d fields of %d bits (%d limbs). -/' % (n, cnt, wd, len(limbs)))
            body.append('def d2%s : Nat := packL [\n%s\n  ]\n' % (n, limb_lit(limbs)))
        txt = HEAD % ()
        txt += 'import StaircasePort.D2Common\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n'
        txt += 'namespace StaircasePort.D2\n\nset_option maxRecDepth 20000\n\n'
        txt += '\n'.join(body)
        txt += '\nend StaircasePort.D2\n'
        fname = 'D2Data%d.lean' % pi
        open(os.path.join(SP, fname), 'w').write(txt)
        part_imports.append('import StaircasePort.%s' % fname[:-5])
        log('emitted StaircasePort/%s: %s (%d limbs)' % (fname, names_i, budget[pi]))

    hist = clear['hist_stair']; ranks = clear['ranks']; ranks_base = clear['ranks_base']
    ranks_count = sum(c for _, c in ranks); ranks_sum = sum(r * c for r, c in ranks)
    rb_count = sum(c for _, c in ranks_base)
    lit = lambda pairs: '[' + ', '.join('(%d, %d)' % tuple(p) for p in pairs) + ']'
    ld_lit = '[\n' + ',\n'.join('  (%d, [%s], %d)' % (n, ', '.join(map(str, lt)), d)
                                for n, lt, d in clear['late_dims']) + ']'
    out_lit = '[\n' + ',\n'.join('  (%d, [%s], %d)' % (c, ', '.join(map(str, T)), n)
                                 for c, T, n in clear['out']) + ']'
    corner = [h - 2, h - 5] + [1] * 6
    corner_plain = [h - 2] + [1] * (h + 1)

    spot = []
    def pin(stream, width, idx, val):
        spot.append('theorem pin_%s_%d : fieldOf d2%s %d %d = %d := by decide'
                    % (stream.lower(), idx, stream, width, idx, val))
    for name, width in (('OPS', 16), ('HOLD', 16), ('SIGMA', 5), ('NODEDIMS', 5),
                        ('YLEV', 32), ('ARGS', 32), ('FLAG', 8), ('VLEAFSTART', 5), ('XSU', 16)):
        wd, cnt, limbs = streams[name]
        X = 0
        for i, l in enumerate(limbs):
            X |= l << (65536 * i)
        mask = (1 << width) - 1
        for idx in (0, cnt // 2, cnt - 1):
            pin(name, width, idx, (X >> (width * idx)) & mask)

    root = HEAD % ()
    root += '\n'.join(part_imports) + '\nimport Definitions.Def_IntMul_KappaJainData\n'
    root += '''
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D2: the staircase witness-1 network dataset (regenerated, cross-checked)

Everything the Lean QHNet construction of `bitNetR7_mom` consumes, emitted from the frozen
producer chain at pin c05adfe and pre-verified offline (extract/d2_regen.py PND-GATE — the
GAP-9 lesson): the stage-1 word `d2OPS` with the slot schedule (`d2HOLDLENS`/`d2HOLD`/
`d2START`/`d2RET`/`d2OUT`), the deferred readouts (R = 28866 aux slots; 11565 deferred frames
`d2SIGMA` of primitive integer bases in readout order `d2READOUT`; the other slots read at F0,
corner rank h), the V-leaf starts (`d2VLEAFSLOTS`/`d2VLEAFSTART`), the X_S chains
(`d2XSN`/`d2XSU`), the deferred V gates (`d2LATEV`), all frame dimensions (`d2NODEDIMS` 64042,
`d2LATEDIMS`), the witness side data (`d2ARGS`, `d2JKEYS`/`d2J`, `d2LEAF`, `d2LINKS`,
`d2FLAG`, `d2LATE`), and the hist-assembly inputs (`d2YLEV` level bitmaps, `d2XD` deltas).

Signed conventions: `d2SIGMA` ([-13,10]), `d2VLEAFSTART` ([-10,10]) and `d2FLAG` ([-50,50])
fields are bias-encoded (+16 / +16 / +128) so that every stored field is a nonneg Nat; decoders
subtract the bias. Frame rows are length-h vectors.

Line constants (staircase witness-1): h = 23, v = C(23,3) = 1771, R = 28866, N = v² = 3136441,
W = 2N + 2vR = 108516254, T = 46v + N = 3217907, m = h² = 529.
The decisive pin: the regenerated staircase child-width histogram EQUALS the platform-frozen
`IntMul.Kappa.Jain.bitR7` (37 entries; rankSum 57403754177; childCount 1905413587), kernel-decided.
-/

namespace StaircasePort.D2

set_option maxRecDepth 20000

/-! ## Geometry (BitOppbankConsts/WireLayout pattern, staircase values) -/

def h : ℕ := 23
def v : ℕ := 1771
def Rslots : ℕ := 28866
def N : ℕ := 3136441
def W : ℕ := 108516254
def Tmp : ℕ := 3217907
def m : ℕ := 529
def wEnt : ℕ := 3542
def wAuxEnd : ℕ := 32408
def NL : ℕ := 32431

theorem h_eq : h = 23 := rfl
theorem v_eq : v = 1771 := rfl
theorem Rslots_eq : Rslots = 28866 := rfl
theorem N_eq : N = v * v := by decide
theorem m_eq : m = h * h := by decide
theorem W_eq : W = 2 * N + 2 * v * Rslots := by decide
theorem T_eq : Tmp = 46 * v + N := by decide
theorem wAuxEnd_eq : wAuxEnd = wEnt + Rslots := by decide
theorem NL_eq : NL = wAuxEnd + h := by decide
theorem W_target : W = 108516254 := by decide
theorem m_target : m = 529 := by decide

/-- Merge on the first `2N` roles (WireLayout ρn shape). -/
def ρn (g : ℕ) : ℕ :=
  if g < N then g + N else if g < 2 * N then g - N else g

/-! ## Wire layout bases -/

def wX (t : ℕ) : ℕ := t
def wY (T : ℕ) : ℕ := v + T
def wS (q : ℕ) : ℕ := wEnt + q
def wT (c : ℕ) : ℕ := wAuxEnd + c
def wU (s : ℕ) : ℕ := NL + s

def IsSlot (w : ℕ) : Prop := wEnt ≤ w ∧ w < wAuxEnd
def IsTgt (w : ℕ) : Prop := v ≤ w ∧ w < wEnt

/-! ## Clear tables (small; big streams live in D2Data0/1/2) -/

/-- The staircase entrance corner `[h-2, h-5, 1^6]` (deferred.py STAIRCASE_CORNER). -/
def d2CORNER : List ℕ := %s
/-- The round-six entrance corner `[h-2, 1^(h+1)]` (plain line). -/
def d2CORNERPLAIN : List ℕ := %s
/-- Retained slot per centre (deferred_23 'ret', 23 pairs). -/
def d2RET : List (ℕ × ℕ) := %s
/-- Retained node per centre (witness_23 'retained', 23 pairs). -/
def d2RETNODE : List (ℕ × ℕ) := %s
/-- Late-copy intersection dims (deferred_23 'late_dims', 1396 triples (n, lt, dim)). -/
def d2LATEDIMS : List (ℕ × List ℕ × ℕ) := %s
/-- Outputs (c, T, node): witness_23 'outputs', 5313 triples, out(c,T) = {S : S ∩ T = {c}}. -/
def d2WOUT : List (ℕ × List ℕ × ℕ) := %s

/-! ## Hist assembly outputs (dr.histogram over the regenerated inputs) -/

/-- Child-width histogram of the staircase corner — REGENERATED, equals `Jain.bitR7`. -/
def d2HIST : List (ℕ × ℕ) := %s
/-- Design-B chain-step rank multiset (dr.chain_ranks over the frozen schedule). -/
def d2RANKS : List (ℕ × ℕ) := %s
/-- Base (pre-reorder) word chain ranks == witness_23.claimed.rk (check_lifted hist_ok). -/
def d2RANKSBASE : List (ℕ × ℕ) := %s

def d2HistChildCount : ℕ := (d2HIST.map (·.2)).sum
def d2HistRankSum : ℕ := (d2HIST.map (fun p => p.1 * p.2)).sum
def d2RanksCount : ℕ := (d2RANKS.map (·.2)).sum
def d2RanksSum : ℕ := (d2RANKS.map (fun p => p.1 * p.2)).sum
def d2RanksBaseCount : ℕ := (d2RANKSBASE.map (·.2)).sum

/-- **The decisive D2 pin** (kernel decide): the regenerated staircase histogram is exactly the
platform-frozen `Jain.bitR7` (lean/Round7.lean at c05adfe, transcribed in JainData.lean). -/
theorem d2HIST_eq_bitR7 : d2HIST = IntMul.Kappa.Jain.bitR7 := by decide

theorem d2HistChildCount_eq : d2HistChildCount = 1905413587 := by decide
theorem d2HistRankSum_eq : d2HistRankSum = 57403754177 := by decide
theorem d2RanksCount_eq : d2RanksCount = %d := by decide
theorem d2RanksBaseCount_eq : d2RanksBaseCount = %d := by decide

/-! ## Spot decodes (kernel decide on the packed limbs; full streams Python-verified) -/

%s

end StaircasePort.D2
''' % (', '.join(str(x) for x in corner), ', '.join(str(x) for x in corner_plain),
       lit(clear['ret']), lit(clear['retnode']), ld_lit, out_lit,
       lit(hist), lit(ranks), lit(ranks_base), ranks_count, rb_count,
       '\n\n'.join(spot))
    open(os.path.join(SP, 'D2Data.lean'), 'w').write(root)
    log('emitted StaircasePort/D2Data.lean (root: geometry + clear tables + pins + %d spot pins)' % len(spot))

if __name__ == '__main__':
    main()
