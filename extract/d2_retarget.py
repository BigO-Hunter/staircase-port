#!/usr/bin/env python3
"""D2 table retarget (STAGE 2, lane formalok-port) — the GREC/D2 -> Rec/chunk pack at R7 geometry.

WHAT THIS DELIVERS (and what it deliberately does NOT):
  * the R7 label-pack geometry (NL = wAuxEnd + h = 32431) and the CODE WIDTH DECISION, measured:
    the frozen d2 stage word has max node id 64042, and the R6/R8 code base is cbase = v + 2 = 1773,
    so max code = 65815 > 2^16 - 1 = 65535. The R8 GenData pack used 16-bit fields because R8's
    densified node count (62478) fit; d2's does NOT. The retarget therefore packs 17-bit fields.
    (Derived, not inherited: the field width is a function of the node count, and the node count
    changed with the dataset.)
  * SG_slots0: the initial label state over the slot band (wS q = wEnt + q, code = cbase + hold[q][0]),
    packed at 17-bit fields, with a FULL round-trip decode gate over all NL fields.
  * the exact list of platform definitions the Rec/chunk construction still needs, with a filesystem
    audit proving which are absent locally (so the resume point is a named dependency, not a guess).

NOT delivered (deliberately, no invention): the Rec (= LInstr) list itself. Deriving
(code, moves, gates) from the design-B word requires the R6 `Loc`/GenData encoder semantics
(injS / retS / the cND densify pass), whose definitions are absent from BOTH this checkout and
prove2me_workspace/Definitions. Guessing them would fabricate a table; the audit below is the
receipt that says so.

Exact ints only, stdlib only. No writes outside extract/out/ and the emitted Lean module.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
OUT = os.path.join(HERE, 'out')
sys.path[:0] = [os.path.join(HERE, 'jainroot', 'scripts'),
                os.path.join(HERE, 'jainroot', 'independent', 'two-stage-bit'),
                os.path.join(HERE, 'jainroot', 'independent', 'deferred-readout')]
import deferred as dr  # noqa: E402

LOG = []
VERDICTS = []


def log(*a):
    line = ' '.join(str(x) for x in a)
    LOG.append(line)
    print(line, flush=True)


def verdict(name, ok, detail=''):
    VERDICTS.append((name, bool(ok), detail))
    log('PND %-52s %s %s' % (name, 'PASS' if ok else 'FAIL', detail))
    if not ok:
        raise SystemExit('RETARGET-GATE FAILURE: %s %s' % (name, detail))


# ---------------------------------------------------------------- geometry (R7 retarget)
def geometry(R):
    h, v = 23, 1771
    wEnt = 2 * v
    wAuxEnd = wEnt + R
    NL = wAuxEnd + h              # R8 template: NL = 2v + NR + h  (31359 = 31336 + 23)
    N = v * v
    W = 2 * N + 2 * v * R
    Tmp = 2 * h * v + N
    return dict(h=h, v=v, R=R, wEnt=wEnt, wAuxEnd=wAuxEnd, NL=NL, N=N, W=W, Tmp=Tmp,
                cbase=v + 2)


# ---------------------------------------------------------------- dependency audit
NEEDED = {
    # name -> candidate paths (relative to each root searched)
    'R6 Defs51 (genF/genStepF/mvF/codeOf/Loc: injS/retS/GREC Rec encoder)':
        ['Definitions/Def_IntMul_Kappa_R6_Defs51.lean'],
    'R6 GenData_1 (Rec/chunk label packs SG1_*)':
        ['Definitions/Def_IntMul_Kappa_R6_Data_BitNBGenData_1.lean'],
    'R6 GenData_2 (stage-2 packs SG2_*)':
        ['Definitions/Def_IntMul_Kappa_R6_Data_BitNBGenData_2.lean'],
    'R6 Defs52 (NB program assembly)':
        ['Definitions/Def_IntMul_Kappa_R6_Defs52.lean'],
}
ROOTS = [os.path.expanduser('~/bigo-campaign/staircase-port'),
         os.path.expanduser('~/prove2me_workspace')]


def audit():
    present, absent = {}, {}
    for name, rels in NEEDED.items():
        hits = [os.path.join(r, rel) for r in ROOTS for rel in rels
                if os.path.exists(os.path.join(r, rel))]
        (present if hits else absent)[name] = hits
        log('DEP %-6s %s' % ('FOUND' if hits else 'ABSENT', name),
            ' '.join(hits) if hits else '(searched: ' + ', '.join(ROOTS) + ')')
    return present, absent


# ---------------------------------------------------------------- packing (Python mirror)
def catB(B, xs):
    acc = 0
    for x in reversed(xs):
        acc = (acc << B) | x
    return acc


def fieldOf(S, w, i):
    return (S >> (w * i)) & ((1 << w) - 1)


def main():
    os.makedirs(OUT, exist_ok=True)
    W, D = dr.load(23, 'witness_23.json.gz', 'deferred_23.json.gz')
    S = dr.Schedule(W, D)
    G = geometry(S.R)

    # ---- A. geometry matches the frozen dataset and the D2Data pins
    verdict('geometry.R == frozen R', G['R'] == D['R'], 'R=%d' % G['R'])
    verdict('geometry.NL == 2v+NR+h', G['NL'] == 2 * G['v'] + G['R'] + G['h'], 'NL=%d' % G['NL'])
    verdict('geometry.W == 2N+2vR', G['W'] == 2 * G['N'] + 2 * G['v'] * G['R'], 'W=%d' % G['W'])
    verdict('geometry.Tmp == 46v+N', G['Tmp'] == 46 * G['v'] + G['N'], 'Tmp=%d' % G['Tmp'])
    verdict('R==28866 (D2Data)', G['R'] == 28866, '')
    verdict('NL==32431 (R7; R8 was 31359)', G['NL'] == 32431, 'NL=%d' % G['NL'])

    # ---- B. the frozen word's maxima
    nodes = set()
    for hl in S.hold:
        nodes.update(hl)
    maxNode = max(nodes)
    nNodes = len(nodes)
    adds = sum(1 for o in S.ops if o[0] == 'add')
    verdict('node span 1..64042', min(nodes) == 1 and maxNode == 64042,
            'min=%d max=%d distinct=%d' % (min(nodes), maxNode, nNodes))
    verdict('node count == v + adds', nNodes == G['v'] + adds,
            'nodes=%d v+adds=%d' % (nNodes, G['v'] + adds))

    # ---- C. THE WIDTH DECISION (measured, not inherited)
    cbase = G['cbase']
    maxCode = cbase + maxNode
    verdict('cbase == v+2 == 1773', cbase == 1773, '')
    verdict('16-bit fields are INSUFFICIENT for the d2 word',
            maxCode > (1 << 16) - 1, 'maxCode=%d > 65535' % maxCode)
    width = 17
    verdict('17-bit fields suffices', maxCode <= (1 << width) - 1,
            'maxCode=%d <= %d' % (maxCode, (1 << width) - 1))

    # ---- D. every wire's initial code must fit the field too
    codes0 = [0] * G['NL']
    for q in range(G['R']):
        codes0[G['wEnt'] + q] = cbase + S.hold[q][0]
    verdict('all initial wire codes < 2^width', max(codes0) <= (1 << width) - 1,
            'max init code=%d' % max(codes0))

    # ---- E. the entry-band source leaves (v src slots) are the 'src' start codes
    src_starts = [(s, st[1]) for s, st in enumerate(S.start) if st[0] == 'src']
    verdict("count('src' starts) == v", len(src_starts) == G['v'], 'n=%d' % len(src_starts))

    # ---- F. FULL round-trip decode of the packed seed over all NL fields
    packed = catB(width, codes0)
    back = [fieldOf(packed, width, i) for i in range(G['NL'])]
    # catB puts index 0 in the MOST significant slot -> fieldOf index i reads the tail;
    # check both orientations explicitly so the convention is pinned, not assumed.
    ok_fwd = back == list(reversed(codes0))
    ok_rev = back == codes0
    verdict('pack/decode round-trips (reversed-field convention pinned)', ok_fwd or ok_rev,
            'orientation=%s' % ('reversed' if ok_fwd else ('identity' if ok_rev else 'MISMATCH')))
    orientation = 'reversed' if ok_fwd else 'identity'

    # ---- G. emission: hex limbs of 3855 fields (17 * 3855 = 65535 bits)
    per_limb = (65535 // width)
    limbs = []
    for start in range(0, len(codes0), per_limb):
        limbs.append('0x%x' % catB(width, codes0[start:start + per_limb]))
    verdict('limb count * %d fields covers NL' % per_limb, len(limbs) * per_limb >= G['NL'],
            'limbs=%d' % len(limbs))

    present, absent = audit()

    cert = dict(geometry=G, maxNode=maxNode, nNodes=nNodes, adds=adds, cbase=cbase,
                maxCode=maxCode, codeWidth=width, orientation=orientation,
                limbFields=per_limb, limbCount=len(limbs),
                seedMaxCode=max(codes0), verdicts=VERDICTS,
                dependencies_present=present, dependencies_absent=absent,
                not_delivered=['Rec/LInstr list (needs the R6 Loc/GenData encoder)',
                               'cs1/cs2 chunk lists', 'stage-2 (SG2) packs'])
    with open(os.path.join(OUT, 'd2_retarget.json'), 'w') as f:
        json.dump(cert, f, indent=1)

    # ---- H. emit the Lean data module
    lean = []
    lean.append('import Mathlib')
    lean.append('')
    lean.append('set_option autoImplicit false')
    lean.append('set_option relaxedAutoImplicit false')
    lean.append('')
    lean.append('/-!')
    lean.append('# D2 -> Rec/chunk table retarget, part 1: geometry, code width, slot-band seed')
    lean.append('')
    lean.append('GENERATED by extract/d2_retarget.py from the frozen design-B word; do not hand-edit.')
    lean.append('Certificate: extract/out/d2_retarget.json (all PND verdicts PASS).')
    lean.append('')
    lean.append('## The width decision (measured, not inherited)')
    lean.append('The R6/R8 label pack stores one code per wire in a fixed-width field; the code of')
    lean.append('node `n` is `cbase + n` with `cbase = v + 2 = 1773`. R8 packed 16-bit fields and its')
    lean.append('densified node count (62478, max code 64251) fit. The d2 word has 64042 nodes, so its')
    lean.append('max code is 65815 > 65535: **16-bit fields are insufficient here**, and this module')
    lean.append('lays the pack out at 17-bit fields. `width16_fails` / `width17_suffices` below are')
    lean.append('the machine-checked halves of that decision.')
    lean.append('')
    lean.append('## What is packed')
    lean.append('`SG_slots0`: the initial label state over the slot band only —')
    lean.append('`code(wS q) = cbase + hold[q][0]` for `q < NR`, zero elsewhere. `hold` is the frozen,')
    lean.append('replay-verified slot->node time line, so this table is certified data, not a guess.')
    lean.append('The entry band (`wX`/`wY`, the `v` source-leaf slots) and the temp bands are NOT')
    lean.append('part of this seed; they ride the same `hold`/`start` streams once the Rec encoder')
    lean.append('lands.')
    lean.append('')
    lean.append('## Deliberately NOT delivered')
    lean.append('The `Rec` (= `LInstr`) list: `(code, moves, gates)` per step. Constructing it needs')
    lean.append('the R6 `Loc`/GenData encoder (`injS`/`retS` + the `cND` densify pass), absent from')
    lean.append('this checkout AND from prove2me_workspace/Definitions (`dependencies_absent` in the')
    lean.append('certificate). Deriving it by guesswork would fabricate a table; the audit names the')
    lean.append('dependency instead. `genF` itself is already ported (`StaircasePort.QL.LabGen`).')
    lean.append('-/')
    lean.append('')
    lean.append('namespace StaircasePort.QT')
    lean.append('')
    lean.append('/-! ## Geometry (R7 retarget; = DenseProg.QD / D2Data constants) -/')
    lean.append('')
    lean.append('def h : ℕ := %d' % G['h'])
    lean.append('def v : ℕ := %d' % G['v'])
    lean.append('def NR : ℕ := %d' % G['R'])
    lean.append('def wEnt : ℕ := %d' % G['wEnt'])
    lean.append('def wAuxEnd : ℕ := %d' % G['wAuxEnd'])
    lean.append('def NL : ℕ := %d' % G['NL'])
    lean.append('')
    lean.append('theorem NL_eq : NL = %d := rfl' % G['NL'])
    lean.append('theorem wAuxEnd_eq : wAuxEnd = %d := rfl' % G['wAuxEnd'])
    lean.append('theorem NL_shape : NL = 2 * v + NR + h := rfl')
    lean.append('')
    lean.append('/-! ## The code alphabet -/')
    lean.append('')
    lean.append('/-- Node ids of the frozen design-B word: `1 .. nNodes`. -/')
    lean.append('def nNodes : ℕ := %d' % nNodes)
    lean.append('theorem nNodes_eq : nNodes = 64042 := rfl')
    lean.append('')
    lean.append('/-- Code base: `code n = cbase + n` (`cbase = v + 2`, the R6 `cND` offset). -/')
    lean.append('def cbase : ℕ := %d' % cbase)
    lean.append('theorem cbase_eq : cbase = 1773 := rfl')
    lean.append('theorem cbase_shape : cbase = v + 2 := rfl')
    lean.append('')
    lean.append('/-- Field width of the code pack for THIS dataset. -/')
    lean.append('def codeWidth : ℕ := %d' % width)
    lean.append('')
    lean.append('/-- Maximum code in the word. -/')
    lean.append('def maxCode : ℕ := %d' % maxCode)
    lean.append('theorem maxCode_eq : maxCode = cbase + nNodes := rfl')
    lean.append('')
    lean.append('/-- **16-bit fields cannot hold this word.** The R8 pack size does not transfer:')
    lean.append('the field width is a function of the node count, and d2 has 1564 more nodes than R8. -/')
    lean.append('theorem width16_fails : maxCode > 2 ^ 16 - 1 := by decide')
    lean.append('')
    lean.append('/-- 17-bit fields suffice. -/')
    lean.append('theorem width17_suffices : maxCode ≤ 2 ^ 17 - 1 := by decide')
    lean.append('')
    lean.append('/-- Every code fits the chosen width. -/')
    lean.append('theorem codes_fit (n : ℕ) (hn : n ≤ nNodes) : cbase + n ≤ 2 ^ 17 - 1 := by')
    lean.append('  have hp : (2 : ℕ) ^ 17 = 131072 := by norm_num')
    lean.append('  have hc : cbase = 1773 := rfl')
    lean.append('  have hn2 : nNodes = 64042 := rfl')
    lean.append('  omega')
    lean.append('')
    lean.append('/-! ## Packing primitives (width-parametric; the R8 `catB`/`fieldOf` shapes) -/')
    lean.append('')
    lean.append('/-- Little-endian bit catenation: element 0 lands in the MOST significant field.')
    lean.append('(The R8 seed file uses the same `foldr`; `orientation` in the certificate pins which')
    lean.append('index `fieldOf` then reads.) -/')
    lean.append('def catB (B : ℕ) (l : List ℕ) : ℕ := l.foldr (fun x acc => x ||| (acc <<< B)) 0')
    lean.append('')
    lean.append('/-- Width-`w` field `i` of a packed code state. -/')
    lean.append('def fieldOf (X w i : ℕ) : ℕ := (X >>> (w * i)) &&& (2 ^ w - 1)')
    lean.append('')
    lean.append('/-- Pack a code function over `NL` wires. -/')
    lean.append('def packCodes (f : ℕ → ℕ) : ℕ := catB 17 ((List.range NL).map f)')
    lean.append('')
    lean.append('/-- Decode a wire. `foldr (fun x acc => x ||| (acc <<< B))` puts element 0 in the')
    lean.append('LOWEST field, so wire `w` is field `w` (the certificate pins orientation=identity by')
    lean.append('a full %d-field round-trip). NOTE: this is a *full* 17-bit code per field; the R8')
    lean.append('GenData_0 words appear to shift the code by 4 (code<<4) to leave a dim nibble, which')
    lean.append('this pack does NOT replicate - the two packings are not interchangeable. -/')
    lean.append('def codeOf (S : ℕ) (w : ℕ) : ℕ := fieldOf S 17 w')
    lean.append('')
    lean.append('/-! ## `SG_slots0` — the slot-band initial label state -/')
    lean.append('')
    lean.append('/-- `packL` over %d-field limbs (17 * %d = 65535 bits per limb). -/' % (per_limb, per_limb))
    lean.append('def packL (l : List ℕ) : ℕ := catB 65535 l')
    lean.append('')
    lean.append('/-- Packed initial codes: `code(wS q) = cbase + hold[q][0]`, entry/temp bands zero.')
    lean.append('Certificate `orientation=%s`, `seedMaxCode=%d`, full %d-field round-trip PASS. -/'
                % (orientation, max(codes0), G['NL']))
    lean.append('def SG_slots0 : ℕ := packL [')
    for i, l in enumerate(limbs):
        lean.append('  %s%s' % (l, ',' if i + 1 < len(limbs) else ''))
    lean.append('  ]')
    lean.append('')
    lean.append('/-! ## Decode pins (sampled; the full round-trip is the certificate) -/')
    lean.append('')
    for q in (0, 1, G['R'] // 2, G['R'] - 1):
        w = G['wEnt'] + q
        lean.append('theorem seed_field_%d : codeOf SG_slots0 %d = %d := by decide'
                    % (q, w, codes0[w]))
    lean.append('')
    lean.append('end StaircasePort.QT')
    lean.append('')

    path = os.path.join(ROOT, 'StaircasePort', 'D2Chunks.lean')
    with open(path, 'w') as f:
        f.write('\n'.join(lean))
    log('wrote', path, '(%d lines)' % len(lean))
    with open(os.path.join(OUT, 'd2_retarget.log'), 'w') as f:
        f.write('\n'.join(LOG) + '\n')


if __name__ == '__main__':
    main()
