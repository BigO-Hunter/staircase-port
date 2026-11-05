"""N2c emitter v2: builds the complete Lean text for N2c (data + proofs) as
n2c_block.lean, to be spliced into StaircasePort/Pivot.lean replacing the N2c sorry.

Minors are found SYSTEMATICALLY (echelon over F_P: the independent rows plus the pivot
columns give an invertible square minor), not randomly.
"""
import json, re, os
PROBE = os.environ.get('N2C_PROBE') == '1'

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
pc = [44] + [22 + k for k in range(1, 22)] + [22, 21, 20] + [k for k in range(2, 20)] + [1, 0]
n = 45
assert sorted(pc) == list(range(n))
def rho(X, Y): return sum(1 for r in range(X) if pc[r] >= Y)

def rowmod(r, cols, p=P): return [Q[r][c] % p for c in cols]

def echelon_minor(rows, cols, t, p=P, order='asc'):
    """Independent rows (in `order` of preference) + pivot columns of the block."""
    basis = []      # reduced rows
    piv = []        # pivot column index (within `cols`)
    chosen = []
    rws = sorted(rows) if order == 'asc' else sorted(rows, reverse=True)
    for r in rws:
        v = rowmod(r, cols, p)
        for (bv, bp) in zip(basis, piv):
            if v[bp]:
                f = v[bp]
                v = [(v[k] - f * bv[k]) % p for k in range(len(cols))]
        nz = next((k for k in range(len(cols)) if v[k]), None)
        if nz is None: continue
        inv = pow(v[nz], p - 2, p)
        basis.append([x * inv % p for x in v]); piv.append(nz); chosen.append(r)
        if len(chosen) == t: break
    if len(chosen) < t: return None
    return sorted(chosen), sorted(cols[k] for k in piv)

def det_inv_mod(S, p=P):
    nn = len(S)
    M = [[S[i][j] % p for j in range(nn)] + [1 if i == j else 0 for j in range(nn)] for i in range(nn)]
    det = 1
    for c in range(nn):
        pivr = None
        for r in range(c, nn):
            if M[r][c] % p: pivr = r; break
        if pivr is None: return 0, None
        if pivr != c: M[c], M[pivr] = M[pivr], M[c]; det = -det
        det = det * M[c][c] % p
        inv = pow(M[c][c], p - 2, p)
        M[c] = [(v * inv) % p for v in M[c]]
        for r in range(nn):
            if r != c and M[r][c] % p:
                f = M[r][c]
                M[r] = [(M[r][k] - f * M[c][k]) % p for k in range(2 * nn)]
    return det % p, [row[nn:] for row in M]

certs = []; bykey = {}
def add_cert(R, Cc):
    R = sorted(R); Cc = sorted(Cc)
    key = (tuple(R), tuple(Cc))
    if key in bykey: return bykey[key]
    S = [[Q[r][c] % P for c in Cc] for r in R]
    det, inv = det_inv_mod(S)
    assert det != 0, ('singular minor', R, Cc)
    cols = [[inv[l][j] for l in range(len(Cc))] for j in range(len(Cc))]
    c = {'R': R, 'C': Cc, 'S': S, 'T': cols, 'det': det}
    certs.append(c); bykey[key] = c
    return c

def covers(c, X, Y, t):
    return len(c['R']) == t and max(c['R']) < X and min(c['C']) >= Y

needB = [(i + 1, pc[i], rho(i, pc[i]) + 1) for i in range(n)]
needC = [(i, pc[i] + 1, rho(i, pc[i])) for i in range(n) if rho(i, pc[i]) > 0]

def build():
    order = [('asc', 'asc'), ('asc', 'desc'), ('desc', 'desc'), ('desc', 'asc')]
    while True:
        pending = []
        for i in range(n):
            j = pc[i]; k = rho(i, j)
            for (kind, X, Y, t) in (('B', i + 1, j, k + 1), ('C', i, j + 1, k)):
                if t == 0: continue
                if any(covers(c, X, Y, t) for c in certs): continue
                pending.append((X, Y, t))
        # order pending by size desc so big minors are chosen first (cheap ones stay cheap)
        pending = sorted(set(pending), key=lambda z: -z[2])
        if not pending: break
        best = None
        for (X, Y, t) in pending:
            for (ro, co) in order:
                cols = list(range(Y, 45))
                if co == 'desc':
                    cols = cols[::-1]
                got = echelon_minor(range(X), cols, t, order=ro)
                if not got: continue
                R, Cc = got
                # how many currently-uncovered needs does this cert cover?
                gain = sum(1 for (k2, X2, Y2, t2) in
                           [('B', pc_[0], pc_[1], pc_[2]) for pc_ in []] or [])
                gain = 0
                for ii in range(n):
                    jj = pc[ii]; kk = rho(ii, jj)
                    for (kind, X2, Y2, t2) in (('B', ii + 1, jj, kk + 1), ('C', ii, jj + 1, kk)):
                        if t2 == 0 or t2 != len(R): continue
                        if any(covers(c, X2, Y2, t2) for c in certs): continue
                        if max(R) < X2 and min(Cc) >= Y2: gain += 1
                if best is None or gain > best[0]:
                    best = (gain, R, Cc)
        assert best, ('stuck', pending)
        add_cert(best[1], best[2])
build()
cov = set()
for c in certs:
    for kind, need in (('B', needB), ('C', needC)):
        for bb in need:
            if covers(c, *bb): cov.add((kind,) + bb)
missing = [('B',) + bb for bb in needB if ('B',) + bb not in cov] + \
          [('C',) + bb for bb in needC if ('C',) + bb not in cov]
print('certs:', len(certs), 'missing:', missing)
assert not missing
print('certChk mults:', sum(len(c['R']) ** 3 for c in certs),
      'entry checks:', sum(len(c['R']) ** 2 for c in certs))
print('sizes:', [len(c['R']) for c in certs])

# ---- upper-bound sources ----
blk = {}
ne = open('StaircasePort/NEBlocks.lean').read()
mre = re.search(r'def stairNEBlocks\s*:\s*List\s*\([^)]*\)\s*:=\s*\[(.*?)\]\s*\n\ntheorem', ne, re.S)
for t4 in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)', mre.group(1)):
    blk[(int(t4[0]), int(t4[1]))] = (int(t4[2]), int(t4[3]))
upper = {}
for i in range(n):
    j = pc[i]; k = rho(i, j)
    for (X, Y, t) in ((i, j, k), (i + 1, j, k + 1), (i, j + 1, k), (i + 1, j + 1, k)):
        if (X, Y, t) in upper: continue
        assert Y <= 45
        if t == min(X, n - Y):
            upper[(X, Y, t)] = ('height' if X <= n - Y else 'width', t)
        else:
            e = blk[(X - 1, Y)]
            assert e[1] <= t
            upper[(X, Y, t)] = ('table', e[0], e[1])

if PROBE:
    keep = []
    for i in (0, 1):
        j = pc[i]; k = rho(i, j)
        for c in certs:
            if covers(c, i + 1, j, k + 1) or (k and covers(c, i, j + 1, k)):
                if not any(c is d for d in keep): keep.append(c)
    certs[:] = keep
    print('PROBE mode: certs', [len(c['R']) for c in certs])

def natlist(l): return '[' + ', '.join(str(v) for v in l) + ']'
def nrows(S): return '[' + ',\n   '.join(natlist(r) for r in S) + ']'

THEAD = """/-! ### N2c — the rightmost-pivot lower bound at the extracted witness (check_stair item 3)

`stairPC` is the extracted rightmost-pivot pattern (staircase_data.json `pc`), a permutation
of `0..44`; the corner runs are exactly its graph (`stairCornerRuns45_pairs`, kernel
`decide`). For row `i` the four NE blocks around `(i, pc i)` have

  A = rk q i (pc i) = k,     B = rk q (i+1) (pc i) = k+1,
  C = rk q i (pc i+1) = k,   D = rk q (i+1) (pc i+1) = k,   k = #{r < i | pc r ≥ pc i},

which is `IsPiv q i (pc i)` by `isPiv_of_bounds`. Uppers are trivial (`min(#rows,#cols)`) or
N2b's cut table (`rkQ_le_of_block`); lowers are explicit nonzero minors certified by a
modular inverse mod `stairCertP` (the N3 `certChk` mechanism) — `n2c_rank_lower`.
-/

/-- The extracted rightmost-pivot pattern: row `i`'s rightmost pivot is column `pc i`. -/
def stairPC : List ℕ := @@PC@@

/-- The extracted corner runs are exactly the graph of `stairPC`. -/
theorem stairCornerRuns45_pairs :
    runPairs stairCornerRuns45 = (List.range 45).map (fun i => (i, stairPC.getD i 0)) := by
  decide

/-! #### generic rank lemmas -/

/-- NE-block rank is monotone in the row cut. -/
lemma rk_rows_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X X' Y : ℕ} (h : X ≤ X') : rk q X Y ≤ rk q X' Y := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X'} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} =>
          (⟨r.1, by have := r.2; omega⟩ : {r : Fin a // r.val < X'})) (fun c => c) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- NE-block rank is monotone in the column cut (larger `Y` = smaller block). -/
lemma rk_cols_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X Y Y' : ℕ} (h : Y' ≤ Y) : rk q X Y ≤ rk q X Y' := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y' ≤ c.val} => c.1)).submatrix (fun r => r)
        (fun c : {c : Fin b // Y ≤ c.val} =>
          (⟨c.1, by have := c.2; omega⟩ : {c : Fin b // Y' ≤ c.val})) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- Trivial height bound. -/
lemma rk_le_height {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) : rk q X Y ≤ X := by
  rw [rk]
  refine (Matrix.rank_le_card_height _).trans ?_
  exact Fintype.card_le_of_embedding
    ⟨fun r : {r : Fin a // r.val < X} => (⟨r.1.val, r.2⟩ : Fin X), fun u v huv => by
      simp only [Fin.mk.injEq, Subtype.mk.injEq] at huv
      exact Subtype.ext (Fin.ext huv)⟩

/-- Trivial width bound. -/
lemma rk_le_width {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) (hY : Y ≤ b) : rk q X Y ≤ b - Y := by
  rw [rk]
  refine (Matrix.rank_le_card_width _).trans ?_
  exact Fintype.card_le_of_embedding
    ⟨fun c : {c : Fin b // Y ≤ c.val} =>
        (⟨c.1.val - Y, by have := c.2; have := c.1.isLt; omega⟩ : Fin (b - Y)),
      fun u v huv => by
      simp only [Fin.mk.injEq] at huv
      have h1 := u.2; have h2 := v.2
      exact Subtype.ext (Fin.ext (by omega))⟩

/-- A nonzero `n × n` minor forces `n ≤` the NE-block rank. -/
lemma rk_ge_of_det {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) {n_ : ℕ} (R : Fin n_ → {r : Fin a // r.val < X})
    (Cc : Fin n_ → {c : Fin b // Y ≤ c.val})
    (hdet : (Matrix.of fun i j => q (R i).1 (Cc j).1).det ≠ 0) : n_ ≤ rk q X Y := by
  have h1 : (Matrix.of fun i j => q (R i).1 (Cc j).1).rank = n_ := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
  have h2 : ((q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
      (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix R Cc).rank =
      (Matrix.of fun i j => q (R i).1 (Cc j).1).rank := rfl
  rw [← h1, ← h2, rk]
  exact Matrix.rank_submatrix_le _ _ _

/-- `IsPiv` from four exact rank values. -/
lemma isPiv_of_exact {a b : ℕ} (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j = k) (hB : rk q (i+1) j = k+1)
    (hC : rk q i (j+1) = k) (hD : rk q (i+1) (j+1) = k) : IsPiv q i j := by
  unfold IsPiv
  rw [hA, hB, hC, hD]
  omega

/-- `IsPiv` from two-sided bounds. -/
lemma isPiv_of_bounds {a b : ℕ} (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j ≤ k) (hB : rk q (i+1) j ≤ k+1)
    (hC : rk q i (j+1) ≤ k) (hD : rk q (i+1) (j+1) ≤ k)
    (hBlo : k+1 ≤ rk q (i+1) j) (hClo : k ≤ rk q i (j+1)) : IsPiv q i j := by
  have hAe : rk q i j = k := le_antisymm hA (hClo.trans (rk_cols_mono q (by omega)))
  have hCe : rk q i (j+1) = k := le_antisymm hC hClo
  have hDe : rk q (i+1) (j+1) = k := le_antisymm hD (hClo.trans (rk_rows_mono q (by omega)))
  exact isPiv_of_exact q i j k hAe (le_antisymm hB hBlo) hCe hDe

/-- N2b's cut bound, restated for `stairCornerQ` at the table block `(X-1, Y)`. -/
lemma rkQ_le_of_block (X Y c r : ℕ) (h : (X - 1, Y, r, c) ∈ stairNEBlocks) :
    rk stairCornerQ X Y ≤ c := by
  have hb := stairNE_rk_le stairQX1 stairQY1 stairQX2 stairQY2 (X - 1, Y, r, c) h
  simpa [stairCornerQ, stairMQ, stairPairM] using hb

/-- **The modular minor certificate as a rank lower bound.** `rl`/`cl` are the minor's
row/column indices, `rows` the minor mod `stairCertP` and `cols` the transpose of its
inverse mod `stairCertP` (the N3 `certChk` convention); `hent` pins `rows` against the
concrete corner entries. -/
lemma n2c_rank_lower {n_ X Y : ℕ} (hX : X ≤ 45) (rl cl : List ℕ)
    (hrl : ∀ i : Fin n_, rl.getD i.val 0 < X)
    (hcl : ∀ i : Fin n_, Y ≤ cl.getD i.val 0)
    (rows cols : List (List ℕ))
    (hchk : certChk rows cols n_ stairCertP = true)
    (hent : ((List.range n_).all fun i => (List.range n_).all fun j =>
      decide (corZStair stairMZ (rl.getD i 0) (cl.getD j 0) % (stairCertP : ℤ) =
        (((rows.getD i []).getD j 0 : ℕ) : ℤ))) = true) :
    n_ ≤ rk stairCornerQ X Y := by
  set Dz : Matrix (Fin n_) (Fin n_) ℤ :=
    Matrix.of fun i j => corZStair stairMZ (rl.getD i.val 0) (cl.getD j.val 0) with hDz
  have hentQ : (Matrix.of fun i j : Fin n_ =>
        stairCornerQ (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
          (⟨cl.getD j.val 0, by have := hcl j; omega⟩ : Fin 45)) =
      Dz.map (Int.cast : ℤ → ℚ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, hDz, stairCornerQ, stairCornerQOf,
      ← stairMZ_map, corStairQ_cast]
  have hdetQ : (Dz.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    have e1 : (Dz.map (Int.cast : ℤ → ℚ)).det = ((Dz.det : ℤ) : ℚ) := by
      have h := RingHom.map_det (Int.castRingHom ℚ) Dz
      rw [RingHom.mapMatrix_apply] at h
      exact h.symm
    rw [e1, Int.cast_ne_zero]
    intro h0
    have e2 := RingHom.map_det (Int.castRingHom (ZMod stairCertP)) Dz
    rw [RingHom.mapMatrix_apply, h0, map_zero] at e2
    have e3 : Dz.map (Int.castRingHom (ZMod stairCertP)) =
        Matrix.of fun i l : Fin n_ =>
          (((rows.getD i.val []).getD l.val 0 : ℕ) : ZMod stairCertP) := by
      ext i l
      rw [Matrix.map_apply, hDz, Matrix.of_apply, Matrix.of_apply]
      have hc := hent
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
      rw [← ZMod.intCast_mod, hc i.val i.isLt l.val l.isLt, Int.cast_natCast]
    rw [e3] at e2
    exact det_ne_zero_of_certChk rows cols hchk e2.symm
  rw [hentQ]
  exact rk_ge_of_det stairCornerQ X Y
    (fun i => ⟨⟨rl.getD i.val 0, by have := hrl i; omega⟩, hrl i⟩)
    (fun j => ⟨⟨cl.getD j.val 0, by have := hcl j; omega⟩, hcl j⟩) hdetQ"""

out = [THEAD.replace('@@PC@@', natlist(pc))]
for idx, c in enumerate(certs):
    lbl = (str(c['R'][0]) + '..' + str(c['R'][-1])) if len(c['R']) > 2 else str(c['R'])
    lbc = (str(c['C'][0]) + '..' + str(c['C'][-1])) if len(c['C']) > 2 else str(c['C'])
    out.append(f"""
/-- N2c minor certificate {idx}: rows {lbl}, cols {lbc} (det mod P = {c['det']}). -/
def n2cR{idx} : List ℕ := {natlist(c['R'])}
def n2cC{idx} : List ℕ := {natlist(c['C'])}
def n2cS{idx} : List (List ℕ) := {nrows(c['S'])}
def n2cT{idx} : List (List ℕ) := {nrows(c['T'])}""")
out.append("")
for idx, c in enumerate(certs):
    nn = len(c['R'])
    out.append(f"""
theorem n2cChk{idx} : certChk n2cS{idx} n2cT{idx} {nn} stairCertP = true := by decide +kernel
theorem n2cEnt{idx} : ((List.range {nn}).all fun i => (List.range {nn}).all fun j =>
    decide (corZStair stairMZ (n2cR{idx}.getD i 0) (n2cC{idx}.getD j 0) % (stairCertP : ℤ) =
      (((n2cS{idx}.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel""")

def up_proof(X, Y, t, src):
    if src[0] == 'height': return "exact rk_le_height stairCornerQ %d %d" % (X, Y)
    if src[0] == 'width': return "refine rk_le_width stairCornerQ %d %d (by decide)" % (X, Y)
    return "exact rkQ_le_of_block %d %d %d %d (by decide)" % (X, Y, t, src[1])

def cert_use(c):
    idx = certs.index(c)
    return ("refine n2c_rank_lower (by decide) n2cR%d n2cC%d (by decide) (by decide) "
            "n2cS%d n2cT%d n2cChk%d n2cEnt%d" % (idx, idx, idx, idx, idx, idx))

for i in (range(2) if PROBE else range(n)):
    j = pc[i]; k = rho(i, j)
    srcs = [upper[(i, j, k)], upper[(i + 1, j, k + 1)], upper[(i, j + 1, k)],
            upper[(i + 1, j + 1, k)]]
    cb = next(c for c in certs if covers(c, i + 1, j, k + 1))
    cc = next((c for c in certs if k and covers(c, i, j + 1, k)), None)
    body = ["""  have hpc : stairPC.getD %d 0 = %d := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ %d %d %d ?_ ?_ ?_ ?_ ?_ ?_""" % (i, j, i, j, k),
            "  · " + up_proof(i, j, k, srcs[0]),
            "  · " + up_proof(i + 1, j, k + 1, srcs[1]),
            "  · " + up_proof(i, j + 1, k, srcs[2]),
            "  · " + up_proof(i + 1, j + 1, k, srcs[3]),
            "  · " + cert_use(cb),
            "  · " + (cert_use(cc) if cc else "exact Nat.zero_le _")]
    out.append("\ntheorem n2cPiv%d : IsPiv stairCornerQ %d (stairPC.getD %d 0) := by\n%s"
               % (i, i, i, "\n".join(body)))

if PROBE:
    txt = "\n".join(out) + "\n"
    open('n2c_probe1.lean', 'w').write(txt)
    print('PROBE wrote n2c_probe1.lean')
    raise SystemExit(0)

out.append("""
/-- Row-level form of N2c. -/
theorem stairPivAt (i : Fin 45) : IsPiv stairCornerQ i.val (stairPC.getD i.val 0) := by
  fin_cases i
%s

/-! **N2c** — every position of the extracted corner runs is an `IsPiv` of the witness
corner (check_stair item 3, kernel-checked: the pivots are the extracted `pc`). -/
theorem stairCorner_pivots_witness :
    ∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2 := by
  intro x hx
  rw [stairCornerRuns45_pairs] at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact stairPivAt ⟨i, List.mem_range.mp hi⟩""" % "\n".join(
    "  · exact n2cPiv%d" % i for i in range(n)))

txt = "\n".join(out) + "\n"
open('n2c_block.lean' if not PROBE else 'n2c_probe1.lean', 'w').write(txt)
print('wrote n2c_block.lean: %d lines, %d certs' % (txt.count('\n'), len(certs)))
