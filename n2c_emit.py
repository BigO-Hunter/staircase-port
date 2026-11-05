"""N2c emitter: builds the complete Lean text for N2c (data + proofs) and writes
n2c_block.lean (to be spliced into StaircasePort/Pivot.lean, replacing the N2c sorry).

Everything numeric is verified here first (mirroring the Lean semantics):
  * the concrete 45x45 corner Q (corZStair stairMZ)
  * pc, the four-block targets per IsPiv position
  * every upper-bound source (trivial min(#rows,#cols) or a stairNEBlocks cut)
  * every minor certificate: det != 0 mod stairCertP and its modular inverse
  * the cover: every position's B-block (size k+1) and C-block (size k) has a minor
"""
import json, random, re

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
def rho(X, Y): return sum(1 for r in range(X) if pc[r] >= Y)

def det_inv_mod(S, p=P):
    nn = len(S)
    M = [[S[i][j] % p for j in range(nn)] + [1 if i == j else 0 for j in range(nn)] for i in range(nn)]
    det = 1
    for c in range(nn):
        piv = None
        for r in range(c, nn):
            if M[r][c] % p: piv = r; break
        if piv is None: return 0, None
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = -det
        det = det * M[c][c] % p
        inv = pow(M[c][c], p - 2, p)
        M[c] = [(v * inv) % p for v in M[c]]
        for r in range(nn):
            if r != c and M[r][c] % p:
                f = M[r][c]
                M[r] = [(M[r][k] - f * M[c][k]) % p for k in range(2 * nn)]
    return det % p, [row[nn:] for row in M]

# ---------- certificate pool ----------
certs = []          # list of dicts: R, Cc (sorted lists), S (entries), T (cols = transpose of inverse)
bykey = {}
def add_cert(R, Cc):
    R = sorted(R); Cc = sorted(Cc)
    key = (tuple(R), tuple(Cc))
    if key in bykey: return bykey[key]
    S = [[Q[r][c] % P for c in Cc] for r in R]
    det, inv = det_inv_mod(S)
    if det == 0: return None
    cols = [[inv[l][j] for l in range(len(Cc))] for j in range(len(Cc))]
    assert all(sum(S[i][l] * cols[j][l] for l in range(len(Cc))) % P == (1 if i == j else 0)
               for i in range(len(R)) for j in range(len(Cc)))
    c = {'R': R, 'C': Cc, 'S': S, 'T': cols, 'det': det}
    certs.append(c); bykey[key] = c
    return c

def covers(c, X, Y, t):
    return len(c['R']) == t and max(c['R']) < X and min(c['C']) >= Y

needB = [(i + 1, pc[i], rho(i, pc[i]) + 1) for i in range(n)]
needC = [(i, pc[i] + 1, rho(i, pc[i])) for i in range(n) if rho(i, pc[i]) > 0]

# forced structural certs (square = whole block, contiguous)
add_cert([0], [44])
add_cert(range(22), range(23, 45))
add_cert(range(23), range(22, 45))
add_cert(range(24), range(21, 45))
add_cert(range(25), range(20, 45))
add_cert(range(43), range(2, 45))
add_cert(range(44), range(1, 45))

def covered_now():
    s = set()
    for c in certs:
        for kind, need in (('B', needB), ('C', needC)):
            for bb in need:
                if covers(c, *bb): s.add((kind,) + bb)
    return s

random.seed(17)
# ---- greedy: random shapes with wide coverage, per target size ----
def greedy(t, gen_shapes, tries):
    picked = []
    for _ in range(tries):
        cov = covered_now()
        rem = [(k, bb) for k, need in (('B', needB), ('C', needC)) for bb in need
               if bb[2] == t and (k,) + bb not in cov]
        if not rem: break
        best = None
        for (R, Cc) in gen_shapes():
            cand = [x for x in rem if len(R) == x[1][2] and max(R) < x[1][0] and min(Cc) >= x[1][1]]
            if not cand: continue
            if best is not None and len(cand) <= len(best[1]): continue
            try:
                det, _ = det_inv_mod([[Q[r][c] % P for c in Cc] for r in R])
            except Exception:
                continue
            if det == 0: continue
            best = ((R, Cc), cand)
        if best is None:
            print('  !! t=%d no shape covers %s' % (t, rem[:3])); break
        c = add_cert(best[0][0], best[0][1])
        picked.append(c)
    return picked

def gen2():
    for _ in range(400):
        r = random.randint(1, 20)
        m = random.randint(r, 21)
        R = sorted(random.sample(range(m + 1), 2))
        if max(R) != m: continue
        c1 = random.randint(22 + m, 43)
        if c1 >= 45: continue
        Cc = sorted(random.sample(range(c1, 45), 2))
        if min(Cc) != c1: continue
        yield (R, Cc)
    for r1 in range(0, 21):
        for c1 in range(23, 44):
            yield ([r1, r1 + 1], [c1, c1 + 1])

def gen26():
    for _ in range(600):
        m = random.randint(25, 42)                       # max row
        R = sorted(set(random.sample(range(m + 1), 26)) | {m})
        if len(R) != 26: continue
        c = random.randint(max(2, 19 - (42 - m)), 19)    # min col
        Cc = sorted(set(random.sample(range(c, 45), 26)))
        if len(Cc) != 26 or min(Cc) != c: continue
        yield (R, Cc)
    for m in range(25, 43):
        for c in range(2, 20):
            R = list(range(m - 25, m + 1))
            Cc = list(range(c, c + 26))
            if Cc[-1] < 45:
                yield (R, Cc)

for t, gen, tries in ((2, gen2, 200), (26, gen26, 200)):
    picked = greedy(t, gen, tries)
    print('family t=%d: %d certs' % (t, len(picked)))

allcov = covered_now() | {('B', 45, 0, 45)}
missing = [('B',) + bb for bb in needB if ('B',) + bb not in allcov] + \
          [('C',) + bb for bb in needC if ('C',) + bb not in allcov]
print('certs:', len(certs), 'missing:', missing)
assert not missing, missing

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
        if t == min(X, n - Y):
            upper[(X, Y, t)] = ('height' if X <= n - Y else 'width', t)
        else:
            e = blk[(X - 1, Y)]
            assert e[1] <= t
            upper[(X, Y, t)] = ('table', e[0], e[1])

# ================= Lean emission =================
def natlist(l): return '[' + ', '.join(str(v) for v in l) + ']'
def nrows(S): return '[' + ',\n   '.join(natlist(r) for r in S) + ']'

out = []
out.append("""/-! ### N2c — the rightmost-pivot lower bound at the extracted witness (check_stair item 3)

The extracted pivot pattern pc (staircase_data.json `pc`) is a permutation of `0..44`; the
corner runs decode to the graph of pc (`stairCornerRuns45_pairs`, a kernel `decide`). For
each row `i` the four NE blocks around `(i, pc i)` satisfy:

  A = rk q i (pc i) = k,      B = rk q (i+1) (pc i) = k+1,
  C = rk q i (pc i+1) = k,    D = rk q (i+1) (pc i+1) = k,     k = #{r < i | pc r ≥ pc i},

which is exactly `IsPiv q i (pc i)` by `isPiv_of_bounds`. The upper bounds are the trivial
`min(#rows,#cols)` ones or N2b's cut table (`rkQ_le_of_block`); the lower bounds are
explicit nonzero minors, certified by a modular inverse mod `stairCertP` (the N3 `certChk`
mechanism) — `n2c_rank_lower`.
-/

/-- The extracted rightmost-pivot pattern: row `i`'s rightmost pivot is column `pc i`. -/
def stairPC : List ℕ := %s

/-- The corner runs are exactly the graph of `stairPC` (kernel `decide` on the extracted
run list). -/
theorem stairCornerRuns45_pairs :
    runPairs stairCornerRuns45 = (List.range 45).map (fun i => (i, stairPC.getD i 0)) := by
  decide""" % natlist(pc))

# ---- generic lemmas ----
out.append("""
/-! #### generic rank lemmas (Mathlib d13f23b7 supplies `rank_submatrix_le`,
`rank_of_det_ne_zero`, `rank_le_card_height/width`; the bridges below are local) -/

/-- NE-block rank is monotone in the row cut. -/
lemma rk_rows_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X X' Y : ℕ} (h : X ≤ X') : rk q X Y ≤ rk q X' Y := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X'} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} => (⟨r.1, by have := r.2; omega⟩ : {r : Fin a // r.val < X'}))
        (fun c => c) := by
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
        (fun c : {c : Fin b // Y' ≤ c.val} => c.1)).submatrix
        (fun r => r)
        (fun c : {c : Fin b // Y ≤ c.val} => (⟨c.1, by have := c.2; omega⟩ : {c : Fin b // Y' ≤ c.val})) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- Trivial height bound: an `X`-row block has rank at most `X`. -/
lemma rk_le_height {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K) (X Y : ℕ) :
    rk q X Y ≤ X := by
  rw [rk]
  refine (Matrix.rank_le_card_height _).trans ?_
  exact Fintype.card_le_of_embedding
    ⟨fun r : {r : Fin a // r.val < X} => (⟨r.1.val, r.2⟩ : Fin X), fun u v huv => by
      simp only [Fin.mk.injEq, Subtype.mk.injEq] at huv
      exact Subtype.ext (Fin.ext huv)⟩

/-- Trivial width bound: the block's columns `≥ Y` are at most `b - Y`. -/
lemma rk_le_width {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K) (X Y : ℕ)
    (hY : Y ≤ b) : rk q X Y ≤ b - Y := by
  rw [rk]
  refine (Matrix.rank_le_card_width _).trans ?_
  exact Fintype.card_le_of_embedding
    ⟨fun c : {c : Fin b // Y ≤ c.val} => (⟨c.1.val - Y, by have := c.2; have := c.1.isLt; omega⟩ : Fin (b - Y)),
      fun u v huv => by
      simp only [Fin.mk.injEq] at huv
      have h1 := u.2; have h2 := v.2
      exact Subtype.ext (Fin.ext (by omega))⟩

/-- A nonzero `n × n` minor forces `n ≤` the NE-block rank. -/
lemma rk_ge_of_det {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K) (X Y : ℕ)
    {n : ℕ} (R : Fin n → {r : Fin a // r.val < X}) (C : Fin n → {c : Fin b // Y ≤ c.val})
    (hdet : (Matrix.of fun i j => q (R i).1 (C j).1).det ≠ 0) : n ≤ rk q X Y := by
  have h1 : (Matrix.of fun i j => q (R i).1 (C j).1).rank = n := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
  have h2 : ((q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
      (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix R C).rank =
      (Matrix.of fun i j => q (R i).1 (C j).1).rank := rfl
  rw [← h1, ← h2, rk]
  exact Matrix.rank_submatrix_le _ _ _

/-- IsPiv from four exact rank values. -/
lemma isPiv_of_exact (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j = k) (hB : rk q (i+1) j = k+1)
    (hC : rk q i (j+1) = k) (hD : rk q (i+1) (j+1) = k) : IsPiv q i j := by
  unfold IsPiv
  rw [hA, hB, hC, hD]
  omega

/-- IsPiv from two-sided bounds: uppers on the four blocks + lower bounds on the `(i+1,j)`
block (size `k+1`) and the `(i,j+1)` block (size `k`). -/
lemma isPiv_of_bounds (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j ≤ k) (hB : rk q (i+1) j ≤ k+1)
    (hC : rk q i (j+1) ≤ k) (hD : rk q (i+1) (j+1) ≤ k)
    (hBlo : k+1 ≤ rk q (i+1) j) (hClo : k ≤ rk q i (j+1)) : IsPiv q i j := by
  have hAe : rk q i j = k := le_antisymm hA (hClo.trans (rk_cols_mono q (by omega)))
  have hCe : rk q i (j+1) = k := le_antisymm hC hClo
  have hDe : rk q (i+1) (j+1) = k := le_antisymm hD (hClo.trans (rk_rows_mono q (by omega)))
  exact isPiv_of_exact q i j k hAe (le_antisymm hB hBlo) hCe hDe

/-- N2b's cut bound, restated for `stairCornerQ` at a table block `(X-1, Y)`. -/
lemma rkQ_le_of_block (X Y c r : ℕ) (h : (X - 1, Y, r, c) ∈ stairNEBlocks) :
    rk stairCornerQ X Y ≤ c := by
  have hb := stairNE_rk_le stairQX1 stairQY1 stairQX2 stairQY2 (X - 1, Y, r, c) h
  simpa [stairCornerQ, stairMQ, stairPairM] using hb""")

# ---- the minor lemma ----
out.append("""
/-- **The modular minor certificate, consumed as a rank lower bound.** `rl`/`cl` are the
minor's row/column indices; `rows` is the minor mod `stairCertP` and `cols` the transpose of
its inverse mod `stairCertP` (the N3 `certChk` convention). `hent` pins `rows` against the
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
  -- the rational minor is the cast of the integer minor
  have hentQ : (Matrix.of fun i j : Fin n_ =>
        stairCornerQ (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
          (⟨cl.getD j.val 0, by have := hcl j; omega⟩ : Fin 45)) =
      Dz.map (Int.cast : ℤ → ℚ) := by
    ext i j
    rw [Matrix.map_apply, of_apply, of_apply, hDz, of_apply]
    exact corStairQ_cast stairMZ _ _
  have hdetZ : Dz.det ≠ 0 := by
    intro h0
    have e1 : (Dz.map (Int.cast : ℤ → ℚ)).det = ((Dz.det : ℤ) : ℚ) := by
      have := RingHom.map_det (Int.castRingHom ℚ) Dz
      rw [RingHom.mapMatrix_apply] at this
      exact this.symm
    have e2 := RingHom.map_det (Int.castRingHom (ZMod stairCertP)) Dz
    rw [RingHom.mapMatrix_apply, h0, map_zero] at e2
    have e3 : Dz.map (Int.castRingHom (ZMod stairCertP)) =
        Matrix.of fun i l : Fin n_ =>
          (((rows.getD i.val []).getD l.val 0 : ℕ) : ZMod stairCertP) := by
      ext i l
      rw [Matrix.map_apply, hDz, of_apply, of_apply]
      have hc := hent
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
      rw [← ZMod.intCast_mod, hc i.val i.isLt l.val l.isLt, Int.cast_natCast]
    rw [e3] at e2
    exact det_ne_zero_of_certChk rows cols hchk e2.symm
  rw [hentQ]
  refine rk_ge_of_det stairCornerQ X Y
    (fun i => ⟨⟨rl.getD i.val 0, by have := hrl i; omega⟩, hrl i⟩)
    (fun j => ⟨⟨cl.getD j.val 0, by have := hcl j; omega⟩, hcl j⟩) ?_
  simpa using (Int.cast_ne_zero (α := ℚ)).mpr hdetZ |> fun hh => hh""")

# ---- certificate data ----
for idx, c in enumerate(certs):
    out.append("""
/-- N2c minor cert %d: rows %s, cols %s (det %% P = %d). -/
def n2cR%d : List ℕ := %s
def n2cC%d : List ℕ := %s
def n2cS%d : List (List ℕ) := %s
def n2cT%d : List (List ℕ) := %s""" % (
        idx, (str(c['R'][0]) + '..' + str(c['R'][-1])) if len(c['R']) > 2 else str(c['R']),
        (str(c['C'][0]) + '..' + str(c['C'][-1])) if len(c['C']) > 2 else str(c['C']),
        c['det'], idx, natlist(c['R']), idx, natlist(c['C']), idx, nrows(c['S']), idx, nrows(c['T'])))

out.append("\nset_option maxRecDepth 20000 in")
for idx, c in enumerate(certs):
    nn = len(c['R'])
    out.append("""
theorem n2cChk%d : certChk n2cS%d n2cT%d %d stairCertP = true := by decide +kernel
theorem n2cEnt%d : ((List.range %d).all fun i => (List.range %d).all fun j =>
    decide (corZStair stairMZ (n2cR%d.getD i 0) (n2cC%d.getD j 0) %% (stairCertP : ℤ) =
      (((n2cS%d.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel""" % (
        idx, idx, idx, nn, idx, nn, nn, nn, idx, idx, idx))

# ---- per-position lemmas ----
pos = []
for i in range(n):
    j = pc[i]; k = rho(i, j)
    # upper bound sources
    srcs = []
    for (X, Y, t) in ((i, j, k), (i + 1, j, k + 1), (i, j + 1, k), (i + 1, j + 1, k)):
        srcs.append(upper[(X, Y, t)])
    # B cert (size k+1) and C cert (size k)
    cb = next(c for c in certs if covers(c, i + 1, j, k + 1))
    cc = next((c for c in certs if k and covers(c, i, j + 1, k)), None)
    pos.append({'i': i, 'j': j, 'k': k, 'srcs': srcs, 'B': cb, 'C': cc})

def up_proof(X, Y, t, src):
    if src[0] == 'height':
        return "exact rk_le_height stairCornerQ %d %d" % (X, Y)
    if src[0] == 'width':
        return "refine rk_le_width stairCornerQ %d %d (by decide)" % (X, Y)
    return "exact rkQ_le_of_block %d %d %d %d (by decide)" % (X, Y, t, src[1]) if src[1] != t \
        else "exact rkQ_le_of_block %d %d %d %d (by decide)" % (X, Y, t, src[1])

def cert_use(c, X, Y):
    idx = certs.index(c)
    return ("refine n2c_rank_lower (by decide) n2cR%d n2cC%d (by decide) (by decide) "
            "n2cS%d n2cT%d n2cChk%d n2cEnt%d" % (idx, idx, idx, idx, idx, idx))

for p in pos:
    i, j, k = p['i'], p['j'], p['k']
    if k == 0:
        body = ["""  have hpc : stairPC.getD %d 0 = %d := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ %d %d 0 ?_ ?_ ?_ ?_ ?_ ?_""" % (i, j, i, j),
                "  · " + up_proof(i, j, 0, p['srcs'][0]),
                "  · " + up_proof(i + 1, j, 1, p['srcs'][1]),
                "  · " + up_proof(i, j + 1, 0, p['srcs'][2]),
                "  · " + up_proof(i + 1, j + 1, 0, p['srcs'][3]),
                "  · " + cert_use(p['B'], i + 1, j),
                "  · exact Nat.zero_le _"]
        # note: the B cert is size 1 here -> k+1=1
    else:
        body = ["""  have hpc : stairPC.getD %d 0 = %d := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ %d %d %d ?_ ?_ ?_ ?_ ?_ ?_""" % (i, j, i, j, k),
                "  · " + up_proof(i, j, k, p['srcs'][0]),
                "  · " + up_proof(i + 1, j, k + 1, p['srcs'][1]),
                "  · " + up_proof(i, j + 1, k, p['srcs'][2]),
                "  · " + up_proof(i + 1, j + 1, k, p['srcs'][3]),
                "  · " + cert_use(p['B'], i + 1, j),
                "  · " + cert_use(p['C'], i, j + 1)]
    out.append("\ntheorem n2cPiv%d : IsPiv stairCornerQ %d (stairPC.getD %d 0) := by\n%s"
               % (i, i, i, "\n".join(body)))

out.append("\n/-- **N2c** — every position of the extracted corner runs is an `IsPiv` of the "
           "witness corner. -/\ntheorem stairCorner_pivots_witness :\n"
           "    ∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2 := by\n"
           "  intro x hx\n  rw [stairCornerRuns45_pairs] at hx\n"
           "  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx\n"
           "  exact Fin.cases " + " ".join("") + " (by\n"
           "    intro i\n    fin_cases i\n" +
           "\n".join("    · exact n2cPiv%d" % i for i in range(n)) + ") ⟨i, List.mem_range.mp hi⟩")

txt = "\n".join(out) + "\n"
open('n2c_block.lean', 'w').write(txt)
print('\nwrote n2c_block.lean (%d lines, %d certs)' % (txt.count('\n'), len(certs)))
print('total certChk mults:', sum(len(c['R']) ** 3 for c in certs))
print('total entry checks:', sum(len(c['R']) ** 2 for c in certs))
