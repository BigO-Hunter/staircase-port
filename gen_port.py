#!/usr/bin/env python3
"""Generate the N5-2 port scaffold at clone root from the fetched `flag_gen` body.

Source: ref/nb_flag_gen_solution.lean:13-1064 (the flag_gen submission = all its inlined helper
sections + the main theorem). Target: n52_port.lean, specialized to h = 19 and wrapped in
StaircasePort.Stair.N52 so no name is re-declared at a platform path.

Adaptations, each documented at its site in the generated file:
  A. `variable {h : ℕ}` dropped, `h` -> `19` (the frame is concrete here; pDatStair/corStairR
     exist only at n = 23). Named-argument LABELS `(h := ...)` are preserved.
  B. `namespace IntMul.Kappa.R6.Bit.NB` lines dropped (replaced by StaircasePort.Stair.N52).
  C. Three platform children consumed by the body are stubbed (PLATFORM STUBS section).
  D. Corner factor `pDat` (r6/Defs4 `cor` frame) -> `pDatStair` (staircase frame `corStairQ`):
     the statement's `hcert`, the Pall product, and `pDat_ne` -> `pDatStair_ne`.
  E. Data-clause call: `data_edge` -> `data_edge_stair` fed by `isPiv_stair_lower` (N2d).
  F. Conclusion `DataE` -> `DataE'`.
"""
import re

SRC = "ref/nb_flag_gen_solution.lean"
lines = open(SRC).read().split("\n")
body = lines[12:1064]          # file lines 13..1064

LOCAL = """sum_sv_mul sum_mul_sv Nm_sq Tm_Ti Ti_Tm Tm_row Ti_col flagEquiv_top flagEquiv_bot
qM_mul qM_idem qM_trace qM_corner rank_eq_trace aux1_upper aux1_diag aux1_diag_last aux2_upper
aux2_diag aux2_diag_last kron_vec1 kron_vec2 qM_eq side_B side_A side1_B_upper side1_B_diag
side1_A_upper side1_A_diag side2_B_upper side2_B_diag side2_A_upper side2_A_diag vmv_idem
one_sub_vmv_idem trace_one_sub_vmv aux1_edge aux2_edge rank_kron_vmv side1_edge side2_edge
idem_similar_trace eIdem_mul eIdem_trace eIdem_corner eIdem_corner_det Uf_pt Vf_pt map_XU
map_XV map_cm eval_det map_sconj adj_eq sconj_eq det_sub_smul exists_eval_ne conj_wit eval_pA_U
eval_pA_V eval_pCor_U eval_pCor_V eval_pT eval_detU eval_detV wP_dot wP_idem wP_trace wP_apply
lab_trace pA_U_ne pA_V_ne detU_ne detV_ne pT_ne pCor_U_ne pCor_V_ne map_kM eval_pDat_of
pDat_ne conj_vmv conj_one conj_one' conj_dot conj_sub_vmv conj_idem conj_rank lab_of_sconj
Te_Te' Te'_Te Sb_conj Sb_inv lst_eq corner_of_pCor flag_gen_stair_aux""".split()

out = []
for ln in body:
    if ln.strip() == "variable {h : ℕ}":
        continue
    if ln.strip() == "namespace IntMul.Kappa.R6.Bit.NB" or ln.strip() == "end IntMul.Kappa.R6.Bit.NB":
        continue
    # A: protect named-argument labels before replacing the word `h`
    ln = ln.replace("(h := ", "(\x00HARG\x00 := ").replace("{h := ", "{\x00HARG\x00 := ")
    ln = re.sub(r"\bh\b", "19", ln)
    ln = ln.replace("\x00HARG\x00", "h")
    # A': named args to LOCAL lemmas/defs that no longer take `h`
    for nm in LOCAL:
        ln = ln.replace(f"{nm} (h := 19)", nm)
    out.append(ln)
txt = "\n".join(out)

txt = txt.replace("intro 19; exact e (Fin.ext (by omega))", "intro hh; exact e (Fin.ext (by omega))")

# A'': the two side*-A_upper proofs leave literal `if True`/`if False` residues once h is
# concrete; the generic body's simp set then lacks the `ite`/`dite` reduction lemmas.
import re as _re
_pat = _re.compile(r"    simp \(disch := omega\) only \[Rterms, (Ry2?), of_apply, dif_pos, "
                   r"dif_neg, if_pos, if_neg,\n      Fin\.ext_iff, List\.map_cons, "
                   r"List\.map_nil, List\.sum_cons, List\.sum_nil, zero_mul, add_zero\]")
def _grow(m):
    return ("    simp (disch := omega) only [Rterms, " + m.group(1) + ", of_apply, dif_pos, "
            "dif_neg, if_pos, if_neg,\n      Fin.ext_iff, List.map_cons, List.map_nil, "
            "List.sum_cons, List.sum_nil, zero_mul, add_zero,\n"
            "      ite_true, ite_false, dite_true, dite_false, \u2193reduceIte, \u2193reduceDIte]")
txt, _n = _pat.subn(_grow, txt)
assert _n == 2, _n

txt = txt.replace("flag_gen_sol_aux", "flag_gen_stair_aux")

PLATFORM = open("n52_platform_stubs.lean").read()
STAIRFACTOR = open("n52_stairfactor.lean").read()


def sub1(text, old, new, tag):
    n = text.count(old)
    assert n == 1, f"{tag}: expected 1 occurrence, found {n}"
    return text.replace(old, new)


# D1: the statement's hcert moves to the staircase frame
txt = sub1(txt,
           "      cor ((1 - vecMulVec w₁ v₁) ⊗ₖ (1 - vecMulVec w₂ v₂)) i.val j.val).det ≠ 0)",
           "      corStairQ ((1 - vecMulVec w₁ v₁) ⊗ₖ (1 - vecMulVec w₂ v₂)) i.val j.val).det ≠ 0)",
           "hcert")

# D2: replace the r6 pDat lemma block (map_kM stays: it is frame-free) with the stair factor
start = txt.index("lemma eval_pDat_of")
end = txt.index("end Data", start)
txt = txt[:start] + STAIRFACTOR + "\n" + txt[end:]

# D3: Pall product + its nonvanishing use pDatStair
txt = sub1(txt, "(∏ q ∈ Lab ×ˢ Lab, (pDat (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2) *",
           "(∏ q ∈ Lab ×ˢ Lab, (pDatStair (vecMulVec q.1.1 q.1.2) (vecMulVec q.2.1 q.2.2) *",
           "pall")
txt = sub1(txt, "      · exact pDat_ne _ _ _ _", "      · exact pDatStair_ne _ _ _ _", "pdat_ne")

# E: the data clause
OLD_CALL = """    refine data_edge _ _ _ _ (conj_dot U hdU _ _ (hLab _ hp₁)) (conj_dot V hdV _ _ (hLab _ hp₂))
      (mul_ne_zero (hx1 _) (hx2 _)) (mul_ne_zero hy1 hy2) ?_ ?_"""
NEW_CALL = """    -- N5-2 swap (fetched :1049): platform `data_edge` (r6 frame) -> `data_edge_stair`
    -- (N5-1, Signature.lean:197) whose pivot hypothesis is N2d `isPiv_stair_lower`
    -- (Pivot.lean:310). It needs the STAIRCASE-frame corner det, supplied below.
    have h₁' : (U⁻¹ *ᵥ p₁.2) ⬝ᵥ (Uᵀ *ᵥ p₁.1) = 1 := conj_dot U hdU _ _ (hLab _ hp₁)
    have h₂' : (V⁻¹ *ᵥ p₂.2) ⬝ᵥ (Vᵀ *ᵥ p₂.1) = 1 := conj_dot V hdV _ _ (hLab _ hp₂)
    refine data_edge_stair _ _ _ _ h₁' h₂'
      (isPiv_stair_lower _ _ _ _ h₁' h₂' (mul_ne_zero (hx1 _) (hx2 _)) (mul_ne_zero hy1 hy2) ?_ ?_)"""
txt = sub1(txt, OLD_CALL, NEW_CALL, "data_call")

# the hdet block: stair-frame eval identity
txt = sub1(txt, """      rw [eval_pDat_of f _ _ _ _ (sconj_eq U _ hdU) (sconj_eq V _ hdV), ← hUdef, ← hVdef,
        conj_vmv, conj_vmv] at t""",
           """      rw [eval_pDatStair_of f _ _ _ _ (sconj_eq U _ hdU) (sconj_eq V _ hdV), ← hUdef,
        ← hVdef, conj_vmv, conj_vmv] at t""",
           "hdet_rw")

# F: conclusion
txt = sub1(txt, "        DataE (h := 19) (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv)) :=",
           "        DataE' (h := 19) (S * ((1 - vecMulVec p₁.1 p₁.2) ⊗ₖ (1 - vecMulVec p₂.1 p₂.2)) * Sinv)) :=",
           "dataclause")

HEADER = '''/-
N5-2: port of `flag_gen` (ref/nb_flag_gen_solution.lean, generated from the ACCEPTED
submission 3a50ac98 of IntMul.Kappa.R6.Bit.NB.flag_gen), specialized to h = 19 and re-aimed at
the STAIRCASE corner.  Generated by gen_port.py — edit that, not this file.

Adaptations vs the fetched body (each is marked inline):
  A. `variable {h : ℕ}` dropped, `h` -> `19` (the staircase frame `corStairR`/`pDatStair` is
     concrete at n = 23); named-argument labels `(h := ...)` are preserved.
  B. `namespace IntMul.Kappa.R6.Bit.NB` dropped — the body lives in `StaircasePort.Stair.N52`.
  C. PLATFORM STUBS: `aux_edge_of`, `side_edge_of`, `idem_similar` (generic Proved children).
  D. Corner factor `pDat` (Defs4:1497, r6/Defs4 `cor` frame) -> `pDatStair` (staircase frame),
     including the theorem's `hcert` and `pDatStair_ne` for the Pall product.
  E. Data-clause call `data_edge` (fetched :1049) -> `data_edge_stair` (N5-1) fed by
     `isPiv_stair_lower` (N2d, Pivot.lean:310).
  F. Conclusion `DataE` -> `DataE'` (Data.lean:63).
-/
import StaircasePort.Signature
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace StaircasePort.Stair.N52

open Matrix Finset MvPolynomial
open StaircasePort.Stair
open IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

'''

open("n52_port.lean", "w").write(HEADER + PLATFORM + txt + "\n\nend\n\nend StaircasePort.Stair.N52\n")
print("wrote n52_port.lean,", len(txt.split(chr(10))), "body lines")
