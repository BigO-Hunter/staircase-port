#!/usr/bin/env python3
"""Assemble Signature.lean deterministically from the pre-assembly backup.

  [A: header + N5-1 (DEPort, data_edge_stair)]
  [M: N5-2 machinery (corStairR ...) from the backup]
  [P: N52 port body (stubs + flag_gen body), from n52_port.lean]
  [F: flagBasis_stair — statement verbatim, proved by delegation]
  end StaircasePort.Stair
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent
if len(sys.argv) != 2:
    sys.exit("usage: assemble_sig.py <pre-assembly Signature backup.lean>\n"
             "Historical one-shot assembler; the assembled StaircasePort/Signature.lean\n"
             "is already committed. The backup input is not vendored.")
BK = sys.argv[1]
bk = open(BK).read()

FLAG_DOC = "/-- **N5-2** — `flagBasis_stair`"
MACH = "/-! ## N5-2 machinery: the staircase-frame corner factor"
END = "end StaircasePort.Stair"

a = bk.index(FLAG_DOC)
m = bk.index(MACH)
e = bk.rindex(END)
A = bk[:a].rstrip() + "\n"
M = bk[m:e].rstrip() + "\n"
F = bk[a:m].rstrip() + "\n"

# --- port body
port = open(ROOT / "n52_port.lean").read()
marker = "open scoped Kronecker\n"
port_body = port[port.index(marker) + len(marker):].strip("\n")
port_body = port_body.replace("namespace StaircasePort.Stair.N52", "namespace N52")
if not port_body.lstrip().startswith("namespace N52"):
    port_body = "namespace N52\n\n" + port_body.lstrip("\n")
port_body = port_body.replace("end StaircasePort.Stair.N52", "end N52")
assert port_body.rstrip().endswith("end N52"), port_body[-80:]
opts = ("set_option maxHeartbeats 1000000\nset_option autoImplicit false\n"
        "set_option relaxedAutoImplicit false\n\n")

# --- flagBasis proof
F2 = F.replace("""          Sinv)) := by
  sorry""",
              """          Sinv)) := by
  -- The r6 delegation (nb_flagBasis_solution.lean:198)
  --   `flag_gen (h := 19) qx1 qy1 qx2 qy2 qxy1 qxy2 data_cert Lab hLab Pis hPis`
  -- becomes the ported body with the staircase witness. The one hypothesis the port adds over
  -- the r6 body is `hcert`, supplied here by N3's kernel-checked `stair_data_cert`
  -- (Cert.lean:213) — the same role `data_cert` plays in the r6 body
  -- (nb_flagBasis_solution.lean:121-147).
  exact N52.flag_gen_stair_aux stairQX1 stairQY1 stairQX2 stairQY2 stairQxy1 stairQxy2
    stair_data_cert Lab hLab Pis hPis""")
assert "exact N52.flag_gen_stair_aux" in F2

open(ROOT / "StaircasePort/Signature.lean", "w").write(
    A + "\n" + M + "\n" + opts + port_body + "\n\n" + F2 + "\n" + END + "\n")
print("assembled:", len(open(ROOT / "StaircasePort/Signature.lean").read().split("\n")), "lines")
