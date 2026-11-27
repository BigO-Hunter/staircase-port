# Staircase recovery lanes

These branches preserve proof and recovery work that was not integrated into main. They
are source branches, not new repositories and not claims that every lane is complete.
Each branch tip carries a cleanup commit removing internal host logistics; the original
history is preserved underneath. The SHAs below name the preserved source points.

- `recovery/stage2` at `c70fc9175f6e0e4c780da5e11d8335476369f356`: the 37-commit integrated stage-two local main (FormalCalc/DenseProg/LabGen/PackCore proved; Rec derivation blocked).
- `recovery/sp-compose` at `23b29e7b1929447c0164f58dc28698040db3b340`: composition surgery complete; integration gate unfinished.
- `recovery/sp-corner` at `8d13ebf7c43790500afd3dbd1e81a1890b0ac572`: corner n7_rk_qm route rewrite recovery.
- `recovery/sp-d2` at `265d2c4a0277f04de1069e93402bbe8454af55bc`: D2 resume and scaffold continuation.
- `recovery/sp-midrun` at `042437bb1acab9636afa819da7f94a706816bcf2`: middle-run producer conventions and isPiv work.
- `recovery/sp-n2b-r2` at `98506ed2655afa7596fd8a5f2686e2a8eeb5f111`: N2b build evidence (8997 jobs) and probes.
- `recovery/sp-n2c` at `f64e2ae2338839e5457005f38b46b98e64cc3c94`: N2c final verification, 8997 jobs and zero errors.
- `recovery/sp-n2d` at `3df626eca4b6809d69536d5c3ea72f41f93d967e`: N2d stopping point and refuted-goal analysis.
- `recovery/sp-n52` at `fbd1b3ecce9f4efcadf0fd9c08a2368af20d0e21`: N5-2 `flagBasis_stair` proof and axiom audit.
- `recovery/sp-n6` at `15c0d3c399a4a1aa647b6fe9f1c95d8ec81d45cb`: N6 shifted-block corner-obstacle removal.
- `recovery/sp-n7` at `c28b8ae5ad7aef7df104535b4a0e99b0c10efed7`: N7 rewire, byte-identical `flagBasis_stair`, and corner-hole contract type.

The `archive/home-*` branches mirror these tips (same commits, kept as received).
Each branch keeps its original commit history. Do not fast-forward main from these
branches without a fresh proof-tree merge and build.
