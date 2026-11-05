

# --- shifted-block probe: is there a rank-one-above-diagonal block that puts the corner
# position (25,2) at a diagonal index l >= 1 (needed because isPiv_rank1_lower demands 1 <= l)?
def probe_shifted(C, r0, off, K=18, G=19):
    n_bad = 0
    for k1 in range(K):
        for k2 in range(k1 + 1, K):
            for g1 in range(G):
                for g2 in range(g1 + 1, G):
                    if not (k2 < g1):
                        continue
                    if off + g2 >= 45 or r0 + k2 >= 45:
                        continue
                    d = (C[r0 + k1][off + g1] * C[r0 + k2][off + g2]
                         - C[r0 + k1][off + g2] * C[r0 + k2][off + g1])
                    if d != 0:
                        n_bad += 1
    return n_bad


print('shifted-block probes (rank-one needs k < g in block coords)')
for nm, C in (('r6-ctrl', Cr6), ('stair', Cs)):
    for r0, off, note in ((24, 1, '(24+k,1+g): k=1 -> (25,2)'), (25, 2, '(25+k,2+g): k=0'),
                          (23, 0, '(23+k,0+g)')):
        print(f'  [{nm}] {note}: {probe_shifted(C, r0, off)} nonzero minors')
