import json
import n6_midrun as nm

M, q, order, dv = nm.build()
cache = {}


def R(X, Y):
    if (X, Y) not in cache:
        cache[(X, Y)] = nm.rank_mod(q[:X, Y:])
    return cache[(X, Y)]


def piv(i, j):
    a = R(i + 1, j + 1)
    b = R(i, j)
    c = R(i + 1, j)
    d = R(i, j + 1)
    return (a + b == c + d + 1), (a, b, c, d)


for (i, j) in [(1, 507), (2, 508), (25, 486), (45, 45), (100, 100)]:
    print(i, j, piv(i, j))
