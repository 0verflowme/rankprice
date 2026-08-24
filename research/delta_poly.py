"""Polynomial-time delta*: delta* = rank of the collapse-flattening M_P.

M_P rows i in [h]; columns q in {1} u {x_j} u {x_j x_k (j<k)};
entry = coefficient in P of the multilinear reduction ml(x_i * q):
  q=1       -> P_lin[i]
  q=x_j     -> P_lin[i] if j==i else P_pair[{i,j}]
  q=x_j x_k -> P_pair[{i,k}] if i==j; P_pair[{i,j}] if i==k;
               else P_trip[{i,j,k}]
Theorem: V0^perp = left kernel of M_P, delta* = rank(M_P).
"""
import itertools, random, sys, time
sys.path.insert(0, 'research')
from rank_price2 import (pc, par, f2_rank, rm_star_generators, pattern_of,
                         pattern_masks, cubic_of_pattern, coset_scan,
                         rank_of_support, delta_star_brute, tstar)
random.seed(4242)

def MP_rank(P, h, want_kernel=False):
    lin, pairs, trips = P
    pairs = set(pairs); trips = set(trips)
    def pcoef_pair(a, b):
        return 1 if tuple(sorted((a, b))) in pairs else 0
    def pcoef_trip(a, b, c):
        return 1 if tuple(sorted((a, b, c))) in trips else 0
    cols = [('one',)] + [('l', j) for j in range(h)] + \
           [('q', j, k) for j in range(h) for k in range(j + 1, h)]
    rows = []
    for i in range(h):
        bits = 0
        for ci, col in enumerate(cols):
            if col[0] == 'one':
                v = (lin >> i) & 1
            elif col[0] == 'l':
                j = col[1]
                v = (lin >> i) & 1 if j == i else pcoef_pair(i, j)
            else:
                j, k = col[1], col[2]
                if i == j:
                    v = pcoef_pair(i, k)
                elif i == k:
                    v = pcoef_pair(i, j)
                else:
                    v = pcoef_trip(i, j, k)
            if v:
                bits |= 1 << ci
        rows.append(bits)
    # rank + left kernel via row reduction with tags
    piv = {}
    ker = []
    for i, r in enumerate(rows):
        cur, tag = r, 1 << i
        while cur:
            b = cur.bit_length() - 1
            if b in piv:
                pr, pt = piv[b]
                cur ^= pr
                tag ^= pt
            else:
                piv[b] = (cur, tag)
                break
        if cur == 0:
            ker.append(tag)
    if want_kernel:
        return len(piv), ker
    return len(piv)

def cubic_of_masks(masks, h):
    """sparse cubic: skip the dense 2^h-bit pattern entirely"""
    import itertools as it
    lin = 0
    pairs = set()
    trips = set()
    for y in masks:
        bits = [i for i in range(h) if (y >> i) & 1]
        for i in bits:
            lin ^= 1 << i
        for ij in it.combinations(bits, 2):
            pairs ^= {ij}
        for t in it.combinations(bits, 3):
            trips ^= {t}
    return (lin, frozenset(pairs), frozenset(trips))

def delta_poly(rep_or_pattern, h):
    if isinstance(rep_or_pattern, int):
        return MP_rank(cubic_of_pattern(rep_or_pattern, h), h)
    masks = [S for S, a in rep_or_pattern.items() if a & 1]
    return MP_rank(cubic_of_masks(masks, h), h)

if __name__ == '__main__':
    t0 = time.time()
    print("== V1: vs brute delta* on random instances h=4,5 ==")
    ok = bad = 0
    for h in (4, 5):
        for _ in range(60):
            rep = {S: random.randrange(8) for S in range(1, 1 << h)
                   if random.random() < .5}
            if not any(a & 1 for a in rep.values()):
                continue
            dp = delta_poly(rep, h)
            db = delta_star_brute(rep, h)
            if dp == db:
                ok += 1
            else:
                bad += 1
                if bad <= 5:
                    print(f"   MISMATCH h={h}: poly {dp} brute {db} rep {rep}")
    print(f"   agree {ok}, mismatch {bad}")

    print("== V2: planted low-rank + RM* scramble, h=5 ==")
    gens5 = rm_star_generators(5, 1)
    ok = bad = 0
    for _ in range(20):
        V = []
        while f2_rank(V) < 3:
            V = [random.randrange(1, 32) for _ in range(3)]
        pts = set()
        for bits in range(1, 8):
            m = 0
            for i in range(3):
                if (bits >> i) & 1:
                    m ^= V[i]
            pts.add(m)
        x = 0
        for m in pts:
            if random.random() < .7:
                x ^= 1 << (m - 1)
        for g in gens5:
            if random.random() < .5:
                x ^= g
        if x == 0:
            continue
        dp = MP_rank(cubic_of_pattern(x, 5), 5)
        db = coset_scan(x, gens5, rank_of_support)
        if dp == db: ok += 1
        else:
            bad += 1
            print(f"   MISMATCH planted: poly {dp} brute {db}")
    print(f"   agree {ok}, mismatch {bad}")

    print("== V3: h=6 brute (4.2M cosets) x2 ==")
    gens6 = rm_star_generators(6, 2)
    for _ in range(2):
        rep = {S: random.choice((1, 3, 5, 7)) for S in range(1, 64)
               if random.random() < .6}
        dp = delta_poly(rep, 6)
        db = coset_scan(pattern_of(rep), gens6, rank_of_support)
        print(f"   poly {dp} brute {db} {'MATCH' if dp==db else 'MISMATCH'}")

    print("== V4: planted d inside big h (no brute; expect delta*=d) ==")
    for h, d in ((10, 4), (14, 6), (20, 8), (30, 10)):
        rows = []
        while f2_rank(rows) < d:
            rows = [random.randrange(1, 1 << h) for _ in range(d)]
        rep = {}
        for u in range(1, 1 << d):
            if random.random() < .8:
                m = 0
                for i in range(d):
                    if (u >> i) & 1:
                        m ^= rows[i]
                rep[m] = random.choice((1, 3, 5, 7))
        t1 = time.time()
        dp = delta_poly(rep, h)
        print(f"   h={h} planted d={d}: delta*_poly = {dp}  ({time.time()-t1:.2f}s)")

    print("== V5: scale test, h=64 ==")
    h, d = 64, 12
    rows = []
    while f2_rank(rows) < d:
        rows = [random.randrange(1, 1 << h) for _ in range(d)]
    rep = {}
    for _ in range(4000):
        u = random.randrange(1, 1 << d)
        m = 0
        for i in range(d):
            if (u >> i) & 1:
                m ^= rows[i]
        rep[m] = random.choice((1, 3, 5, 7))
    t1 = time.time()
    dp = delta_poly(rep, h)
    print(f"   h=64, 4000 gadgets, planted d=12: delta* = {dp} ({time.time()-t1:.2f}s)")
    print(f"\nall done {time.time()-t0:.1f}s")
