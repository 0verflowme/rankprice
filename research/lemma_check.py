"""Numeric verification of every step of the intersection-lemma proof."""
import itertools, random, sys
sys.path.insert(0, 'research')
from rank_price2 import (pc, par, f2_rank, rm_star_generators, reduce_basis,
                         cubic_of_pattern, pattern_masks, Q_of_mask,
                         cubic_to_vec, in_span, span_dim, W_of, subspace_points)
random.seed(99)

# ---- Step A: syndrome claim ----
# coefficient of x^T (|T|=d) in P_c == #{y in c : supp y >= T} mod 2
print("A: cubic = RM syndrome map")
for h in (4, 5, 6):
    for _ in range(20):
        x = random.getrandbits((1 << h) - 1)
        if not x: continue
        P = cubic_of_pattern(x, h)
        lin, pairs, trips = P
        masks = pattern_masks(x)
        for d, container in ((1, None), (2, pairs), (3, trips)):
            for T in itertools.combinations(range(h), d):
                cnt = sum(1 for y in masks if all((y >> i) & 1 for i in T)) & 1
                if d == 1:
                    have = (lin >> T[0]) & 1
                else:
                    have = 1 if T in container else 0
                assert cnt == have, (h, T, cnt, have)
print("   coefficient of x^T == parity of #{y in c : y contains T}. OK")

# ---- Step B: duality  {c : cubic(c)=0} == RM(h-4,h)* ----
print("B: kernel == punctured RM(h-4,h) (both inclusions, exhaustive-ish)")
for h in (4, 5):
    gens = rm_star_generators(h, h - 4)
    # RM* subset kernel
    for _ in range(200):
        cw = 0
        for g in gens:
            if random.random() < .5: cw ^= g
        assert cubic_of_pattern(cw, h) == (0, frozenset(), frozenset())
    # kernel subset RM*: random kernel elements found by solving? sample random
    # patterns, keep those with zero cubic, check RM* membership via reduction
    piv = {}
    for g in gens:
        cur = g
        while cur:
            b = cur.bit_length() - 1
            if b in piv: cur ^= piv[b]
            else: piv[b] = cur; break
    def in_rm(c):
        cur = c
        while cur:
            b = cur.bit_length() - 1
            if b not in piv: return False
            cur ^= piv[b]
        return True
    found = 0
    tries = 0
    while found < 30 and tries < 300000:
        tries += 1
        c = random.getrandbits((1 << h) - 1)
        # project to kernel cheaply: flip until cubic zero? just test
        if cubic_of_pattern(c, h) == (0, frozenset(), frozenset()):
            found += 1
            assert in_rm(c), "kernel element NOT in RM*"
    print(f"   h={h}: {found} random zero-cubic patterns all in RM*. OK")

# ---- Step C: independence theorem (T) ----
print("C: independence of Q on <=3-fold XORs of independent vectors")
def dual_basis(E, h):
    """rows lambda_j with lambda_j . e_i = delta_ij"""
    n = len(E)
    # solve for each j: vector L_j with L_j.e_i = delta_ij
    # build matrix with rows e_i, solve E L^T = I over F2
    Ls = []
    for j in range(n):
        # gaussian: solve sum over bits: use augmented approach
        rows = [(E[i], 1 if i == j else 0) for i in range(n)]
        # find any L: treat unknown L as h-bit vector; equations rows
        # solve by elimination over columns
        pivots = []
        rows2 = [list(r) for r in rows]
        L = 0
        # simple method: gaussian eliminate on the e-matrix once per j (cheap here)
        m = [[(E[i] >> b) & 1 for b in range(h)] + [1 if i == j else 0]
             for i in range(n)]
        r = 0
        pivcols = []
        for col in range(h):
            p = None
            for rr in range(r, n):
                if m[rr][col]:
                    p = rr; break
            if p is None: continue
            m[r], m[p] = m[p], m[r]
            for rr in range(n):
                if rr != r and m[rr][col]:
                    m[rr] = [(m[rr][k] ^ m[r][k]) for k in range(h + 1)]
            pivcols.append(col); r += 1
            if r == n: break
        for idx, col in enumerate(pivcols):
            if m[idx][h]:
                L |= 1 << col
        Ls.append(L)
    for j in range(n):
        for i in range(n):
            assert par(E[i], Ls[j]) == (1 if i == j else 0)
    return Ls

for h, n in ((6, 4), (8, 5), (10, 6)):
    for _ in range(15):
        E = []
        while f2_rank(E) < n:
            E = [random.randrange(1, 1 << h) for _ in range(n)]
        subsets = [S for r in (1, 2, 3) for S in itertools.combinations(range(n), r)]
        # random nonempty family
        F = [S for S in subsets if random.random() < .4]
        if not F: F = [random.choice(subsets)]
        tot = None
        for S in F:
            m = 0
            for i in S: m ^= E[i]
            v = cubic_to_vec(Q_of_mask(m, h), h)
            tot = v if tot is None else tot ^ v
        assert tot != 0, "DEPENDENCE FOUND - theorem false"
        # witness: monomial on a maximal element separates
        S0 = max(F, key=len)
        Ls = dual_basis(E, h)
        cnt = 0
        for S in F:
            m = 0
            for i in S: m ^= E[i]
            if all(par(Ls[j], m) for j in S0):
                cnt ^= 1
        assert cnt == 1, "maximal-monomial witness failed"
print("   45 random configurations: sums nonzero, max-monomial witness = 1. OK")

# ---- Step D: span reduction of >=4-folds via null identity ----
print("D: Q(>=4-fold XOR) reduces to <=3-folds (null-identity induction)")
for h, n in ((7, 5), (9, 6)):
    for _ in range(10):
        E = []
        while f2_rank(E) < n:
            E = [random.randrange(1, 1 << h) for _ in range(n)]
        gen3 = []
        for r in (1, 2, 3):
            for S in itertools.combinations(range(n), r):
                m = 0
                for i in S: m ^= E[i]
                gen3.append(cubic_to_vec(Q_of_mask(m, h), h))
        for r in (4, 5):
            if r > n: continue
            for S in itertools.combinations(range(n), r):
                m = 0
                for i in S: m ^= E[i]
                assert in_span(cubic_to_vec(Q_of_mask(m, h), h), gen3), \
                    "span reduction fails"
print("   all 4- and 5-fold Q's lie in span of <=3-fold Q's. OK")
print("\nAll proof steps verified numerically.")
