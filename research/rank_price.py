#!/usr/bin/env python3
"""
v1 -- PARTIALLY SUPERSEDED by rank_price2.py.
Valid and kept: S1 (null identities), S2 (grading iso), S3 (relation code =
RM(h-4,h)* with constructive lifts), tstar (coset min-weight).
WRONG and disabled: the period-group characterization of delta* (S4/S6/S7).
Reason: for parity-phase functions EVERY XOR-shift derivative is Clifford
(f(z xor w) - f(z) has all-even coefficients), so the period kernel is
vacuous. delta* is really MIN-RANK DECODING of the RM* coset -- see v2.

Local research: the F2-rank price delta* for Clifford+T phase polynomials.

Objects.
  A "phase function" on h path variables is f(z) = sum_S a_S * par(S, z) mod 8,
  where S ranges over nonzero masks in [1, 2^h), par(S,z) = popcount(S & z) mod 2,
  and a_S in Z_8. Each odd-coefficient parity costs one T gate (weight = T-count).
  Clifford-free adjustments: adding any even-coefficient combination.

Grading (local derivation, validated in section S2/S3):
  f mod Clifford is captured exactly by a CUBIC polynomial P_f over F_2:
    lin coeff  = a-linear   mod 2
    pair grade = (pair coeff)/2 mod 2
    trip grade = (triple coeff)/4 mod 2
  and par(S, .) maps to e1(S) + e2(S) + e3(S) (elementary symmetric sums on S).

delta* (the rank price) := min over representations of rank_F2 {S : a_S odd}
  Claim (validated S4): delta* = h - dim K where K = period group of P_f,
    K = { w : P_f(x ^ w) = P_f(x) for all x },
  and K is computable in polynomial time by a 3-step linear-algebra filtration.

t* (the weight price / optimal T-count) := min over representations of #odd
  = min-weight of coset  odd(f) + RM(h-4,h)*   (Amy-Mosca Thm 1; inclusion
    RM* subset relations is re-proven locally in S3, equality by dim count).

Separation (S6): generic cubic on d variables has delta* = d, t* = Theta(d^2).
"""
import itertools, random, sys, time

def pc(x):
    return bin(x).count('1')

random.seed(20260823)

# ---------- S0 utilities ----------

def par(S, z):
    return pc(S & z) & 1

def feval(rep, z):
    """rep: dict mask->coeff (Z8). Value of f(z) mod 8."""
    return sum(a * par(S, z) for S, a in rep.items()) % 8

def ftable(rep, h):
    return tuple(feval(rep, z) for z in range(1 << h))

class Cyclo8:
    """Exact Z[omega_8] arithmetic, omega^4 = -1."""
    __slots__ = ("c",)
    def __init__(self, c=(0, 0, 0, 0)):
        self.c = tuple(c)
    @staticmethod
    def unit(k):  # omega^k
        k %= 8
        s = 1 if k < 4 else -1
        c = [0, 0, 0, 0]
        c[k % 4] = s
        return Cyclo8(c)
    def __add__(self, o):
        return Cyclo8(tuple(x + y for x, y in zip(self.c, o.c)))
    def __mul__(self, n):
        return Cyclo8(tuple(x * n for x in self.c))
    def __eq__(self, o):
        return self.c == o.c
    def __repr__(self):
        return f"Cyclo8{self.c}"

# ---------- S1 the null identity ----------

def s1_null_identity():
    print("== S1: subspace null identities ==")
    h = 9
    for dim in (3, 4, 5):
        for _ in range(30):
            basis = []
            while len(basis) < dim:
                v = random.randrange(1, 1 << h)
                if independent(basis + [v]):
                    basis.append(v)
            W = span(basis)
            for _ in range(40):
                z = random.randrange(1 << h)
                s = sum(par(v, z) for v in W if v)
                assert s in (0, 1 << (dim - 1)), (dim, s)
                if dim >= 4:
                    assert s % 8 == 0
    print("   dim-3 subspace sums in {0,4} (NOT null mod 8); dim>=4 null. OK")

def independent(vecs):
    m = list(vecs)
    r = 0
    for i in range(len(m)):
        p = None
        for j in range(r, len(m)):
            if m[j]:
                p = j
                break
        if p is None:
            return False
        m[r], m[p] = m[p], m[r]
        hb = m[r].bit_length() - 1
        for j in range(len(m)):
            if j != r and (m[j] >> hb) & 1:
                m[j] ^= m[r]
        r += 1
    return True

def span(basis):
    out = [0]
    for b in basis:
        out += [x ^ b for x in out]
    return out

def f2_rank(vecs):
    m = [v for v in vecs if v]
    r = 0
    for _ in range(len(m)):
        p = None
        for j in range(r, len(m)):
            if m[j]:
                p = j
                break
        if p is None:
            break
        m[r], m[p] = m[p], m[r]
        hb = m[r].bit_length() - 1
        for j in range(len(m)):
            if j != r and (m[j] >> hb) & 1:
                m[j] ^= m[r]
        r += 1
    return r

# ---------- S2/S3 grading iso and relation code ----------

def cubic_of_rep(rep, h):
    """P_f as (lin_mask, set of pair tuples, set of triple tuples)."""
    lin = 0
    pairs = set()
    trips = set()
    for S, a in rep.items():
        if a & 1 == 0:
            # even coefficient: contributes only even grades; check it drops out
            # 2k*par: lin += 2k (mod2 -> 0), pair += -4k (grade -2k mod 2 -> 0), trip 8k -> 0
            continue
        bits = [i for i in range(h) if (S >> i) & 1]
        for i in bits:
            lin ^= 1 << i
        for i, j in itertools.combinations(bits, 2):
            pairs ^= {(i, j)}
        for t in itertools.combinations(bits, 3):
            trips ^= {t}
    return (lin, frozenset(pairs), frozenset(trips))

def cubic_eval(P, x):
    lin, pairs, trips = P
    v = pc(lin & x) & 1
    for (i, j) in pairs:
        v ^= ((x >> i) & (x >> j)) & 1
    for (i, j, k) in trips:
        v ^= ((x >> i) & (x >> j) & (x >> k)) & 1
    return v

def s2_grading():
    print("== S2: grading map is well-defined and injective on functions mod Clifford ==")
    h = 4
    # (a) even additions leave the cubic unchanged and change f by a Clifford function
    for _ in range(50):
        rep = {S: random.randrange(8) for S in range(1, 1 << h) if random.random() < .5}
        rep2 = dict(rep)
        for S in list(rep2):
            rep2[S] = (rep2[S] + 2 * random.randrange(4)) % 8
        assert cubic_of_rep(rep, h) == cubic_of_rep(rep2, h)
    # (b) equal cubic ==> equal function up to Clifford: check the difference has
    #     all-even coefficients representation => it IS by construction here.
    # (c) equal function ==> equal cubic: exhaustively for h=3 over kernel elements.
    h3 = 3
    masks = list(range(1, 8))
    zero = ftable({}, h3)
    kercnt = 0
    bad = 0
    for coeffs in itertools.product(range(8), repeat=7):
        rep = dict(zip(masks, coeffs))
        if ftable(rep, h3) == zero:
            kercnt += 1
            if cubic_of_rep(rep, h3) != cubic_of_rep({}, h3):
                bad += 1
    # group sizes: reachable functions should number 8^3 * 4^3 * 2^1 = 65536
    # so kernel size = 8^7 / 65536 = 32768? (only if map is onto that count)
    print(f"   kernel of rep->function for h=3: {kercnt} elements; cubic!=0 on kernel: {bad}")
    assert bad == 0, "grading NOT constant on kernel -> iso broken"
    total = 8 ** 7
    print(f"   distinct functions reachable = {total // kercnt} "
          f"(predicted {8**3 * 4**3 * 2**1})")
    assert total // kercnt == 8 ** 3 * 4 ** 3 * 2 ** 1

def rm_star_generators(h, r):
    """Punctured RM(r,h): rows = monomials of degree<=r evaluated on nonzero points.
    Coordinate y (mask 1..2^h-1) <-> point y."""
    gens = []
    for deg in range(r + 1):
        for T in itertools.combinations(range(h), deg):
            row = 0
            for y in range(1, 1 << h):
                if all((y >> i) & 1 for i in T):
                    row |= 1 << (y - 1)
            gens.append(row)
    return gens

def graded_signature(rep, h):
    """(lin mod 8 per var, pair mod 8, triple mod 8) via parity expansion
    par(S) = sum_{A subset S, A nonempty} (-2)^{|A|-1} prod_A x_i."""
    lin = [0]*h
    pair = {}
    trip = {}
    for S, a in rep.items():
        bits = [i for i in range(h) if (S >> i) & 1]
        for i in bits:
            lin[i] = (lin[i] + a) % 8
        for ij in itertools.combinations(bits, 2):
            pair[ij] = (pair.get(ij, 0) - 2*a) % 8
        for t in itertools.combinations(bits, 3):
            trip[t] = (trip.get(t, 0) + 4*a) % 8
    return lin, pair, trip

def lift_codeword(c_masks, h):
    """Given odd-pattern c (list of parity masks) with cubic(c)=0, build an exact
    mod-8 relation with that odd pattern: fix pair grades then linear grades."""
    rep = {y: 1 for y in c_masks}
    lin, pair, trip = graded_signature(rep, h)
    for t, v in trip.items():
        assert v % 8 == 0, ("triple grade nonzero", t, v)
    for (i, j), v in pair.items():
        assert v % 4 == 0, ("pair grade not 0 mod 4", v)
        if v % 8 == 4:
            m = (1 << i) | (1 << j)
            rep[m] = (rep.get(m, 0) + 2) % 8   # adds -4 to that pair grade
    lin, pair, trip = graded_signature(rep, h)
    for i, v in enumerate(lin):
        if v:
            assert v % 2 == 0
            m = 1 << i
            rep[m] = (rep.get(m, 0) + (8 - v)) % 8
    return rep

def s3_relation_code():
    print("== S3: Res2(relations) = ker(cubic) = RM(h-4,h)*, constructive lifts ==")
    for h in (4, 5, 6):
        gens = rm_star_generators(h, h - 4)
        for _ in range(15):
            cw = 0
            for g in gens:
                if random.random() < .5:
                    cw ^= g
            c_masks = [y for y in range(1, 1 << h) if (cw >> (y - 1)) & 1]
            # necessary condition: cubic of the odd pattern vanishes
            P = cubic_of_rep({y: 1 for y in c_masks}, h)
            assert P == (0, frozenset(), frozenset()), (h, "cubic nonzero on RM*")
            # constructive lift is an exact mod-8 relation
            rep = lift_codeword(c_masks, h)
            for z in range(1 << h):
                assert feval(rep, z) == 0, (h, z)
        dim_rm = f2_rank(gens)
        want = (1 << h) - 1 - (h + h*(h-1)//2 + h*(h-1)*(h-2)//6)
        assert dim_rm == want
        print(f"   h={h}: dim RM* = {dim_rm} = 2^h-1 - (h + C(h,2) + C(h,3)); "
              f"random codewords lift to exact relations. OK")
    print("   => Res2(relations) = RM(h-4,h)* exactly (dim count + inclusion, both local).")

# ---------- S4 delta*: period filtration ----------

def period_group(P, h):
    """Poly-time period group of cubic P via 3-step filtration. Returns basis."""
    lin, pairs, trips = P
    # Step 1: quadratic part of Delta_w P must vanish:
    #   for each pair (j,k): sum_{i:(i,j,k) in D} w_i = 0.
    eqs = {}
    for (i, j, k) in trips:
        for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
            eqs.setdefault((b, c), 0)
            eqs[(b, c)] |= 1 << a
    W = nullspace(list(eqs.values()), h)
    # Step 2: linear part of Delta_w P on W must vanish. For w in W (additive there):
    #   linpart_k(w) = sum_{(i,j,k) in D} w_i w_j  +  sum over pairs containing k.
    def linpart(w):
        out = 0
        for (i, j, k) in trips:
            for (a, b, c) in ((i, j, k), (j, i, k), (k, i, j)):
                if ((w >> b) & 1) and ((w >> c) & 1):
                    out ^= 1 << a
        for (i, j) in pairs:
            if (w >> j) & 1:
                out ^= 1 << i
            if (w >> i) & 1:
                out ^= 1 << j
        return out
    W = hom_kernel(W, linpart, h)
    # Step 3: constant part = P(w) on remaining subgroup (additive there).
    W = hom_kernel(W, lambda w: cubic_eval(P, w), 1)
    return W

def nullspace(rows, h):
    """Basis of {w in F2^h : for each row R, popcount(R & w) even}. Proper RREF."""
    mat = [r for r in rows if r]
    # forward elimination to RREF (pivot = lowest set bit for simple indexing)
    pivrow = {}   # pivot column -> row
    for r in mat:
        cur = r
        while cur:
            b = cur.bit_length() - 1
            if b in pivrow:
                cur ^= pivrow[b]
            else:
                pivrow[b] = cur
                break
    # back-substitute to eliminate pivot columns from other rows
    for b in sorted(pivrow):
        for b2 in pivrow:
            if b2 != b and (pivrow[b2] >> b) & 1:
                pivrow[b2] ^= pivrow[b]
    basis = []
    pivots = set(pivrow)
    for free in range(h):
        if free in pivots:
            continue
        w = 1 << free
        for b, R in pivrow.items():
            if (R >> free) & 1:
                w |= 1 << b
        basis.append(w)
    return basis

def hom_kernel(basis, phi, out_bits):
    """Kernel of additive map phi restricted to span(basis)."""
    imgs = [phi(b) for b in basis]
    # solve sum c_i imgs_i = 0 over F2 by elimination on (img | tag) pairs
    pairs = [(imgs[i], basis[i]) for i in range(len(basis))]
    ker = []
    piv = {}
    for img, tag in pairs:
        cur_i, cur_t = img, tag
        for b in sorted(piv, reverse=True):
            if (cur_i >> b) & 1:
                pi, pt = piv[b]
                cur_i ^= pi
                cur_t ^= pt
        if cur_i == 0:
            ker.append(cur_t)
        else:
            piv[cur_i.bit_length() - 1] = (cur_i, cur_t)
    return [k for k in ker if k]

def brute_periods(P, h):
    T = [cubic_eval(P, x) for x in range(1 << h)]
    out = []
    for w in range(1, 1 << h):
        if all(T[x ^ w] == T[x] for x in range(1 << h)):
            out.append(w)
    return out

def delta_star(rep, h):
    P = cubic_of_rep(rep, h)
    K = period_group(P, h)
    return h - len(K), K, P

def s4_delta():
    print("== S4: delta* via period filtration; validate vs brute force ==")
    for h in (5, 6, 7, 8):
        for _ in range(30):
            rep = {S: random.randrange(8) for S in range(1, 1 << h)
                   if random.random() < .3}
            P = cubic_of_rep(rep, h)
            K = period_group(P, h)
            Kb = brute_periods(P, h)
            assert len(span(K)) - 1 == len(Kb), (h, sorted(span(K))[1:], Kb)
    print("   filtration == brute periods on 120 random instances (h=5..8). OK")
    # planted instances: f = g(L z) + Clifford junk, generic g on d vars
    for (h, d) in ((8, 3), (10, 4), (12, 5), (16, 6)):
        # random surjective L: F2^h -> F2^d as d rows
        rows = []
        while f2_rank(rows) < d:
            rows = [random.randrange(1, 1 << h) for _ in range(d)]
        # generic g: random odd coeffs on all parities of d vars
        g = {u: random.choice((1, 3, 5, 7)) for u in range(1, 1 << d)}
        # pull back: parity u of (Lz) = parity(pullback mask) of z
        rep = {}
        for u, a in g.items():
            m = 0
            for i in range(d):
                if (u >> i) & 1:
                    m ^= rows[i]
            rep[m] = (rep.get(m, 0) + a) % 8
        # Clifford junk
        for _ in range(2 * h):
            S = random.randrange(1, 1 << h)
            rep[S] = (rep.get(S, 0) + 2 * random.randrange(4)) % 8
        ds, K, P = delta_star(rep, h)
        if h <= 9:
            Kb = brute_periods(P, h)
            assert len(span(K)) - 1 == len(Kb), "filtration wrong on planted"
        print(f"   planted h={h} d={d}: delta* = {ds}")
        assert ds <= d
        if ds < d:
            print("     (generic g degenerate this draw — rare, acceptable)")
    print("   delta* recovers planted dimension. OK")

# ---------- S5 t*: coset minimum weight ----------

def tstar(rep, h):
    """Exact min T-count = min weight over coset odd(rep) + RM(h-4,h)*.
    Feasible h<=6."""
    x = 0
    for S, a in rep.items():
        if a & 1:
            x ^= 1 << (S - 1)
    gens = rm_star_generators(h, h - 4)
    gens = reduce_basis(gens)
    k = len(gens)
    best = pc(x)
    cur = x
    # Gray code over 2^k codewords
    for i in range(1, 1 << k):
        cur ^= gens[(i & -i).bit_length() - 1]
        w = pc(cur)
        if w < best:
            best = w
    return best

def reduce_basis(gens):
    out = []
    piv = {}
    for g in gens:
        cur = g
        for b in sorted(piv, reverse=True):
            if (cur >> b) & 1:
                cur ^= piv[b]
        if cur:
            piv[cur.bit_length() - 1] = cur
    return list(piv.values())

def s5_tstar():
    print("== S5: exact t* (coset min weight) ==")
    # sanity: the all-parities function on 4 vars is Clifford (t*=... its odd
    # vector is the all-ones = the null codeword, so t* = 0)
    rep = {S: 1 for S in range(1, 16)}
    assert tstar(rep, 4) == 0
    print("   all-15-parities on h=4: t* = 0 (it is the null identity). OK")
    # IRIS's own demo: 14 odd parities of rank 4 -> equivalent to 1 parity
    rep = {S: 1 for S in range(1, 15)}   # drop parity 15
    ds, _, _ = delta_star(rep, 4)
    ts = tstar(rep, 4)
    print(f"   14 parities (drop one): t* = {ts}, delta* = {ds}   "
          f"(IRIS's 14->1 example: known move)")
    assert ts == 1 and ds == 1
    # embedding invariance: planted d=4 generic inside h=5
    g = {u: random.choice((1, 3, 5, 7)) for u in range(1, 16)}
    t_d = tstar(g, 4)
    rows = []
    while f2_rank(rows) < 4:
        rows = [random.randrange(1, 32) for _ in range(4)]
    rep5 = {}
    for u, a in g.items():
        m = 0
        for i in range(4):
            if (u >> i) & 1:
                m ^= rows[i]
        rep5[m] = (rep5.get(m, 0) + a) % 8
    t_h = tstar(rep5, 5)
    print(f"   embedding d=4 generic into h=5: t*_d = {t_d}, t*_h = {t_h}")
    assert t_h == t_d

def s6_separation():
    print("== S6: rank price vs weight price on dense random functions ==")
    print("   d  delta*  t*(min/med/max over draws)   d^2/6  (d^2+d)/2+1   "
          "2^delta*   2^{0.396 t*_med}")
    rows = []
    for d, draws in ((4, 40), (5, 40), (6, 6)):
        ts_all = []
        ds_all = []
        for _ in range(draws):
            g = {u: random.choice((1, 3, 5, 7)) for u in range(1, 1 << d)
                 if random.random() < .8}
            ds, _, _ = delta_star(g, d)
            ts_all.append(tstar(g, d))
            ds_all.append(ds)
        ts_all.sort()
        med = ts_all[len(ts_all) // 2]
        rows.append((d, max(ds_all), ts_all[0], med, ts_all[-1]))
        print(f"   {d}  {max(ds_all)}      {ts_all[0]}/{med}/{ts_all[-1]}"
              f"                 {d*d/6:.1f}   {(d*d+d)//2+1}          "
              f"{1 << max(ds_all)}       {2**(0.396*med):.1f}")
    return rows

# ---------- S7 exact factored amplitude ----------

def s7_amplitude():
    print("== S7: exact amplitude via 2^{delta*} enumeration == ")
    h, d = 10, 4
    rows = []
    while f2_rank(rows) < d:
        rows = [random.randrange(1, 1 << h) for _ in range(d)]
    g = {u: random.choice((1, 3, 5, 7)) for u in range(1, 1 << d)}
    rep = {}
    for u, a in g.items():
        m = 0
        for i in range(d):
            if (u >> i) & 1:
                m ^= rows[i]
        rep[m] = (rep.get(m, 0) + a) % 8
    for _ in range(h):
        S = random.randrange(1, 1 << h)
        rep[S] = (rep.get(S, 0) + 2 * random.randrange(4)) % 8
    # brute: sum over 2^h
    brute = Cyclo8()
    for z in range(1 << h):
        brute = brute + Cyclo8.unit(feval(rep, z))
    # factored: delta* many variables. Need f as function of coset representatives:
    ds, K, P = delta_star(rep, h)
    Kfull = span(K)
    # choose transversal: greedy complement basis
    comp = []
    for i in range(h):
        if f2_rank(K + comp + [1 << i]) > f2_rank(K + comp):
            comp.append(1 << i)
    assert len(comp) == ds
    fac = Cyclo8()
    for bits in range(1 << ds):
        z = 0
        for i in range(ds):
            if (bits >> i) & 1:
                z ^= comp[i]
        # f constant-mod-Clifford on z+K, but the *value* needs the true f plus
        # the Clifford part is NOT constant on cosets. So factored evaluation must
        # sum the Clifford part over the coset exactly: do it as a sub-sum.
        sub = Cyclo8()
        for k in Kfull:
            sub = sub + Cyclo8.unit(feval(rep, z ^ k))
        fac = fac + sub
    assert brute == fac
    # The honest cost note: naive coset summation is still 2^h. The real algorithm
    # Gauss-sums the Clifford part in closed form; here we only validate values.
    print(f"   h={h}, delta*={ds}: brute 2^{h} sum == coset-organized sum. OK")
    print("   (full IRIS-2-style closed-form Gauss sum per coset: future work)")

# ---------- S8 optional pyzx ----------

def s8_pyzx():
    print("== S8: pyzx cross-check (post-simplification T-count vs t*) ==")
    try:
        import pyzx as zx
    except ImportError:
        print("   pyzx not installed; skipped.")
        return
    for d in (4, 5):
        g = {u: random.choice((1, 3, 5, 7)) for u in range(1, 1 << d)}
        ts = tstar(g, d)
        c = zx.Circuit(d)
        for S, a in g.items():
            bits = [i for i in range(d) if (S >> i) & 1]
            for b in bits[:-1]:
                c.add_gate("CNOT", b, bits[-1])
            for _ in range(a):
                c.add_gate("T", bits[-1])
            for b in reversed(bits[:-1]):
                c.add_gate("CNOT", b, bits[-1])
        gph = c.to_graph()
        zx.simplify.full_reduce(gph)
        tc = zx.tcount(gph)
        print(f"   d={d}: exact t* = {ts}, pyzx full_reduce tcount = {tc}, "
              f"delta* = {delta_star(g, d)[0]}")

if __name__ == "__main__":
    t0 = time.time()
    s1_null_identity()
    s2_grading()
    s3_relation_code()
    s5_tstar()
    print("(S4/S6/S7 disabled -- superseded by rank_price2.py)")
    print(f"\nall sections done in {time.time()-t0:.1f}s")
