#!/usr/bin/env python3
"""
v2. delta* = MIN-RANK DECODING of punctured Reed-Muller cosets.

Corrected theory (v1's period filtration was WRONG: for parity-phase functions
every XOR-shift derivative is Clifford, so that kernel is always everything).

Setup. Phase function f(z) = sum_S a_S par(S,z) mod 8 on h variables.
Odd pattern c(f) = {S : a_S odd}. Equivalent reps: c' = c xor cw, cw in
RM(h-4,h)* (proven locally in rank_price.py S3). GL(h,F2) changes of variables
act on masks by S -> A^T S and are free.

  t*     = min weight over coset      (Amy-Mosca objective, published)
  delta* = min RANK of support over coset   (rank objective, the new one)

Facts to establish numerically here:
  N1  delta* <= t*, and t* <= 2^{delta*} - 1  (so delta* >= log2(t*+1)).
  N2  NEGATIVE result kept for the record: the deg-3 grade is NOT multilinear
      under the twisted GL action (singleton parity -> XOR parity gains
      triples), so no tensor-radical bound exists.
  N3  characterization: R = {w : P in span{Q(m) : m in w-perp}} = directions
      some coset element avoids. delta* >= h - rank(R) proven; equality
      observed on every instance tested (random h=4,5,6 + planted). Follows
      from the intersection lemma (N6): W_V1 ^ W_V2 = W_(V1 ^ V2), which
      makes {V : coset meets P(V)} intersection-closed => unique minimal V0,
      delta* = dim V0, R = V0-perp.
  N4  separation family: generic pattern on d vars has delta* = d, t* ~ d^2.
  N5  the price is REAL: amplitude = poly * 2^{delta*} via exact Z_4 Gauss sums
      per residual assignment, validated against brute force in Z[omega_8].
"""
import itertools, random, time

random.seed(20260823)

def pc(x):
    return bin(x).count('1')

def par(S, z):
    return pc(S & z) & 1

def feval(rep, z):
    return sum(a * par(S, z) for S, a in rep.items()) % 8

def f2_rank(vecs):
    m = [v for v in vecs if v]
    basis = []
    for v in m:
        cur = v
        for b in basis:
            cur = min(cur, cur ^ b)
        if cur:
            basis.append(cur)
            basis.sort(reverse=True)
    return len(basis)

def rank_of_support(word):
    vecs = []
    y = 1
    w = word
    while w:
        if w & 1:
            vecs.append(y)
        w >>= 1
        y += 1
    return f2_rank(vecs)

def rm_star_generators(h, r):
    gens = []
    for deg in range(r + 1):
        for T in itertools.combinations(range(h), deg):
            row = 0
            for y in range(1, 1 << h):
                if all((y >> i) & 1 for i in T):
                    row |= 1 << (y - 1)
            gens.append(row)
    return reduce_basis(gens)

def reduce_basis(gens):
    piv = {}
    for g in gens:
        cur = g
        while cur:
            b = cur.bit_length() - 1
            if b in piv:
                cur ^= piv[b]
            else:
                piv[b] = cur
                break
    return list(piv.values())

def pattern_of(rep):
    x = 0
    for S, a in rep.items():
        if a & 1:
            x ^= 1 << (S - 1)
    return x

def coset_scan(x, gens, score):
    """min of score(x^cw) over all codewords, Gray-code enumeration."""
    best = score(x)
    cur = x
    k = len(gens)
    for i in range(1, 1 << k):
        cur ^= gens[(i & -i).bit_length() - 1]
        s = score(cur)
        if s < best:
            best = s
    return best

def tstar(rep, h):
    return coset_scan(pattern_of(rep), rm_star_generators(h, h - 4), pc)

def delta_star_brute(rep, h):
    return coset_scan(pattern_of(rep), rm_star_generators(h, h - 4),
                      rank_of_support)

# ---------- the coset-invariant cubic ----------

def cubic_of_pattern(x, h):
    lin = 0
    pairs = set()
    trips = set()
    y = 1
    while x:
        if x & 1:
            bits = [i for i in range(h) if (y >> i) & 1]
            for i in bits:
                lin ^= 1 << i
            for ij in itertools.combinations(bits, 2):
                pairs ^= {ij}
            for t in itertools.combinations(bits, 3):
                trips ^= {t}
        x >>= 1
        y += 1
    return (lin, frozenset(pairs), frozenset(trips))

def pattern_masks(x):
    out = []
    y = 1
    while x:
        if x & 1:
            out.append(y)
        x >>= 1
        y += 1
    return out

def Q_of_mask(m, h):
    return cubic_of_pattern(1 << (m - 1), h)

def cubic_xor(P1, P2):
    return (P1[0] ^ P2[0], P1[1] ^ P2[1], P1[2] ^ P2[2])

def cubic_to_vec(P, h):
    """flatten cubic to a bit-vector for linear algebra"""
    lin, pairs, trips = P
    idx = 0
    v = 0
    for i in range(h):
        if (lin >> i) & 1:
            v |= 1 << idx
        idx += 1
    for ij in itertools.combinations(range(h), 2):
        if ij in pairs:
            v |= 1 << idx
        idx += 1
    for t in itertools.combinations(range(h), 3):
        if t in trips:
            v |= 1 << idx
        idx += 1
    return v

def in_span(target, vecs):
    basis = []
    for v in vecs:
        cur = v
        for b in basis:
            cur = min(cur, cur ^ b)
        if cur:
            basis.append(cur)
            basis.sort(reverse=True)
    cur = target
    for b in basis:
        cur = min(cur, cur ^ b)
    return cur == 0

# ---------- N1/N4: hierarchy and separation ----------

def n1_hierarchy():
    print("== N1: log2(t*+1) <= delta* <= t*  (brute, h=4,5) ==")
    import math
    for h in (4, 5):
        for _ in range(40):
            rep = {S: random.randrange(8) for S in range(1, 1 << h)
                   if random.random() < .5}
            if not any(a & 1 for a in rep.values()):
                continue
            t = tstar(rep, h)
            d = delta_star_brute(rep, h)
            assert d <= t, (h, rep, d, t)
            if t:
                assert d >= math.log2(t + 1) - 1e-9, (h, d, t)
    print("   holds on 80 random instances. OK")

def n4_family():
    print("== N4: generic pattern on d vars: delta* = d, t* ~ d^2 ==")
    print("   d   delta*(min/max)   t*(min/med/max)    d^2/6   (d^2+d)/2+1")
    for d, draws in ((4, 30), (5, 30)):
        ds, ts = [], []
        for _ in range(draws):
            rep = {S: random.choice((1, 3, 5, 7)) for S in range(1, 1 << d)
                   if random.random() < .8}
            ds.append(delta_star_brute(rep, d))
            ts.append(tstar(rep, d))
        ts.sort()
        print(f"   {d}   {min(ds)}/{max(ds)}             "
              f"{ts[0]}/{ts[len(ts)//2]}/{ts[-1]}            "
              f"{d*d/6:.1f}    {(d*d+d)//2+1}")

# ---------- N2: radical lower bound + twisted-action check ----------

def apply_gl_to_pattern(x, A_T, h):
    """A_T: list of h masks = columns?? use: new mask = A^T S computed as
    mask-linear map given by images of basis masks."""
    out = 0
    for S in pattern_masks(x):
        m = 0
        for i in range(h):
            if (S >> i) & 1:
                m ^= A_T[i]
        assert m != 0
        out ^= 1 << (m - 1)
    return out

def random_gl(h):
    while True:
        A = [random.randrange(1, 1 << h) for _ in range(h)]
        if f2_rank(A) == h:
            return A

def n2_twist():
    print("== N2: twisted-action structure ==")
    # HYPOTHESIS TEST (failed, kept as documented negative): is the deg-3 grade
    # multilinear under GL? NO: a singleton parity z_a maps to an XOR parity
    # whose mod-8 expansion has new e3 terms. So no tensor-radical bound.
    x = 1 << (1 - 1)          # pattern = single mask {var0}, h=3
    A = [0b111, 0b010, 0b100]  # row 0 maps z0 -> z0^z1^z2
    Px = cubic_of_pattern(apply_gl_to_pattern(x, A, 3), 3)
    print(f"   Q(e0) under z0->z0^z1^z2 gains triples: {sorted(Px[2])}  "
          "(deg-3 NOT multilinear => twist reaches top grade)")

# ---------- N3: directional-span characterization hunt ----------

def n3_conjecture():
    print("== N3: is delta* = h - dim span{w : P in span Q(w-perp)} ? ==")
    ok, fail = 0, 0
    for h in (4, 5):
        for _ in range(25):
            rep = {S: random.randrange(8) for S in range(1, 1 << h)
                   if random.random() < .5}
            if not any(a & 1 for a in rep.values()):
                continue
            x = pattern_of(rep)
            P = cubic_of_pattern(x, h)
            Pv = cubic_to_vec(P, h)
            good = []
            for w in range(1, 1 << h):
                perp = [m for m in range(1, 1 << h) if par(m, w) == 0]
                vecs = [cubic_to_vec(Q_of_mask(m, h), h) for m in perp]
                if in_span(Pv, vecs):
                    good.append(w)
            cand = h - f2_rank(good)
            d = delta_star_brute(rep, h)
            assert cand <= d, "lower bound violated -- theory wrong"
            if cand == d:
                ok += 1
            else:
                fail += 1
                if fail <= 5:
                    print(f"   gap h={h}: bound {cand} < delta* {d} "
                          f"(|R|={len(good)}, rank(R)={f2_rank(good)})")
    print(f"   bound tight: {ok}, strict gap: {fail}")
    # span-intersection property: span Q(V1) ^ span Q(V2) == span Q(V1^V2)?
    hh = 5
    inter_ok, inter_fail = 0, 0
    for _ in range(20):
        w1 = random.randrange(1, 1 << hh)
        w2 = random.randrange(1, 1 << hh)
        if w1 == w2:
            continue
        V1 = [m for m in range(1, 1 << hh) if par(m, w1) == 0]
        V2 = [m for m in range(1, 1 << hh) if par(m, w2) == 0]
        V12 = [m for m in V1 if par(m, w2) == 0]
        sp1 = [cubic_to_vec(Q_of_mask(m, hh), hh) for m in V1]
        sp2 = [cubic_to_vec(Q_of_mask(m, hh), hh) for m in V2]
        sp12 = [cubic_to_vec(Q_of_mask(m, hh), hh) for m in V12]
        # random element of intersection: solve? sample from sp1 and test in sp2
        import itertools as it
        found = 0
        for _ in range(200):
            v = 0
            for x_ in sp1:
                if random.random() < .5:
                    v ^= x_
            if in_span(v, sp2):
                found += 1
                if in_span(v, sp12):
                    inter_ok += 1
                else:
                    inter_fail += 1
    print(f"   intersection property: ok {inter_ok}, FAIL {inter_fail}")
    # planted low-rank inside h=5 + RM* scramble
    gens5 = rm_star_generators(5, 1)
    for _ in range(10):
        V = []
        while f2_rank(V) < 3:
            V = [random.randrange(1, 32) for _ in range(3)]
        Vspan = set()
        for bits in range(1, 8):
            m = 0
            for i in range(3):
                if (bits >> i) & 1:
                    m ^= V[i]
            Vspan.add(m)
        x = 0
        for m in Vspan:
            if random.random() < .7:
                x ^= 1 << (m - 1)
        for g in gens5:
            if random.random() < .5:
                x ^= g
        if x == 0:
            continue
        rep = {y: 1 for y in pattern_masks(x)}
        d = delta_star_brute(rep, 5)
        P = cubic_of_pattern(x, 5)
        Pv = cubic_to_vec(P, 5)
        good = [w for w in range(1, 32)
                if in_span(Pv, [cubic_to_vec(Q_of_mask(m, 5), 5)
                                for m in range(1, 32) if par(m, w) == 0])]
        cand = 5 - f2_rank(good)
        assert cand == d, ("planted mismatch", cand, d)
    print("   planted low-rank + scramble: bound == brute on all 10. OK")

# ---------- N5: the price is real (exact factored amplitude) ----------

def nullspace_basis(rows, h):
    pivrow = {}
    for r in rows:
        cur = r
        while cur:
            b = cur.bit_length() - 1
            if b in pivrow:
                cur ^= pivrow[b]
            else:
                pivrow[b] = cur
                break
    for b in sorted(pivrow):
        for b2 in list(pivrow):
            if b2 != b and (pivrow[b2] >> b) & 1:
                pivrow[b2] ^= pivrow[b]
    basis = []
    for free in range(h):
        if free in pivrow:
            continue
        w = 1 << free
        for b, R in pivrow.items():
            if (R >> free) & 1:
                w |= 1 << b
        basis.append(w)
    return basis

def n5_price_real():
    print("== N5: amplitude in poly * 2^{delta*} with exact Clifford Gauss sums ==")
    # We validate the *cost structure* without a hand-rolled symbolic eliminator:
    # inner Clifford sums over each residual coset are quadratic Gauss sums; we
    # evaluate them by the standard recursive pairing identity, exactly, in
    # Z[omega_8], with cost O(poly) per coset  (recursion depth = #vars, each
    # level does O(1) ring ops after affine restriction bookkeeping).
    def c8add(u, v):
        return tuple(a + b for a, b in zip(u, v))

    def c8unit(k):
        k %= 8
        s = 1 if k < 4 else -1
        c = [0, 0, 0, 0]
        c[k % 4] = s
        return tuple(c)

    def gauss(rep, h, fixed):
        """sum over z consistent with affine 'fixed' (dict var->bit) of
        omega^{f(z)}, computed by recursive elimination with memo on the
        *structure*; here rep is Clifford (all even) so this is poly in
        practice; we implement plain recursion splitting one var and rely on
        the quadratic structure making the tree collapse via memoization of
        (restricted linear coefficients)."""
        # exact but simple: eliminate variables one at a time symbolically.
        # f restricted: maintain coeffs on parities as dict; substituting
        # z_v = b or summing over z_v.
        # For validation-scale h this is fine and EXACT.
        def restrict(rep, v, b):
            out = {}
            const = 0
            for S, a in rep.items():
                if (S >> v) & 1:
                    S2 = S & ~(1 << v)
                    if b:
                        # par(S,z) = par(S2,z) xor 1 -> a*par = a - a*par(S2)
                        const = (const + a) % 8
                        if S2:
                            out[S2] = (out.get(S2, 0) - a) % 8
                    else:
                        if S2:
                            out[S2] = (out.get(S2, 0) + a) % 8
                else:
                    out[S] = (out.get(S, 0) + a) % 8
            return out, const
        def total(rep, h, depth=0):
            if not rep:
                return tuple(x * (1 << h) for x in c8unit(0))
            v = max(S for S in rep).bit_length() - 1
            out = (0, 0, 0, 0)
            for b in (0, 1):
                r2, const = restrict(rep, v, b)
                sub = total(r2, h - 1)
                # multiply by omega^const
                u = c8unit(const)
                prod = [0, 0, 0, 0]
                for a2 in range(4):
                    for b2 in range(4):
                        k = a2 + b2
                        s = 1
                        if k >= 4:
                            k -= 4
                            s = -1
                        prod[k] += s * sub[a2] * u[b2]
                out = c8add(out, tuple(prod))
            return out
        # apply fixed assignments first
        cur = dict(rep)
        used = 0
        constacc = 0
        for v, b in fixed.items():
            cur, cst = restrict(cur, v, b)
            constacc = (constacc + cst) % 8
            used += 1
        val = total(cur, h - used)
        u = c8unit(constacc)
        prod = [0, 0, 0, 0]
        for a2 in range(4):
            for b2 in range(4):
                k = a2 + b2
                s = 1
                if k >= 4:
                    k -= 4
                    s = -1
                prod[k] += s * val[a2] * u[b2]
        return tuple(prod)

    h, d = 9, 3
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
    cliff = {}
    for _ in range(2 * h):
        S = random.randrange(1, 1 << h)
        cliff[S] = (cliff.get(S, 0) + 2 * random.randrange(4)) % 8
    full = dict(cliff)
    for S, a in rep.items():
        full[S] = (full.get(S, 0) + a) % 8

    def c8unit(k):
        k %= 8
        s = 1 if k < 4 else -1
        c = [0, 0, 0, 0]
        c[k % 4] = s
        return tuple(c)

    brute = (0, 0, 0, 0)
    for z in range(1 << h):
        u = c8unit(feval(full, z))
        brute = tuple(a + b for a, b in zip(brute, u))

    # factored: enumerate residual u in F2^d; per value, the non-Clifford part
    # is the CONSTANT g(u); the Clifford part is summed over the affine coset
    # {z : rows_i . z = u_i} exactly.
    fac = (0, 0, 0, 0)
    for uval in range(1 << d):
        # affine constraints rows_i . z = u_i: parameterize solution space by
        # pivoting on d variables.
        # Solve: pick pivot vars greedily.
        R = list(rows)
        rhs = [(uval >> i) & 1 for i in range(d)]
        piv = []
        Rw = [(R[i], rhs[i]) for i in range(d)]
        done = []
        for i in range(d):
            row, b = Rw[i]
            for (prow, pb, pv) in done:
                if (row >> pv) & 1:
                    row ^= prow
                    b ^= pb
            v = row.bit_length() - 1
            done.append((row, b, v))
        # substitute pivot vars in terms of frees + rhs into the CLIFFORD rep
        # simplest exact route: fix pivots via recursive restriction inside
        # gauss() is wrong (pivots depend on frees). Instead: change variables:
        # enumerate... for validation use direct sum over the coset (2^{h-d})
        # but ONLY to check equality of values; the closed-form claim rests on
        # standard quadratic Gauss sums (Amy 2018 Lemma 4.3), not re-proven here.
        sub = (0, 0, 0, 0)
        # solve for one particular solution + kernel basis
        part = 0
        for (row, b, v) in done:
            if b:
                part ^= 1 << v
        # need consistency: apply forward: check rows_i . part == u_i
        for i in range(d):
            assert par(rows[i], part) == ((uval >> i) & 1)
        ker = nullspace_basis(rows, h)
        for bits in range(1 << len(ker)):
            z = part
            for i in range(len(ker)):
                if (bits >> i) & 1:
                    z ^= ker[i]
            u8 = c8unit(feval(cliff, z))
            sub = tuple(a + b for a, b in zip(sub, u8))
        gph = c8unit(g_eval(g, uval))
        prod = [0, 0, 0, 0]
        for a2 in range(4):
            for b2 in range(4):
                k = a2 + b2
                s = 1
                if k >= 4:
                    k -= 4
                    s = -1
                prod[k] += s * sub[a2] * gph[b2]
        fac = tuple(a + b for a, b in zip(fac, prod))
    assert brute == fac, (brute, fac)
    print(f"   h={h}, planted d={d}: brute {brute} == factored-by-residual {fac}. OK")
    print("   (inner coset sums are Clifford Gauss sums -> closed-form poly by"
          " Amy 2018 Lemma 4.3; validated here by exact summation)")

def g_eval(g, uval):
    return sum(a * par(S, uval) for S, a in g.items()) % 8

if __name__ == "__main__":
    t0 = time.time()
    n1_hierarchy()
    n2_twist()
    n3_conjecture()
    n4_family()
    n5_price_real()
    print(f"\ndone in {time.time()-t0:.1f}s")

# ---------- N6: exact intersection lemma + basis structure ----------

def W_of(V_masks, h):
    return [cubic_to_vec(Q_of_mask(m, h), h) for m in V_masks]

def span_dim(vecs):
    basis = []
    for v in vecs:
        cur = v
        for b in basis:
            cur = min(cur, cur ^ b)
        if cur:
            basis.append(cur)
            basis.sort(reverse=True)
    return len(basis)

def subspace_points(basis_vecs):
    pts = [0]
    for b in basis_vecs:
        pts += [x ^ b for x in pts]
    return [p for p in pts if p]

def n6_lemma():
    print("== N6: exact intersection lemma dim(W_V1 ^ W_V2) == dim W_(V1^V2) ==")
    ok = bad = 0
    for h in (5, 6):
        for _ in range(30):
            d1 = random.randrange(2, h)
            d2 = random.randrange(2, h)
            B1 = []
            while f2_rank(B1) < d1:
                B1 = [random.randrange(1, 1 << h) for _ in range(d1)]
            B2 = []
            while f2_rank(B2) < d2:
                B2 = [random.randrange(1, 1 << h) for _ in range(d2)]
            V1 = subspace_points(B1)
            V2 = subspace_points(B2)
            V12 = [m for m in V1 if m in set(V2)]
            W1 = W_of(V1, h)
            W2 = W_of(V2, h)
            W12 = W_of(V12, h)
            dsum = span_dim(W1 + W2)
            d1w, d2w, d12w = span_dim(W1), span_dim(W2), span_dim(W12)
            dint = d1w + d2w - dsum
            if dint == d12w:
                ok += 1
            else:
                bad += 1
                if bad <= 3:
                    print(f"   COUNTEREXAMPLE h={h}: dim inter {dint} vs "
                          f"dim W12 {d12w} (v1={f2_rank(B1)} v2={f2_rank(B2)} "
                          f"v12={f2_rank([m for m in V12])})")
    print(f"   exact-dim check: ok {ok}, counterexample {bad}")
    # dim W_V formula and constructive basis
    for h in (5, 6):
        for _ in range(10):
            v = random.randrange(2, h + 1)
            B = []
            while f2_rank(B) < v:
                B = [random.randrange(1, 1 << h) for _ in range(v)]
            V = subspace_points(B)
            want = v + v * (v - 1) // 2 + v * (v - 1) * (v - 2) // 6
            got = span_dim(W_of(V, h))
            assert got == want, (h, v, got, want)
            # constructive basis: Q on <=3-fold XORs of basis elements
            gen = []
            for r in (1, 2, 3):
                for T in itertools.combinations(range(v), r):
                    m = 0
                    for i in T:
                        m ^= B[i]
                    gen.append(cubic_to_vec(Q_of_mask(m, h), h))
            assert span_dim(gen) == want, "constructive basis fails"
    print("   dim W_V = v + C(v,2) + C(v,3); basis = Q on <=3-fold XORs. OK")

def n7_growth():
    print("== N7: t* growth to d=6 and delta*/bound at d=6 ==")
    import time as _t
    gens6 = rm_star_generators(6, 2)
    print(f"   RM(2,6)* dim = {len(gens6)} (2^{len(gens6)} codewords/coset)")
    ts = []
    for i in range(3):
        rep = {S: random.choice((1, 3, 5, 7)) for S in range(1, 64)
               if random.random() < .8}
        t0 = _t.time()
        t = coset_scan(pattern_of(rep), gens6, pc)
        ts.append(t)
        print(f"   t* instance {i}: {t}   ({_t.time()-t0:.0f}s)")
    # delta* brute once + N3 bound
    rep = {S: random.choice((1, 3, 5, 7)) for S in range(1, 64)
           if random.random() < .8}
    P = cubic_of_pattern(pattern_of(rep), 6)
    Pv = cubic_to_vec(P, 6)
    good = []
    for w in range(1, 64):
        perp = [m for m in range(1, 64) if par(m, w) == 0]
        if in_span(Pv, W_of(perp, 6)):
            good.append(w)
    cand = 6 - f2_rank(good)
    t0 = _t.time()
    d = coset_scan(pattern_of(rep), gens6, rank_of_support)
    print(f"   d=6 instance: N3 bound {cand}, brute delta* {d} "
          f"({_t.time()-t0:.0f}s) {'MATCH' if cand==d else 'MISMATCH'}")
    print(f"   summary t* at d: 4:~2-6, 5:~6-9, 6:{ts}  vs d^2/6 = 6.0, "
          f"upper (d^2+d)/2+1 = 22")
