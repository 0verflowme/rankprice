"""Machine checks for the corrections listed in docs/proofs.md (pass 4).

Each block prints PASS or raises. Python 3.9+, standard library only.
Block R5 needs the benchmark files: vendor/feynman (see README).

  R1  The 4-parity "Selinger" pattern equals CCZ times CS-dagger. It lies in
      a different Clifford coset. Inside its own coset the CCZ pattern has
      t* = 7 = 2^3 - 1 and delta* = 3.
  R2  delta* as extracted from a circuit depends on the circuit. Two circuits
      for the identity operator give delta* = 2 and delta* = 3.
  R3  Phi restricted to patterns has rank f(h), so ker Phi has the dimension
      of RM(h-4,h)*. (lemma_check.py step B finds 0 samples at h = 5.)
  R4  Generic classes have full core: the exact fraction of classes with
      delta* < d (closed recursion, checked exhaustively at d = 4) is below
      the counting bound (2^d - 1) / 2^(f(d)-f(d-1)).
  R5  After the basis_reduce_track fix: delta* = rho on every gf2^k_mult
      benchmark, delta* < rho on 26 of the 40 computed circuits, and rank
      beats 0.396 t on 33 of 40. (Before the fix the table said 13 and 25.)
  R7  basis_reduce_track is a linear change of coordinates: delta* in the
      rotated coordinates equals delta* in the original coordinates.
  R6  The k = 2 convolution tensor has bilinear rank 3, so 7*M_bil = 21.
      The raw pattern has 18 parities in the same coset. Hence t* < 7*M_bil
      and "rank wins iff M_bil(k) > 1.44k" is only a one-way implication.
"""
import cmath, csv, itertools, math, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rank_price2 import (pc, f2_rank, rm_star_generators, coset_scan,
                         rank_of_support, cubic_of_pattern, Q_of_mask,
                         cubic_to_vec, span_dim)
from delta_poly import MP_rank, cubic_of_masks
from bench import extract_gadgets, basis_reduce_track, MP_rank_fast, parse_qc

random.seed(7)
W8 = cmath.exp(1j * math.pi / 4)


def f(h):
    return h + h * (h - 1) // 2 + h * (h - 1) * (h - 2) // 6


def pattern(masks):
    x = 0
    for m in masks:
        x ^= 1 << (m - 1)
    return x


def par(m, z):
    return pc(m & z) & 1


# ---------------------------------------------------------------- R1
def r1():
    print("R1: Selinger's 4-T gate versus the CCZ coset")
    X, Y, Z = 1, 2, 4
    seven = [X, Y, Z, X ^ Y, Y ^ Z, X ^ Z, X ^ Y ^ Z]
    signs7 = [1, 1, 1, -1, -1, -1, 1]
    four = [Z, Y ^ Z, X ^ Z, X ^ Y ^ Z]
    signs4 = [1, -1, -1, 1]
    for z in range(8):
        x, y, zz = z & 1, (z >> 1) & 1, (z >> 2) & 1
        f7 = sum(s * par(m, z) for m, s in zip(seven, signs7)) % 8
        f4 = sum(s * par(m, z) for m, s in zip(four, signs4)) % 8
        assert f7 == (4 * x * y * zz) % 8
        assert f4 == (4 * x * y * zz - 2 * x * y) % 8
    print("   7-parity phase = 4xyz (CCZ); 4-parity phase = 4xyz - 2xy "
          "(CCZ times CS-dagger). PASS")

    # CS is not Clifford: CS (X tensor I) CS^dagger is not a Pauli string.
    cs = [1, 1, 1, 1j]
    xi = [[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]]
    conj = [[cs[r] * xi[r][c] * cs[c].conjugate() for c in range(4)]
            for r in range(4)]
    nz = sorted({complex(round(v.real, 9), round(v.imag, 9))
                 for row in conj for v in row if abs(v) > 1e-9},
                key=lambda v: (v.real, v.imag))
    # a Pauli string has all nonzero entries equal up to sign
    ratios = {complex(round((v / nz[0]).real, 9), round((v / nz[0]).imag, 9))
              for v in nz}
    assert not ratios <= {1, -1}, ratios
    print("   CS X CS^dagger has entries {1, i, -i}: not a Pauli, "
          "so CS is not Clifford. PASS")

    for h in (3, 4, 5, 6):
        p7 = cubic_of_pattern(pattern(seven), h)
        p4 = cubic_of_pattern(pattern(four), h)
        assert p7 == (0, frozenset(), frozenset({(0, 1, 2)}))
        assert p4 == (0, frozenset({(0, 1)}), frozenset({(0, 1, 2)}))
    print("   Phi(7-pattern) = xyz, Phi(4-pattern) = xyz + xy: "
          "different cosets, h = 3..6. PASS")

    for h in (4, 5, 6):
        gens = rm_star_generators(h, h - 4)
        t = coset_scan(pattern(seven), gens, pc)
        d = coset_scan(pattern(seven), gens, rank_of_support)
        wmin = min(pc(g) for g in gens)
        assert t == 7 and d == 3, (h, t, d)
        print(f"   h={h}: 2^{len(gens)} codewords scanned, "
              f"t*(CCZ) = {t}, delta*(CCZ) = {d}. PASS")
    print("   All h: nonzero codewords of RM(h-4,h)* weigh >= 15, "
          "so |c + w| >= 15 - 7 = 8 > 7.")
    print("   CCZ itself meets the left end: t* = 7 = 2^3 - 1.")


# ---------------------------------------------------------------- R2
def unitary(nq, gates):
    """dense unitary of a tiny gate list (h, t, t*, tof with 3 args)"""
    dim = 1 << nq
    U = [[1.0 if r == c else 0.0 for c in range(dim)] for r in range(dim)]

    def apply(G):
        nonlocal U
        U = [[sum(G[r][k] * U[k][c] for k in range(dim)) for c in range(dim)]
             for r in range(dim)]

    for name, args in gates:
        G = [[0.0] * dim for _ in range(dim)]
        if name == 'h':
            q = args[0]
            for b in range(dim):
                s = -1 if (b >> q) & 1 else 1
                G[b][b] = s / math.sqrt(2)
                G[b ^ (1 << q)][b] = 1 / math.sqrt(2)
        elif name in ('t', 't*'):
            q = args[0]
            ph = W8 if name == 't' else W8.conjugate()
            for b in range(dim):
                G[b][b] = ph if (b >> q) & 1 else 1.0
        elif name == 'tof':
            a, b_, c = args
            for b in range(dim):
                tgt = b ^ (1 << c) if (b >> a) & 1 and (b >> b_) & 1 else b
                G[tgt][b] = 1.0
        apply(G)
    return U


def is_identity(U):
    return all(abs(U[r][c] - (1 if r == c else 0)) < 1e-9
               for r in range(len(U)) for c in range(len(U)))


def circuit_delta(labels, inputs, gates):
    masks, nvar, _ = extract_gadgets(labels, inputs, gates)
    rho, coords = basis_reduce_track(masks)
    return len(masks), rho, MP_rank_fast(coords, rho), nvar


def r2():
    print("R2: delta* depends on the circuit, not only on the operator")
    lab = {'a': 0}
    g = [('T', ['a']), ('H', ['a']), ('H', ['a']), ('T*', ['a'])]
    assert is_identity(unitary(1, [('t', [0]), ('h', [0]), ('h', [0]),
                                   ('t*', [0])]))
    t, rho, d, nv = circuit_delta(lab, ['a'], g)
    assert (t, rho, d) == (2, 2, 2), (t, rho, d)
    print(f"   T H H T^dagger = identity: {nv} path variables, "
          f"odd parities {t}, rho {rho}, delta* {d}. PASS")

    lab = {'a': 0, 'b': 1, 'c': 2}
    g = [('tof', ['a', 'b', 'c']), ('tof', ['a', 'b', 'c'])]
    assert is_identity(unitary(3, [('tof', [0, 1, 2]), ('tof', [0, 1, 2])]))
    t, rho, d, nv = circuit_delta(lab, ['a', 'b', 'c'], g)
    assert (t, rho, d) == (8, 4, 3), (t, rho, d)   # core = span{a, b, z1+z3}
    print(f"   Toffoli Toffoli = identity: {nv} path variables, "
          f"odd parities {t}, rho {rho}, delta* {d}. PASS")
    print("   The identity operator has cost 1. The coset moves fix the "
          "path variables,")
    print("   so the Hadamard rule sum_y (-1)^(y(u+v)) = 2[u=v] is "
          "outside the model.")


# ---------------------------------------------------------------- R3
def r3():
    print("R3: rank of Phi on patterns equals f(h)")
    for h in (4, 5, 6, 7):
        vecs = [cubic_to_vec(Q_of_mask(m, h), h) for m in range(1, 1 << h)]
        r = span_dim(vecs)
        assert r == f(h), (h, r, f(h))
        kdim = (1 << h) - 1 - r
        gens = len(rm_star_generators(h, h - 4))
        assert kdim == gens, (h, kdim, gens)
        print(f"   h={h}: rank Phi = {r} = f(h), dim ker = {kdim} "
              f"= dim RM(h-4,h)*. PASS")


# ---------------------------------------------------------------- R4
def r4():
    print("R4: fraction of classes with delta* < d versus the counting bound")

    def cls(bits, d):
        pairs_all = list(itertools.combinations(range(d), 2))
        trips_all = list(itertools.combinations(range(d), 3))
        lin = bits & ((1 << d) - 1)
        bits >>= d
        pairs = frozenset(p for i, p in enumerate(pairs_all)
                          if (bits >> i) & 1)
        bits >>= len(pairs_all)
        trips = frozenset(t for i, t in enumerate(trips_all)
                          if (bits >> i) & 1)
        return (lin, pairs, trips)

    # exact count: every class has a unique core (Corollary 10), and the
    # classes with core exactly V correspond to full-core classes on dim V
    # variables. So 2^f(d) = sum_j [d choose j]_2 * g(j), g = full-core count.
    def gbin(n, k):
        num = den = 1
        for t in range(k):
            num *= (1 << (n - t)) - 1
            den *= (1 << (t + 1)) - 1
        return num // den

    g = {}
    for d in range(0, 13):
        g[d] = (1 << f(d)) - sum(gbin(d, j) * g[j] for j in range(d))
    exact = {d: ((1 << f(d)) - g[d]) / (1 << f(d)) for d in g}

    for d, mode in ((4, 'all'), (5, 20000), (6, 20000)):
        n = f(d)
        if mode == 'all':
            draws = range(1 << n)
            total = 1 << n
        else:
            draws = (random.getrandbits(n) for _ in range(mode))
            total = mode
        low = sum(1 for b in draws if MP_rank(cls(b, d), d) < d)
        if mode == 'all':
            assert low == (1 << n) - g[d], (low, g[d])
            print(f"   d={d} exhaustive: delta* < d on {low}/{total}, "
                  f"equal to the exact count. PASS")
        else:
            se = math.sqrt(exact[d] * (1 - exact[d]) / total)
            assert abs(low / total - exact[d]) < 4 * se
            print(f"   d={d} sampled: {low}/{total} = {low/total:.5f}, "
                  f"exact {exact[d]:.5f} (within 4 standard errors). PASS")
    for d in (4, 5, 6, 8, 10, 12):
        bound = ((1 << d) - 1) / 2 ** (f(d) - f(d - 1))
        assert exact[d] <= bound
        print(f"   d={d:>2}: exact fraction with delta* < d = {exact[d]:.3e}"
              f" <= counting bound {bound:.3e}. PASS")
    print("   Bound: a non-full core lies in one of 2^d - 1 hyperplanes, "
          "each carrying 2^f(d-1) classes.")
    print("   On d variables delta* <= d, so 2^delta* = 2^d is the cost of "
          "enumerating every variable.")


# ---------------------------------------------------------------- R5
def r5():
    print("R5: benchmark table")
    path = os.path.join(HERE, 'benchmarks', 'results.csv')
    rows = [r for r in csv.DictReader(open(path)) if r['delta'].isdigit()]
    assert len(rows) == 40, len(rows)
    strict = [r['circuit'] for r in rows if int(r['delta']) < int(r['rho'])]
    gf = [r for r in rows if r['circuit'].startswith('gf2^')]
    assert len(strict) == 26, len(strict)
    assert len(gf) == 12 and all(r['delta'] == r['rho'] for r in gf)

    def tval(r):
        return int(r['pyzx_t']) if r['pyzx_t'].isdigit() else int(r['t_raw'])
    wins = [r for r in rows if int(r['delta']) < 0.396 * tval(r)]
    assert len(wins) == 33, len(wins)
    nongf = [r for r in wins if not r['circuit'].startswith('gf2^')]
    by_rho = [r for r in rows if int(r['rho']) < 0.396 * tval(r)]
    print(f"   results.csv: 40 computed, delta* < rho on {len(strict)}, "
          f"delta* = rho on all {len(gf)} multipliers. PASS")
    print(f"   rank beats 0.396 t on {len(wins)}/40 with delta*, "
          f"{len(by_rho)}/40 with raw rho; {len(nongf)} wins are "
          f"non-multiplier circuits. PASS")
    lose = [r['circuit'] for r in rows if r not in wins]
    print(f"   weight still wins on: {', '.join(lose)}")

    qcdir = os.path.join(HERE, '..', 'vendor', 'feynman', 'benchmarks', 'qc')
    if not os.path.isdir(qcdir):
        print("   vendor/feynman absent: recomputation skipped.")
        return
    redo = 0
    for r in rows:
        if int(r['rho']) > 600:
            continue
        labels, inputs, gates = parse_qc(
            os.path.join(qcdir, r['circuit'] + '.qc'))
        masks, _, _ = extract_gadgets(labels, inputs, gates)
        rho, coords = basis_reduce_track(masks)
        d = MP_rank_fast(coords, rho)
        assert (len(masks), rho, d) == (int(r['t_raw']), int(r['rho']),
                                        int(r['delta'])), r['circuit']
        redo += 1
    print(f"   recomputed t_raw, rho, delta* from the .qc files: "
          f"{redo} circuits match results.csv. PASS")


# ---------------------------------------------------------------- R6
def r6():
    print("R6: 7*M_bil(k) is an upper bound on t*, not its value (k = 2)")
    x0, x1, y0, y1, z0, z1, z2 = (1 << i for i in range(7))
    h = 7

    def gadget(acc, a, b, c):
        for m in (a, b, c, a ^ b, b ^ c, a ^ c, a ^ b ^ c):
            acc[m] = acc.get(m, 0) ^ 1

    raw = {}
    for a, b, c in ((x0, y0, z0), (x0, y1, z1), (x1, y0, z1), (x1, y1, z2)):
        gadget(raw, a, b, c)
    kar = {}
    for a, b, c in ((x0, y0, z0 ^ z1), (x1, y1, z1 ^ z2),
                    (x0 ^ x1, y0 ^ y1, z1)):
        gadget(kar, a, b, c)
    raw_m = [m for m, v in raw.items() if v]
    kar_m = [m for m, v in kar.items() if v]
    P_raw = cubic_of_masks(raw_m, h)
    P_kar = cubic_of_masks(kar_m, h)
    want = frozenset({(0, 2, 4), (0, 3, 5), (1, 2, 5), (1, 3, 6)})
    assert P_raw == (0, frozenset(), want)
    assert P_kar == P_raw
    print(f"   raw pattern: {len(raw_m)} parities; Karatsuba pattern: "
          f"{len(kar_m)} parities; same syndrome. PASS")

    # bilinear rank >= rank of the z-flattening = 2k - 1 = 3; Karatsuba gives 3
    slices = []
    for m in range(3):
        v = 0
        for i in range(2):
            for j in range(2):
                if i + j == m:
                    v |= 1 << (2 * i + j)
        slices.append(v)
    assert f2_rank(slices) == 3
    assert len(raw_m) == 18 and len(kar_m) == 21
    assert MP_rank(P_raw, h) == 7
    print("   z-flattening rank 3, so M_bil(2) = 3 and 7*M_bil = 21; "
          "t* <= 18 < 21. PASS")
    print("   delta* = 7 = 4k - 1 at k = 2. PASS")


# ---------------------------------------------------------------- R7
def r7():
    print("R7: the rotation into rho coordinates preserves delta*")
    n = 0
    for h in (4, 6, 9, 12):
        for _ in range(60):
            masks = list({random.randrange(1, 1 << h)
                          for _ in range(random.randrange(1, 3 * h))})
            rho, coords = basis_reduce_track(masks)
            assert f2_rank(coords) == rho == f2_rank(masks)
            # linearity: XOR relations among masks hold among coords
            for _ in range(5):
                sub = random.sample(range(len(masks)),
                                    random.randrange(1, len(masks) + 1))
                xm = xc = 0
                for i in sub:
                    xm ^= masks[i]
                    xc ^= coords[i]
                assert (xm == 0) == (xc == 0)
            assert MP_rank_fast(coords, rho) == \
                MP_rank(cubic_of_masks(masks, h), h), (h, masks)
            n += 1
    print(f"   {n} random patterns: rotated delta* = original delta*. PASS")


if __name__ == '__main__':
    for block in (r1, r2, r3, r4, r5, r6, r7):
        block()
        print()
    print("all review checks passed")
