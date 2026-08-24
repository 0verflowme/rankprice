#!/usr/bin/env python3
"""Wall-clock head-to-head on the superposition-multiplier task:

    A(a0,b0,c0) = <a0,b0,c0| C_k (H^{2k} (x) I) |0^{3k}>
                = 2^{-k} [c0 = a0*b0 in GF(2^k)]     (closed-form ground truth)

Pipeline (ours): compile full path sum -> substitute output constraints ->
delta' core via Theorem 10 -> rotate core to front -> enumerate 2^{delta'}
core assignments, each with an exact Z4 quadratic Gauss sum over the rest.
Everything in exact Z[i] / Z[omega_8]; floats only for display.

Baselines: full brute enumeration of the path sum (2^{#vars}); quizx-rust
stabilizer decomposition (driver in vendor/quizx-driver); analytic weight bar.
"""
import itertools, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench import parse_qc, basis_reduce_track, MP_rank_fast

def pc(x): return bin(x).count('1')

# ---------------- exact scalars ----------------

class Zi:
    """Z[i] exact"""
    __slots__ = ('a', 'b')
    def __init__(self, a=0, b=0): self.a = a; self.b = b
    def __mul__(s, o): return Zi(s.a*o.a - s.b*o.b, s.a*o.b + s.b*o.a)
    def __add__(s, o): return Zi(s.a + o.a, s.b + o.b)
    def __eq__(s, o): return s.a == o.a and s.b == o.b
    def __repr__(s): return f"({s.a}{s.b:+}i)"

I_POW = [Zi(1,0), Zi(0,1), Zi(-1,0), Zi(0,-1)]

class C8:
    """Z[omega_8] exact: c0 + c1 w + c2 w^2 + c3 w^3, w^4 = -1"""
    __slots__ = ('c',)
    def __init__(self, c=(0,0,0,0)): self.c = tuple(c)
    @staticmethod
    def unit(k):
        k %= 8; s = 1 if k < 4 else -1
        c = [0,0,0,0]; c[k%4] = s
        return C8(tuple(c))
    @staticmethod
    def from_zi(z):  # a + b*i, i = w^2
        return C8((z.a, 0, z.b, 0))
    def __add__(s, o): return C8(tuple(x+y for x,y in zip(s.c, o.c)))
    def __mul__(s, o):
        out = [0,0,0,0]
        for i2 in range(4):
            for j in range(4):
                k = i2 + j; sg = 1
                if k >= 4: k -= 4; sg = -1
                out[k] += sg * s.c[i2] * o.c[j]
        return C8(tuple(out))
    def __eq__(s, o): return s.c == o.c
    def __repr__(s): return f"C8{s.c}"
    def to_complex(s, hpow):
        import math
        w = complex(math.cos(math.pi/4), math.sin(math.pi/4))
        v = sum(s.c[k] * w**k for k in range(4))
        return v / (2**(hpow/2))

# ---------------- phase dicts: mask -> coeff mod 8 (bit0 of mask = const) ----

def phase_add(ph, mask, coeff):
    if coeff % 8 == 0: return
    # peel affine constant: par(A xor 1) = 1 - par(A)
    if mask & 1:
        ph['const'] = (ph.get('const', 0) + coeff) % 8
        m = mask & ~1
        if m: phase_add(ph, m, -coeff)
        return
    if mask == 0: return
    ph[mask] = (ph.get(mask, 0) + coeff) % 8
    if ph[mask] == 0: del ph[mask]

def phase_add_prod4(ph, fa, fb):
    """add 4*par(fa)*par(fb) using 4ab = 2(a + b - (a xor b))"""
    phase_add(ph, fa, 2); phase_add(ph, fb, 2); phase_add(ph, fa ^ fb, -2)

def phase_add_ccz(ph, fa, fb, fc, sign):
    """add sign*4*par(fa)par(fb)par(fc) via Selinger:
       4xyz = x+y+z-(x^y)-(y^z)-(x^z)+(x^y^z)"""
    s = 1 if sign >= 0 else -1
    for m, c in ((fa,1),(fb,1),(fc,1),(fa^fb,-1),(fb^fc,-1),(fa^fc,-1),
                 (fa^fb^fc,1)):
        phase_add(ph, m, s*c)

# ---------------- compile the task ----------------

def compile_task(k, a0, b0):
    """returns (phase dict over vars, nvars, constraints [(mask,bit)], hpow)"""
    path = f'vendor/feynman/benchmarks/qc/gf2^{k}_mult.qc'
    labels, inputs, gates = parse_qc(path)
    nv = 0
    form = {}
    ph = {}
    hpow = 0
    # H on all 2k inputs first: input wire gets fresh path var (old form = |0>)
    for q in labels:
        form[q] = 0   # all wires |0>; const bit is bit0
    def newvar():
        nonlocal nv
        nv += 1
        return 1 << nv   # bit0 reserved for const
    for q in inputs:
        v = newvar(); hpow += 1
        # H|0>: no cross term (old form 0)
        form[q] = v
    for name, args in gates:
        n_ = name.lower()
        base = name.rstrip("*d'")
        if n_ == 'h':
            old = form[args[0]]
            v = newvar(); hpow += 1
            # (-1)^{old*new} = 4*par(old)*par(new)
            if old & ~1 or (old & 1):
                phase_add_prod4(ph, old, v)
            form[args[0]] = v
        elif n_ in ('x','y') and len(args) == 1:
            form[args[0]] ^= 1
        elif base in ('Z','z') and len(args) == 3:
            sign = -1 if name != base else 1
            phase_add_ccz(ph, form[args[0]], form[args[1]], form[args[2]], sign)
        elif base in ('Z','z') and len(args) == 2:
            phase_add_prod4(ph, form[args[0]], form[args[1]])  # CZ = 4ab
        elif base in ('Z','z') and len(args) == 1:
            phase_add(ph, form[args[0]], 4)
        elif base in ('S','P','s','p') and len(args) == 1:
            phase_add(ph, form[args[0]], -2 if name != base else 2)
        elif base in ('T','t') and len(args) == 1 and n_ != 'tof':
            phase_add(ph, form[args[0]], -1 if name != base else 1)
        elif n_ in ('tof','cnot','cx'):
            if len(args) == 1: form[args[0]] ^= 1
            elif len(args) == 2: form[args[1]] ^= form[args[0]]
            else: raise RuntimeError("raw tof3 in gf2 file?")
        elif n_ == 'swap':
            form[args[0]], form[args[1]] = form[args[1]], form[args[0]]
        else:
            raise RuntimeError(f"gate {name}")
    return ph, nv, form, hpow, labels

# ---------------- constraint substitution on phase dicts ----------------

def substitute(ph, cons, nv):
    """eliminate constrained variables: solve affine system, substitute
    pivot vars as XORs of frees (+const). Parity masks compose linearly."""
    # gaussian elim on constraint masks (bit0 = const of the affine form;
    # constraint par(mask)=b means par(mask&~1) = b xor (mask&1))
    rows = []
    for mask, b in cons:
        m = mask & ~1
        bb = b ^ (mask & 1)
        if m == 0:
            if bb != 0: return None, None, None   # amplitude 0
            continue
        rows.append((m, bb))
    piv = {}
    for m, b in rows:
        cur, cb = m, b
        while cur:
            bit = cur.bit_length() - 1
            if bit in piv:
                pm, pb = piv[bit]
                cur ^= pm; cb ^= pb
            else:
                piv[bit] = (cur, cb); break
        else:
            if cb: return None, None, None
    # full reduce
    for bit in sorted(piv):
        for b2 in list(piv):
            if b2 != bit and (piv[b2][0] >> bit) & 1 and b2 != bit:
                m2, c2 = piv[b2]
                m1, c1 = piv[bit]
                piv[b2] = (m2 ^ m1, c2 ^ c1)
    # substitution: pivot bit p -> (rest of its row) xor const
    # apply to each phase mask: replace bit p by row
    sub = {}
    for p2, (m, b) in piv.items():
        sub[p2] = (m ^ (1 << p2), b)   # p = par(others) xor b
    out = {}
    if 'const' in ph:
        out['const'] = ph['const']
    for mask, c in ph.items():
        if mask == 'const': continue
        m = mask
        cst = 0
        for p2 in list(sub):
            if (m >> p2) & 1:
                om, ob = sub[p2]
                m = (m & ~(1 << p2)) ^ om
                cst ^= ob
        newmask = m | 0
        if cst: newmask ^= 1  # fold constant into affine bit
        phase_add(out, newmask, c)
    # remaining free variables: renumber densely
    used = 0
    for mask in out:
        if mask == 'const': continue
        used |= mask & ~1
    remap = {}
    for bit in range(1, nv+1):
        if (used >> bit) & 1:
            remap[bit] = len(remap) + 1
    out2 = {}
    if 'const' in out:
        out2['const'] = out['const']
    for mask, c in out.items():
        if mask == 'const': continue
        m2 = mask & 1
        mm = mask & ~1
        while mm:
            b2 = mm.bit_length() - 1
            mm &= ~(1 << b2)
            m2 |= 1 << remap[b2]
        phase_add(out2, m2, c)
    return out2, len(remap), len(piv)

# ---------------- Z4 quadratic Gauss sum (exact, non-branching) ----------

def gauss_z4(r, B, c, m):
    """sum over t in F2^m of i^{ c + sum r_i t_i + 2 sum_{i<j} B[i][j] t_i t_j }
    r: list mod 4; B: dict frozenset({i,j})->bit; returns (Zi, pow2) with
    value = Zi * 2^pow2 ... we return exact Zi including the 2-powers."""
    r = list(r); B = dict(B); c %= 4
    alive = list(range(m))
    fac = Zi(1, 0)
    while alive:
        x = alive.pop()
        a = r[x] % 4
        part = [j for j in alive if B.pop(frozenset((x, j)), 0)]
        if a % 2 == 1:
            # factor (1 +- i), phase -+ par(part)
            fac = fac * (Zi(1,1) if a == 1 else Zi(1,-1))
            s = -1 if a == 1 else 1
            # add s * (sum t_j - 2 sum_{j<j'} t_j t_j') mod 4
            for j in part:
                r[j] = (r[j] + s) % 4
            for j, j2 in itertools.combinations(part, 2):
                key = frozenset((j, j2))
                B[key] = B.get(key, 0) ^ 1
        else:
            want = 0 if a == 0 else 1
            if not part:
                if want == 1: return Zi(0,0)
                fac = fac * Zi(2,0)
                continue
            fac = fac * Zi(2,0)
            # constraint par(part) = want: substitute p = want xor rest
            p = part[0]; rest = part[1:]
            alive.remove(p)
            # r[p]*t_p with t_p = want xor par(rest):
            rp = r[p] % 4
            if rp:
                # rp * (want xor par(rest)) = rp*want + rp*(1-2want)*par(rest)
                c = (c + rp*want) % 4
                coef = (rp * (1 - 2*want)) % 4
                for j in rest:
                    r[j] = (r[j] + coef) % 4
                for j, j2 in itertools.combinations(rest, 2):
                    key = frozenset((j, j2))
                    B[key] = (B.get(key, 0) + coef) % 2  # -2*coef*pairs mod4 /2
                # NOTE: expansion: par(rest) = sum - 2*pairs (mod 4), so
                # coef*par = coef*sum - 2*coef*pairs; the pair term lands in
                # 2*B with coefficient coef mod 2.
            # cross terms 2*B[p][j]*t_p*t_j:
            for j in alive:
                if B.pop(frozenset((p, j)), 0):
                    # 2*t_j*(want xor par(rest)) mod 4
                    if want:
                        r[j] = (r[j] + 2) % 4
                    # 2*t_j*par(rest)*(1-2want) mod 4 == 2*t_j*par(rest)
                    # 2*t_j*(sum_rest t) mod 4: pairwise products:
                    for j2 in rest:
                        if j2 == j:
                            r[j] = (r[j] + 2) % 4  # t_j*t_j = t_j
                        else:
                            key = frozenset((j, j2))
                            B[key] = B.get(key, 0) ^ 1
    return fac * I_POW[c % 4]

def gauss_brute(r, B, c, m):
    tot = Zi(0,0)
    for t in range(1 << m):
        v = c
        for i2 in range(m):
            if (t >> i2) & 1: v += r[i2]
        for key, bb in B.items():
            if bb:
                i2, j = tuple(key)
                if (t >> i2) & 1 and (t >> j) & 1: v += 2
        tot = tot + I_POW[v % 4]
    return tot

def selftest_gauss():
    random.seed(11)
    for m in (0,1,2,3,5,8,10,12):
        for _ in range(40):
            r = [random.randrange(4) for _ in range(m)]
            B = {frozenset(p): random.randrange(2)
                 for p in itertools.combinations(range(m), 2)
                 if random.random() < .5}
            c = random.randrange(4)
            assert gauss_z4(r, B, c, m) == gauss_brute(r, B, c, m), (m, r, B, c)
    print("gauss_z4 selftest: 320 random forms exact. OK")

# ---------------- even phase dict -> Z4 form ----------------

def evenphase_to_z4(ph, nvars):
    """phase dict with all-even coefficients (masks bit0=const allowed) ->
    (r, B, c) with value/2 mod 4 via par(S) = sum - 2*pairs (mod 4)."""
    r = [0]*nvars
    B = {}
    c = 0
    for mask, coeff in ph.items():
        assert mask != 'const', "const must be handled by caller"
        assert coeff % 2 == 0, "odd coefficient in Clifford part"
        q = (coeff // 2) % 4
        if q == 0: continue
        const = mask & 1
        bits = []
        mm = mask & ~1
        while mm:
            b2 = mm.bit_length() - 1
            mm &= ~(1 << b2)
            bits.append(b2 - 1)   # var bits start at 1
        if const:
            # par(S xor 1) = 1 - par(S)
            c = (c + q) % 4
            q = (-q) % 4
            if q == 0: continue
        for i2 in bits:
            r[i2] = (r[i2] + q) % 4
        for i2, j in itertools.combinations(bits, 2):
            key = frozenset((i2, j))
            B[key] = (B.get(key, 0) + q) % 2   # -2q*pairs mod4: pair coeff -q mod 2
    return r, B, c

# ---------------- the factored amplitude ----------------

def amplitude_pipeline(ph, nvars):
    """returns (C8 numerator, stats). Assumes masks' odd part has core delta'.
    Enumerates 2^{delta'} and Gauss-sums the rest."""
    odd_masks = [ (m & ~1) >> 1 for m, cc in ph.items()
                  if m != 'const' and cc % 2 == 1 ]
    # (shift so var bits start at 0 for rank tools)
    rho, coords = basis_reduce_track(odd_masks)
    # basis of span in original var-space:
    # rebuild pivot info to construct rotation: we need explicit basis vectors
    piv = {}
    order = []
    for m in odd_masks:
        cur = m
        while cur:
            b2 = cur.bit_length() - 1
            if b2 in piv: cur ^= piv[b2]
            else:
                piv[b2] = cur; order.append(cur); break
    # Theorem 10 in rho coords:
    dstar = MP_rank_fast(coords, rho) if rho else 0
    # For enumeration we use the SPAN (rho) as core, not V0: simpler and
    # correct (V0 subset span); with Cor.11 rewriting we could shrink to
    # dstar -- for the gf2 task rho == dstar anyway (Thm 12).
    core_basis = order            # rho vectors in var-space
    # complete to full basis: free vars = those not pivot
    pivots = set(piv.keys())
    rest_bits = [b2 for b2 in range(nvars) if b2 not in pivots]
    # change of variables: t = sum s_core[i]*?? -- work coordinate-wise:
    # we enumerate assignments to the CORE PARITIES: choose dual: assign
    # values to pivot vars via: for a core assignment u (values of the rho
    # basis parities), pick the representative where free vars are symbolic
    # and pivot vars are determined? Simplest correct scheme:
    #   variables = pivot vars (rho of them) + rest vars.
    #   Enumerate pivot-var assignments p in F2^rho; rest stay symbolic.
    #   Odd parities depend only on ... NO: masks may include rest bits?
    #   masks lie in span(order); order vectors may include rest bits.
    # Cleanest: substitute variables: for each mask evaluation we need
    # par(S, t). Enumerate assignments to pivot vars only works if every odd
    # mask's rest-bit part is determined... not true in general.
    # Correct scheme: linear change of variables. Define new vars:
    #   s_i = par(order[i], t)  for i < rho   (these are independent forms)
    # extend with s_rest = chosen complementary coordinate forms.
    # Then t = A s for some invertible A; parities transform par(S,t) =
    # par(A^T S, s). We need A^T mapping each odd mask into span(e_core).
    # Construct dual basis: rows D with D[i] . order[j] = delta_ij, and
    # complement rows for rest coordinates.
    A_T = build_transform(order, nvars)
    ph2 = {}
    if 'const' in ph:
        ph2['const'] = ph['const']
    for mask, cc in ph.items():
        if mask == 'const': continue
        const = mask & 1
        mm = (mask & ~1) >> 1
        nm = 0
        t2 = mm
        while t2:
            b2 = t2.bit_length() - 1
            t2 &= ~(1 << b2)
            nm ^= A_T[b2]
        phase_add(ph2, (nm << 1) | const, cc)
    # now odd masks of ph2 live in first-rho coordinates
    total = C8((0,0,0,0))
    stats = dict(rho=rho, dstar=dstar, nvars=nvars)
    base_const = ph2.get('const', 0)
    for u in range(1 << rho):
        # substitute s_core = bits of u into ph2
        cst = base_const
        rem = {}
        for mask, cc in ph2.items():
            if mask == 'const': continue
            const = mask & 1
            mm = (mask & ~1) >> 1
            corepart = mm & ((1 << rho) - 1)
            restpart = mm >> rho
            bit = pc(corepart & u) & 1
            nm = (restpart << 1)  # rest coords shifted; bit0 const
            nc = const ^ bit
            if restpart == 0:
                cst = (cst + cc * nc) % 8
            else:
                phase_add(rem, (restpart << 1) | nc, cc)
        # rem must be all even now; fold rem's peeled constants into cst
        cst = (cst + rem.pop('const', 0)) % 8
        r, B, c4 = evenphase_to_z4(rem, nvars - rho)
        # total phase: omega^{cst} * i^{gauss}
        g = gauss_z4(r, B, c4, nvars - rho)
        total = total + C8.unit(cst) * C8.from_zi(g)
    return total, stats

def build_transform(order, nvars):
    """A_T[bit] for the change of variables t -> s with s_i = par(order[i], t)
    for i < rho, completed arbitrarily. Returns per-old-bit image mask so that
    par(S,t) = par(image-xor, s).  Constructed via inverse of the s(t) matrix."""
    rho = len(order)
    # s = M t with rows: order (rho rows) + complement unit rows
    pivots = set()
    red = []
    for v in order:
        red.append(v)
    # choose complement: standard basis vectors completing rank
    cur_rank_vecs = list(order)
    comp = []
    for b2 in range(nvars):
        cand = 1 << b2
        if rank_of(cur_rank_vecs + comp + [cand]) > rank_of(cur_rank_vecs + comp):
            comp.append(cand)
    rows = list(order) + comp
    n = nvars
    assert len(rows) == n
    # invert M over F2: A = M^{-1}; then t = A s, and par(S,t) = par(A^T S, s):
    # (A^T S)_j = sum_i A_ij S_i -> image of old bit i is column i of A^T =
    # row i of A. So compute A = M^{-1}, return its rows.
    M = rows
    A = [1 << i for i in range(n)]   # identity, will become M^{-1} via ops
    Mw = list(M)
    # gauss-jordan
    r2 = 0
    for col in range(n):
        p2 = None
        for rr in range(r2, n):
            if (Mw[rr] >> col) & 1: p2 = rr; break
        if p2 is None: continue
        Mw[r2], Mw[p2] = Mw[p2], Mw[r2]
        A[r2], A[p2] = A[p2], A[r2]
        for rr in range(n):
            if rr != r2 and (Mw[rr] >> col) & 1:
                Mw[rr] ^= Mw[r2]; A[rr] ^= A[r2]
        r2 += 1
    # Mw is now a permutation-ish reduced form; reorder so Mw = I
    perm = [None]*n
    for rr in range(n):
        b2 = Mw[rr].bit_length() - 1
        assert Mw[rr] == 1 << b2
        perm[b2] = A[rr]
    Ainv_rows = perm   # A[i] = row i of M^{-1}: t_i = sum_j Ainv[i]_j s_j
    # par(S, t) = sum_i S_i t_i = sum_j (sum_i S_i Ainv[i]_j) s_j
    # image mask of old bit i is Ainv_rows[i]
    return Ainv_rows

def rank_of(vecs):
    basis = []
    for v in vecs:
        cur = v
        for b2 in basis:
            cur = min(cur, cur ^ b2)
        if cur: basis.append(cur); basis.sort(reverse=True)
    return len(basis)

# ---------------- brute baseline ----------------

def amplitude_brute(ph, nvars):
    tot = C8((0,0,0,0))
    base = ph.get('const', 0)
    for t in range(1 << nvars):
        v = base
        for mask, cc in ph.items():
            if mask == 'const': continue
            const = mask & 1
            mm = (mask & ~1) >> 1
            v += cc * ((pc(mm & t) & 1) ^ const)
        tot = tot + C8.unit(v % 8)
    return tot

# ---------------- driver ----------------

def gf_product(k, a0, b0, modpoly):
    p = 0
    for j in range(k):
        if (b0 >> j) & 1: p ^= a0 << j
    for d in range(2*k-2, k-1, -1):
        if (p >> d) & 1:
            p ^= modpoly << (d - k)
    return p & ((1 << k) - 1)

MODPOLY = {4:0b10011, 5:0b100101, 6:0b1000011, 7:0b10000011,
           8:0b100011011, 9:0b1000010001, 10:0b10000001001,
           16:0b10001000000001011}

def make_cons(form, labels, k, a0, b0, c0):
    cons = []
    for q in labels:
        kind, idx = q[0], int(q[1:])
        if kind == 'a': bit = (a0 >> idx) & 1
        elif kind == 'b': bit = (b0 >> idx) & 1
        elif kind == 'c': bit = (c0 >> idx) & 1
        else: raise RuntimeError(f"label {q}")
        cons.append((form[q], bit))
    return cons

def run_k(k, do_brute=True, do_wrong=True):
    random.seed(1000 + k)
    a0 = random.randrange(1, 1 << k)
    b0 = random.randrange(1, 1 << k)
    c0 = gf_product(k, a0, b0, MODPOLY[k])
    ph, nv, form, hpow, labels = compile_task(k, a0, b0)
    cons = make_cons(form, labels, k, a0, b0, c0)
    t0 = time.time()
    ph2, nfree, npiv = substitute(ph, cons, nv)
    if ph2 is None:
        return dict(k=k, status='ZERO-inconsistent')
    num, st = amplitude_pipeline(ph2, nfree)
    t_pipe = time.time() - t0
    amp = num.to_complex(hpow)
    want = 2.0 ** (-k)
    okmag = abs(abs(amp) - want) < 1e-9 * max(1, want)
    res = dict(k=k, vars=nv, free=nfree, rho=st['rho'], dstar=st['dstar'],
               hpow=hpow, t_pipeline=round(t_pipe, 3),
               amp=abs(amp), want=want, ok=okmag)
    if do_brute and nfree <= 24:
        t0 = time.time()
        bnum = amplitude_brute(ph2, nfree)
        res['t_brute'] = round(time.time() - t0, 3)
        res['brute_match'] = (bnum == num)
    if do_wrong:
        cbad = c0 ^ 1
        consb = make_cons(form, labels, k, a0, b0, cbad)
        phb, nfb, _ = substitute(dict(ph), consb, nv)
        if phb is None:
            res['wrong_c0'] = 0.0
        else:
            nb, _ = amplitude_pipeline(phb, nfb)
            res['wrong_c0'] = abs(nb.to_complex(hpow))
    return res

def run2_k(k, do_brute=True):
    """Task 2: A = <+^{2k}, c0=1 | C | +^{2k}, 0>  = 2^{-2k} * #{(a,b): ab=1}
       = 2^{-2k} (2^k - 1).  Only the c-register is constrained; a,b input
       path variables stay free (that IS the <+| projection), bra H's add 2k
       to the normalization power."""
    ph, nv, form, hpow, labels = compile_task(k, 0, 0)
    cons = []
    for q in labels:
        if q[0] == 'c':
            idx = int(q[1:])
            cons.append((form[q], 1 if idx == 0 else 0))   # c0 = element "1"
        elif q[0] in 'ab':
            pass
    hpow_total = hpow + 2*k
    t0 = time.time()
    ph2, nfree, npiv = substitute(dict(ph), cons, nv)
    if ph2 is None:
        return dict(k=k, status='ZERO')
    num, st = amplitude_pipeline(ph2, nfree)
    t_pipe = time.time() - t0
    amp = num.to_complex(hpow_total)
    want = (2**k - 1) / 4.0**k
    res = dict(k=k, vars=nv, free=nfree, rho=st['rho'], dstar=st['dstar'],
               t_pipeline=round(t_pipe, 2), amp=round(abs(amp), 10),
               want=round(want, 10),
               ok=abs(abs(amp) - want) < 1e-9)
    if do_brute and nfree <= 20:
        t0 = time.time()
        bnum = amplitude_brute(ph2, nfree)
        res['t_brute'] = round(time.time() - t0, 2)
        res['brute_match'] = (bnum == num)
    return res


def export_job(k, path):
    """Export the counting-task residual enumeration as a job file for the
    Rust engine: after constraint substitution and the core-first rotation,
    emit every phase term as (core_mask, rest_mask, const_bit, coeff)."""
    import json
    ph, nv, form, hpow, labels = compile_task(k, 0, 0)
    cons = []
    for q in labels:
        if q[0] == 'c':
            cons.append((form[q], 1 if int(q[1:]) == 0 else 0))
    hpow_total = hpow + 2*k
    ph2, nfree, npiv = substitute(dict(ph), cons, nv)
    odd_masks = [(m & ~1) >> 1 for m, cc in ph2.items()
                 if m != 'const' and cc % 2 == 1]
    piv = {}
    order = []
    for m in odd_masks:
        cur = m
        while cur:
            b = cur.bit_length() - 1
            if b in piv:
                cur ^= piv[b]
            else:
                piv[b] = cur; order.append(cur); break
    rho = len(order)
    A_T = build_transform(order, nfree)
    terms = []
    base_const = ph2.get('const', 0)
    for mask, cc in ph2.items():
        if mask == 'const': continue
        const = mask & 1
        mm = (mask & ~1) >> 1
        nm = 0
        t2 = mm
        while t2:
            b = t2.bit_length() - 1
            t2 &= ~(1 << b)
            nm ^= A_T[b]
        core = nm & ((1 << rho) - 1)
        rest = nm >> rho
        terms.append([core, rest, const, cc % 8])
    job = dict(k=k, rho=rho, nrest=nfree - rho, hpow=hpow_total,
               base_const=base_const, terms=terms)
    with open(path, 'w') as f:
        json.dump(job, f)
    return rho, nfree - rho, len(terms)

if __name__ == '__main__':
    import sys as _s
    if 'export' in _s.argv:
        k = int(_s.argv[_s.argv.index('export') + 1])
        r = export_job(k, f'research/benchmarks/job_k{k}.json')
        print(f"k={k}: rho={r[0]} rest={r[1]} terms={r[2]}")
        _s.exit(0)
    selftest_gauss()
    print("== task 1 (all outputs pinned -- Clifford, engine validation) ==")
    for k in (4, 5, 6, 7):
        r = run_k(k, do_brute=(k <= 7), do_wrong=True)
        print(f"   k={k}: pipeline {r['t_pipeline']}s brute {r.get('t_brute','-')}s "
              f"match={r.get('brute_match','-')} amp==2^-k: {r['ok']} "
              f"wrong-c0 amp: {r.get('wrong_c0')}", flush=True)
    print("== task 2 (counting: <+,c0=1|C|+,0>, rank price active) ==")
    import sys as _s
    ks = [int(x) for x in _s.argv[1:]] or [4, 5]
    for k in ks:
        r = run2_k(k, do_brute=(k <= 4))
        print("  ", r, flush=True)
