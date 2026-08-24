"""Prove-support for the 4k-1 law: delta*(GF(2^k) multiplier) = 4k-1.

A. Idealized model: P = sum_{i,j in [0,k)} x_i y_j z_{i+j} (convolution
   tensor) realized by k^2 CCZ 7-parity gadgets on 4k-1 variables.
   Check: delta* = 4k-1 for k = 3..12 (kernel of M_P trivial).
B. Hypothesis check on the actual .qc files: every CCZ acts on three
   single-variable, constant-free forms; x/y args are input vars; z args
   are path vars; #distinct z vars = 2k-1; each (x,y) input pair occurs
   an odd number of times (exactly once).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench import parse_qc, MP_rank_fast

def pc(x): return bin(x).count('1')

# ---- A: idealized convolution model ----
def ideal_delta(k):
    nv = 4*k - 1
    X = lambda i: 1 << i
    Y = lambda j: 1 << (k + j)
    Z = lambda m: 1 << (2*k + m)
    odd = {}
    def toggle(m):
        if m: odd[m] = odd.get(m, 0) ^ 1
    for i in range(k):
        for j in range(k):
            a, b, c = X(i), Y(j), Z(i+j)
            for combo in (a, b, c, a^b, b^c, a^c, a^b^c):
                toggle(combo)
    masks = [m for m, v in odd.items() if v]
    # masks already live in nv dims; rank first
    from bench import basis_reduce_track
    rho, coords = basis_reduce_track(masks)
    return rho, MP_rank_fast(coords, rho)

print("A: idealized convolution tensor")
for k in range(3, 13):
    rho, ds = ideal_delta(k)
    status = "OK" if ds == 4*k - 1 else "FAIL"
    print(f"   k={k:>2}: rho={rho:>3} delta*={ds:>3}  4k-1={4*k-1:>3}  {status}")
    assert ds == 4*k - 1

# ---- B: hypothesis check on actual circuits ----
print("B: structural hypotheses on the benchmark files")

def check_file(k):
    path = f'vendor/feynman/benchmarks/qc/gf2^{k}_mult.qc'
    labels, inputs, gates = parse_qc(path)
    input_idx = {q: i for i, q in enumerate(inputs)}
    nvar = len(inputs)
    form = {}
    for q in labels:
        form[q] = (1 << (input_idx[q] + 1)) if q in input_idx else 0
    ccz_triples = []
    ok = True
    notes = []
    nv = nvar
    for name, args in gates:
        n_ = name.lower().rstrip('d*')
        if name.lower() == 'h':
            nv += 1
            form[args[0]] = 1 << nv   # bit0 = const
        elif n_ == 'z' and len(args) == 3:
            fs = [form[a] for a in args]
            for f in fs:
                if f & 1: ok = False; notes.append("affine const in CCZ")
                if pc(f >> 1) != 1: ok = False; notes.append("non-single-var form")
            ccz_triples.append(tuple(f >> 1 for f in fs))
        elif n_ in ('tof','cnot') and len(args) == 2:
            form[args[1]] ^= form[args[0]]
        elif n_ in ('x','y') and len(args) == 1:
            form[args[0]] ^= 1
        elif n_ in ('z','s','p','t') :
            pass
        elif n_ == 'swap':
            form[args[0]], form[args[1]] = form[args[1]], form[args[0]]
    inputmasks = set(1 << (i) for i in range(len(inputs)))
    zvars = set()
    xyc = {}
    for (fa, fb, fc) in ccz_triples:
        ins = [f for f in (fa, fb, fc) if f in {1 << i for i in range(len(inputs))}]
        zs = [f for f in (fa, fb, fc) if f not in {1 << i for i in range(len(inputs))}]
        if len(ins) != 2 or len(zs) != 1:
            ok = False; notes.append(f"CCZ not (input,input,path): {len(ins)}/{len(zs)}")
            continue
        zvars.add(zs[0])
        key = frozenset(ins)
        xyc[key] = xyc.get(key, 0) + 1
    odd_pairs = sum(1 for v in xyc.values() if v % 2 == 1)
    res = dict(k=k, n_ccz=len(ccz_triples), zvars=len(zvars),
               pairs=len(xyc), odd_pairs=odd_pairs, ok=ok)
    want_z = 2*k - 1
    good = (ok and len(zvars) == want_z and odd_pairs == k*k
            and len(xyc) == k*k)
    print(f"   k={k:>2}: CCZs={len(ccz_triples):>4} distinct-z={len(zvars):>3} "
          f"(want {want_z}) xy-pairs={len(xyc):>4} odd-multiplicity={odd_pairs:>4} "
          f"(want {k*k})  {'OK' if good else 'CHECK: '+';'.join(set(notes))}")
    return good

allgood = True
for k in (4, 5, 6, 7, 8, 9, 10, 16):
    allgood &= check_file(k)
print("hypotheses hold on all files tested" if allgood else "SOME HYPOTHESIS FAILED")
