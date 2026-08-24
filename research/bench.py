"""Benchmark delta* on the feynman .qc suite.

Pipeline per circuit:
  parse .qc -> track affine wire forms over (input vars + path vars);
  T/Td toggle odd-gadget masks; CCZ/CCZd add the 7 Selinger parities;
  CCX = H CCZ H. Inputs are symbolic (matches feynman's verification task).
  Then: t_raw = #distinct odd masks, rho = rank(masks),
  rotate masks into rho coordinates, delta* = rank(M_P) via the fast
  pair-block bitmask construction (no explicit cubic).
"""
import itertools, os, sys, time, csv, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def pc(x): return bin(x).count('1')

# ---------- .qc parser ----------

def parse_qc(path):
    gates = []
    labels = {}
    inputs = []
    for raw in open(path):
        line = raw.split('#')[0].strip()
        if not line: continue
        tok = line.split()
        if tok[0] == '.v':
            for q in tok[1:]:
                labels.setdefault(q, len(labels))
        elif tok[0] == '.i':
            inputs = tok[1:]
        elif tok[0].startswith('.') or tok[0] in ('BEGIN','END','begin','end'):
            continue
        else:
            gates.append((tok[0], tok[1:]))
    return labels, inputs, gates

class Unsupported(Exception): pass

def extract_gadgets(labels, inputs, gates):
    """returns (odd_masks dict, nvars, stats)"""
    nq = len(labels)
    nvar = 0
    var_of_input = {}
    for q in inputs:
        var_of_input[q] = nvar; nvar += 1
    form = {}
    for q in labels:
        form[q] = (1 << (var_of_input[q] + 1)) if q in var_of_input else 0
        # bit 0 = affine constant
    odd = {}
    h_count = 0
    stats = dict(n=nq, gates=len(gates), tof3=0, t_explicit=0, ccz=0)

    def newvar():
        nonlocal nvar, h_count
        v = nvar; nvar += 1; h_count += 1
        return 1 << (v + 1)

    def toggle(mask):
        m = mask & ~1
        if m:
            odd[m] = odd.get(m, 0) ^ 1

    def ccz(fa, fb, fc):
        stats['ccz'] += 1
        for combo in (fa, fb, fc, fa^fb, fb^fc, fa^fc, fa^fb^fc):
            toggle(combo)

    for name, args in gates:
        base = name.rstrip('*d').rstrip("'")
        dag = name != base and name not in ('cnot','swap','tof')
        n_ = name.lower()
        if n_ in ('h',):
            form[args[0]] = newvar()
        elif n_ in ('x','y') and len(args) == 1:
            form[args[0]] ^= 1
        elif base in ('Z','z') and len(args) == 1:
            pass
        elif base in ('Z','z') and len(args) == 2:
            pass  # CZ: even phase
        elif base in ('Z','z') and len(args) == 3:
            ccz(form[args[0]], form[args[1]], form[args[2]])
        elif base in ('S','P','s','p') and len(args) == 1:
            pass  # even
        elif base in ('T','t') and len(args) == 1 and name.lower() not in ('tof',):
            stats['t_explicit'] += 1
            toggle(form[args[0]])
        elif n_ in ('tof','cnot','cx') :
            if len(args) == 1:
                form[args[0]] ^= 1
            elif len(args) == 2:
                form[args[1]] ^= form[args[0]]
            elif len(args) == 3:
                stats['tof3'] += 1
                form[args[2]] = newvar()
                ccz(form[args[0]], form[args[1]], form[args[2]])
                form[args[2]] = newvar()
            else:
                raise Unsupported(name + ' ' + str(len(args)))
        elif n_ == 'swap' and len(args) == 2:
            form[args[0]], form[args[1]] = form[args[1]], form[args[0]]
        elif n_ == 'cz' and len(args) == 2:
            pass
        else:
            raise Unsupported(f"{name}/{len(args)}")
    masks = [m >> 1 for m, v in odd.items() if v]   # drop const bit position
    stats['h'] = h_count
    stats['nvar'] = nvar
    return masks, nvar, stats

# ---------- rank and coordinates ----------

def basis_reduce_track(masks):
    """echelon basis with coordinate tracking: returns (rho, coords list)"""
    piv = {}   # pivot bit -> (vec, coordvec)
    coords = []
    order = []
    for m in masks:
        cur, cvec = m, 0
        while cur:
            b = cur.bit_length() - 1
            if b in piv:
                pv, pcv = piv[b]
                cur ^= pv; cvec ^= pcv
            else:
                idx = len(order)
                piv[b] = (cur, cvec | (1 << idx))
                order.append(b)
                cvec = cvec | (1 << idx)
                break
        coords.append(cvec)
    return len(order), coords

def MP_rank_fast(masks_rho, rho):
    """rank of the collapse-flattening, pair-block bitmask construction"""
    if rho == 0: return 0
    off = [0]*rho
    acc = 0
    for j in range(rho):
        off[j] = acc; acc += rho - j - 1
    npair = acc
    def pairbits(m):
        out = 0
        mm = m
        while mm:
            j = (mm & -mm).bit_length() - 1
            mm &= mm - 1
            out ^= ((m >> (j+1)) << off[j])
        return out
    L = 0
    PP = [0]*rho
    rowT = [0]*rho
    for m in masks_rho:
        L ^= m
        pb = pairbits(m)
        mm = m
        while mm:
            i = (mm & -mm).bit_length() - 1
            mm &= mm - 1
            PP[i] ^= m
            rowT[i] ^= pb
    slotmask = [0]*rho
    for i in range(rho):
        sm = 0
        for k in range(i+1, rho):
            sm |= 1 << (off[i] + (k - i - 1))
        for j in range(i):
            sm |= 1 << (off[j] + (i - j - 1))
        slotmask[i] = sm
    rows = []
    for i in range(rho):
        Li = (L >> i) & 1
        xblock = PP[i]
        if Li: xblock |= 1 << i
        else: xblock &= ~(1 << i)
        spread = 0
        ppi = PP[i]
        for k in range(rho):
            if k == i: continue
            if (ppi >> k) & 1:
                if k > i: spread |= 1 << (off[i] + (k - i - 1))
                else: spread |= 1 << (off[k] + (i - k - 1))
        tblock = (rowT[i] & ~slotmask[i]) | spread
        row = Li | (xblock << 1) | (tblock << (1 + rho))
        rows.append(row)
    piv = {}
    for r in rows:
        cur = r
        while cur:
            b = cur.bit_length() - 1
            if b in piv: cur ^= piv[b]
            else:
                piv[b] = cur; break
    return len(piv)

def selftest():
    from rank_price2 import cubic_of_pattern
    from delta_poly import MP_rank, cubic_of_masks
    import random
    random.seed(5)
    for rho in (3,5,8,12):
        for _ in range(30):
            masks = list({random.randrange(1, 1 << rho)
                          for _ in range(random.randrange(1, 3*rho))})
            slow = MP_rank(cubic_of_masks(masks, rho), rho)
            fast = MP_rank_fast(masks, rho)
            assert slow == fast, (rho, masks, slow, fast)
    print("selftest: fast M_P == reference on 120 cases. OK")

# ---------- pyzx column ----------

class Alarm(Exception): pass

def pyzx_tcount(path, gatecap=4000, seconds=120):
    try:
        import pyzx as zx
    except ImportError:
        return None
    def handler(s, f): raise Alarm()
    old = signal.signal(signal.SIGALRM, handler)
    signal.alarm(seconds)
    try:
        c = zx.Circuit.load(path)
        if len(c.gates) > gatecap:
            return 'big'
        g = c.to_graph()
        zx.simplify.full_reduce(g)
        return zx.tcount(g)
    except Alarm:
        return 'timeout'
    except Exception as e:
        return f'err'
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)

# ---------- main ----------

def main():
    selftest()
    qcdir = 'vendor/feynman/benchmarks/qc'
    out = []
    RHO_CAP = 1100
    for fn in sorted(os.listdir(qcdir)):
        if not fn.endswith('.qc'): continue
        path = os.path.join(qcdir, fn)
        try:
            labels, inputs, gates = parse_qc(path)
            t0 = time.time()
            masks, nvar, st = extract_gadgets(labels, inputs, gates)
            t_raw = len(masks)
            rho, coords = basis_reduce_track(masks)
            if rho <= RHO_CAP:
                ds = MP_rank_fast(coords, rho)
                t_delta = time.time() - t0
            else:
                ds = None; t_delta = None
            tz = pyzx_tcount(path)
            row = dict(circuit=fn[:-3], n=st['n'], gates=st['gates'],
                       tof3=st['tof3'], t_explicit=st['t_explicit'],
                       nvar=nvar, t_raw=t_raw, rho=rho, delta=ds,
                       pyzx_t=tz,
                       sec=round(t_delta,2) if t_delta is not None else None)
        except Unsupported as e:
            row = dict(circuit=fn[:-3], n='-', gates='-', tof3='-',
                       t_explicit='-', nvar='-', t_raw='-', rho='-',
                       delta=f'skip:{e}', pyzx_t='-', sec='-')
        except Exception as e:
            row = dict(circuit=fn[:-3], n='-', gates='-', tof3='-',
                       t_explicit='-', nvar='-', t_raw='-', rho='-',
                       delta=f'ERR:{type(e).__name__}', pyzx_t='-', sec='-')
        out.append(row)
        print(f"{row['circuit']:22} n={row['n']:>4} gates={row['gates']:>6} "
              f"tof3={row['tof3']:>5} Texp={row['t_explicit']:>5} "
              f"vars={row['nvar']:>5} t_raw={row['t_raw']:>6} rho={row['rho']:>4} "
              f"delta*={row['delta']!s:>10} pyzx_t={row['pyzx_t']!s:>7} "
              f"({row['sec']}s)", flush=True)
    os.makedirs('research/benchmarks', exist_ok=True)
    with open('research/benchmarks/results.csv','w',newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(out[0].keys()))
        w.writeheader()
        for r in out: w.writerow(r)
    print("\nwrote research/benchmarks/results.csv")

if __name__ == '__main__':
    main()
