"""Emit the counting-task circuits as OpenQASM for the quizx head-to-head.
Usage: python3 research/emit_qasm.py 4 5 6 7 8 10
Requires vendor/feynman (see README) for the benchmark .qc sources."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench import parse_qc

def emit(k, outdir='research/benchmarks/qasm'):
    labels, inputs, gates = parse_qc(f'vendor/feynman/benchmarks/qc/gf2^{k}_mult.qc')
    idx = {}
    for q in labels:
        kind, i = q[0], int(q[1:])
        idx[q] = {'a': 0, 'b': k, 'c': 2*k}[kind] + i
    L = ["OPENQASM 2.0;", 'include "qelib1.inc";', f"qreg q[{3*k}];"]
    for name, args in gates:
        n_ = name.lower()
        base = name.rstrip("*d'")
        if n_ == 'h':
            L.append(f"h q[{idx[args[0]]}];")
        elif base in ('Z', 'z') and len(args) == 3:
            a, b, c = (idx[x] for x in args)
            L.append(f"ccz q[{a}],q[{b}],q[{c}];")
        elif n_ in ('tof', 'cnot', 'cx') and len(args) == 2:
            L.append(f"cx q[{idx[args[0]]}],q[{idx[args[1]]}];")
        elif n_ == 'x' and len(args) == 1:
            L.append(f"x q[{idx[args[0]]}];")
        else:
            raise RuntimeError(name)
    os.makedirs(outdir, exist_ok=True)
    open(f'{outdir}/gf{k}.qasm', 'w').write("\n".join(L) + "\n")
    print(f"k={k}: {len(L)-3} gates")

if __name__ == '__main__':
    for k in map(int, sys.argv[1:] or ['4', '5', '6', '7', '8', '10']):
        emit(k)
