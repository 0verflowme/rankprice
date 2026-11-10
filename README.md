# The Rank Price
### the interference dimension of Clifford+T circuits

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22724895.svg)](https://doi.org/10.5281/zenodo.22724895)

Companion code for the paper *The Rank Price: the interference dimension of
Clifford+T circuits* (Priyanshu Kumar, 2026),
DOI [10.5281/zenodo.22724895](https://doi.org/10.5281/zenodo.22724895). Exact simulation of a Clifford+T
phase polynomial costs `poly * 2^rank`, not `2^count`: representations
modulo Clifford form a coset of the punctured Reed-Muller code RM(h-4,h)*;
the literature decodes it for weight (T-count, NP-hard), this work decodes
it for rank, which turns out to be polynomial-time.

Results backed by this repository:

- **Canonical core**: the grading map is the syndrome map of the dual pair
  (punctured RM(h-4,h), shortened RM(3,h)); supporting subspaces form an
  intersection-closed family with a unique minimal core V0;
  delta* = dim V0. Full proofs: `docs/proofs.md`.
- **Polynomial-time algorithm**: delta* = rank of an explicit h x O(h^2)
  matrix; validated 142/142 against brute-force coset scans.
- **The 4k-1 law**: delta*(GF(2^k) Mastrovito multiplier) = 4k-1 exactly;
  corollary: a linear lower bound on multiplier T-count in the coset model.
- **Benchmarks**: rank price beats the generic weight bar 2^{0.396t} on
  33/40 circuits of the feynman suite (`research/benchmarks/results.csv`).
  The paper (Zenodo v1) reports 25/40; see Corrections below.
- **Wall-clock**: exact Z[omega_8] engine (`tools/rankprice-rs`) wins the
  counting-task duel against quizx from k=5, reaching sizes the incumbent's
  measured curve prices in days (`research/benchmarks/timings.md`).

## Reproduce

Proof-step machine checks (Python 3.9+, stdlib only):

    python3 research/rank_price2.py     # structure + intersection lemma
    python3 research/lemma_check.py     # every proof step of docs/proofs.md
    python3 research/delta_poly.py      # poly-time delta* vs brute force
    python3 research/gf_law.py          # 4k-1 premises per benchmark file
    python3 research/review_checks.py   # corrections R1-R7 (about 90 s)
    python3 research/bench.py           # full suite table

The suite scripts need the public benchmark circuits:

    git clone --depth 1 https://github.com/meamy/feynman vendor/feynman

Wall-clock duel:

    python3 research/wallclock.py 4 5           # Python engine + validation
    python3 research/wallclock.py export 7      # emit job file
    cd tools/rankprice-rs && cargo run --release ../../research/benchmarks/job_k7.json

quizx side (optional): `git clone --depth 1 https://github.com/zxcalc/quizx
vendor/quizx`, build `tools/quizx-driver` against it, and feed it the QASM
from `python3 research/emit_qasm.py`.

## Corrections to the paper (Zenodo v1)

Full statements and checks: `docs/proofs.md`, section "Corrections after an
independent review (pass 4)", and `research/review_checks.py`.

- A coordinate bug in `research/bench.py` overstated delta* on 24 of the 40
  benchmark circuits. Corrected: delta* < rho on 26/40 (paper: 13/40) and
  rank beats 0.396 t on 33/40 (paper: 25/40). Multiplier rows are unchanged.
- The Selinger 7 -> 4 example in the hierarchy proposition leaves the CCZ
  coset. Inside the coset t*(CCZ) = 7.
- delta* is invariant under Clifford coset moves on a fixed set of path
  variables. Two circuits for the identity operator give delta* = 2 and 3.
  2^{delta*} is an upper bound on simulation cost.
- The generic-core claim now has a counting proof and an exact count.
- t* <= 7 M_bil(k) is an upper bound only; at k = 2, t* <= 18 < 21.

Historical note: `research/rank_price.py` retains, clearly marked, an early
wrong characterization of delta* (period groups) and why it fails, kept
because the failure is instructive.

## License

MIT (code). The paper text is (c) the author.
