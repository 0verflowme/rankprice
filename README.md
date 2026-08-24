# The Rank Price
### the interference dimension of Clifford+T circuits

Companion code for the paper *The Rank Price: the interference dimension of
Clifford+T circuits* (P. Kumar, 2026). Exact simulation of a Clifford+T
phase polynomial costs `poly * 2^rank`, not `2^count`: representations
modulo Clifford form a coset of the punctured Reed-Muller code RM(h-4,h)*;
the literature decodes it for weight (T-count, NP-hard), this work decodes
it for rank — which turns out to be polynomial-time.

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
  25/40 circuits of the feynman suite (`research/benchmarks/results.csv`).
- **Wall-clock**: exact Z[omega_8] engine (`tools/rankprice-rs`) wins the
  counting-task duel against quizx from k=5, reaching sizes the incumbent's
  measured curve prices in days (`research/benchmarks/timings.md`).

## Reproduce

Proof-step machine checks (Python 3.9+, stdlib only):

    python3 research/rank_price2.py     # structure + intersection lemma
    python3 research/lemma_check.py     # every proof step of docs/proofs.md
    python3 research/delta_poly.py      # poly-time delta* vs brute force
    python3 research/gf_law.py          # 4k-1 premises per benchmark file
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

Historical note: `research/rank_price.py` retains, clearly marked, an early
wrong characterization of delta* (period groups) and why it fails — kept
because the failure is instructive.

## License

MIT (code). The paper text is (c) the author.
