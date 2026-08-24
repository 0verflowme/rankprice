# Measured wall-clock (counting task A = <+,c0=1|C_k|+,0> = (2^k-1)/4^k)

Machine: Apple Silicon laptop, 2026. quizx: release build, BssWithCatsDriver,
4 threads. Ours (Rust): tools/rankprice-rs, rayon. All results integer-exact
and equal to the closed form; wrong-bra controls returned exactly 0.

| k | quizx      | ours (Python) | ours (Rust) | exact answer |
|---|-----------|---------------|-------------|--------------|
| 4 | 0.03 s    | 2.0 s         | 0.002 s     | 15/256       |
| 5 | 0.88 s    | 48 s          | 0.028 s     | 31/1024      |
| 6 | 45.5 s    | 2119 s        | 0.63 s      | 63/4096      |
| 7 | 2970 s    | 32874 s       | 29.1 s      | 127/16384    |
| 8 | unreached | --            | 460 s       | 255/65536    |
| 9 | unreached | --            | 7910 s      | 511/262144   |

Presentation-robustness probe: re-expressing each CCZ as its 7-T gadget
pattern (same unitary) slowed quizx 3-6x (its simplifier re-fuses gadgets);
delta* is representation-invariant by construction.
