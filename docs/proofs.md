# The intersection lemma, proved

Setting: h >= 4 (h <= 3 degenerates trivially: the relation code is zero and
every map below is injective). Patterns are subsets c of F2^h \ {0}, identified
with vectors in F2^(2^h - 1) indexed by nonzero points y. C_h denotes the space
of polynomials over F2 of degree <= 3 with zero constant term;
f(h) := dim C_h = h + C(h,2) + C(h,3). For a nonzero mask m,

    Q(m) := e1(supp m) + e2(supp m) + e3(supp m)  in C_h,

and the grading map is Phi(c) := sum_{y in c} Q(y). Numerical verification of
every lemma: `lemma_check.py` (steps A-D).

## Lemma 1 (Phi is the syndrome map of the cubic evaluation code)

For every monomial x^T with 1 <= |T| <= 3, the coefficient of x^T in Phi(c)
equals #{y in c : supp y >= T} mod 2 = <c, ev(x^T)>, where ev(g) := (g(y))_{y != 0}.
Consequently Phi(c) = 0 iff c is orthogonal to ev(C_h).

Proof. e_d(supp y) contains x^T iff T is a subset of supp y; and
x^T(y) = prod_{i in T} y_i = [T subset of supp y]. Sum over y in c.  QED
(Verified: lemma_check.py step A.)

## Lemma 2 (Dual pair; kernel = punctured Reed-Muller)

ev(C_h) is the shortening of RM(3,h) at the point 0, of dimension f(h), and

    { c : Phi(c) = 0 } = RM(h-4, h)*   (punctured at 0).

Proof. Orthogonality: for deg p <= h-4 and g in C_h, deg(pg) <= h-1, and the
only multilinear monomial with odd sum over F2^h is x_1...x_h; hence
sum_{y != 0} p(y) g(y) = sum_{all y} (pg)(y) - p(0)g(0) = 0 - 0 = 0.
Injectivity of ev on C_h: a nonzero multilinear polynomial vanishing on all
y != 0 must be a multiple of the point-indicator delta_0, which has degree h > 3.
Dimensions: dim RM(h-4,h)* = 2^h - 1 - f(h) (puncturing preserves dimension
since d_min = 16 > 1), and (2^h - 1 - f(h)) + f(h) = 2^h - 1, the code length.
So the two codes are exact annihilators, and by Lemma 1 the kernel of Phi is
the annihilator of ev(C_h), i.e. RM(h-4,h)*.  QED
(Verified: step B, plus rank_price.py S3 constructive lifts.)

Corollary: Phi(c) = Phi(c') iff c + c' in RM(h-4,h)*. Clifford-equivalence
classes of odd patterns are exactly RM cosets, and Phi computes the syndrome.
Amy-Mosca decode this coset for WEIGHT; delta* decodes it for RANK of support.

## Theorem 3 (Independence)

Let e_1, ..., e_n in F2^h be linearly independent, and for S a subset of [n]
with 1 <= |S| <= 3 put m_S := xor of {e_i : i in S}. Then the vectors
{ Q(m_S) } are linearly independent in C_h.

Proof. Suppose sum_{S in F} Q(m_S) = 0 for a nonempty family F. The m_S are
pairwise distinct and nonzero (independence), so c_F := {m_S : S in F} is a
nonempty pattern with Phi(c_F) = 0; by Lemma 1, c_F is orthogonal to ev(C_h).
Choose dual functionals lambda_1, ..., lambda_n in F2^h with
lambda_j . e_i = delta_ij (they exist because the e_i are independent). For
T with 1 <= |T| <= 3 define g_T := prod_{j in T} (lambda_j . x), a product of
at most three homogeneous linear forms, hence g_T in C_h, and

    g_T(m_S) = prod_{j in T} [j in S] = [T subset of S].

Let S0 be an element of F of maximal cardinality. Then

    <c_F, ev(g_{S0})> = #{ S in F : S >= S0 } = 1,

because every S in F has |S| <= |S0|, so S >= S0 forces S = S0. This
contradicts orthogonality.  QED
(Verified: step C — 45 random configurations, witness value always 1.)

## Lemma 4 (Reduction of >= 4-fold combinations; span)

With V = span(e_1..e_v): W_V := span{ Q(m) : m in V \ 0 } is spanned by the
Q(m_S) with |S| <= 3.

Proof. Let m = m_S with |S| = k >= 4; pick distinct a,b,c in S and set
u1 = xor of {e_i : i in S \ {a,b,c}}, u2 = e_a, u3 = e_b, u4 = e_c — four
independent vectors. For W = span(u1..u4) and any g in C_h, the pullback
g(t1 u1 + ... + t4 u4) is a polynomial of degree <= 3 in t over F2, so its sum
over F2^4 vanishes (degree < 4), giving sum_{y in W \ 0} g(y) = -g(0) = 0.
By Lemma 1, Phi(15-pattern of W) = 0, i.e.

    Q(u1+u2+u3+u4) = sum over the other 14 nonzero combinations of Q(.).

The left side is Q(m_S); on the right, every combination containing u1 is an
e-fold of size <= k-1 and every combination without u1 is a <= 3-fold.
Induct on k.  QED
(Verified: step D. Note this one-line degree argument re-derives the
cubic-level content of the mod-8 "spider nest" null identity.)

## Corollary 5 (Dimension and basis)

dim W_V = f(v) = v + C(v,2) + C(v,3), with basis { Q(m_S) : 1 <= |S| <= 3 }
built on any basis of V. (Theorem 3 gives independence, Lemma 4 the span;
the count is f(v).)

## Theorem 6 (Intersection lemma)

For subspaces V1, V2 of F2^h:   W_{V1} ∩ W_{V2} = W_{V1 ∩ V2}.

Proof. The inclusion >= is clear. Choose an adapted basis: c_1..c_r a basis of
V1 ∩ V2, extended by a_1..a_p to a basis of V1 and by b_1..b_q to a basis of
V2; the union {c, a, b} is linearly independent (a dependence would place a
nonzero combination of the a's inside V2, hence inside V1 ∩ V2, contradicting
the basis extension). By Corollary 5, W_{V1} has basis Q(m_S) over <= 3-subsets
S of the (c,a)-indices, and W_{V2} over <= 3-subsets of the (c,b)-indices.
Both are subfamilies of { Q(m_S) : S a <= 3-subset of the (c,a,b)-indices },
which is independent by Theorem 3 applied to the union basis. Therefore

    dim(W_{V1} + W_{V2}) = f(r+p) + f(r+q) - f(r)

(the two generator families overlap exactly in the f(r) generators indexed by
subsets of the c-indices), whence

    dim(W_{V1} ∩ W_{V2}) = f(r+p) + f(r+q) - dim(W_{V1}+W_{V2}) = f(r)
                        = dim W_{V1 ∩ V2},

and the inclusion >= is an equality.  QED

## Corollary 7 (Canonical core; delta* is a dimension)

For an odd pattern c let V(c) := { V : the coset c + RM(h-4,h)* contains a
pattern supported in V }. Since "coset meets patterns-in-V" iff
Phi(c) in W_V (Lemma 2 + surjectivity of Phi from patterns-in-V onto W_V),
Theorem 6 makes V(c) closed under intersection. Hence V(c) has a UNIQUE
minimal element V0(c) (the intersection of all members), and

    delta*(c) = dim V0(c),
    { w : some coset element avoids direction w } = V0(c)^perp, a subspace,
    delta*(c) = h - dim V0(c)^perp.

Membership of a given direction w is a polynomial-size linear feasibility test
(is Phi(c) in W_{w^perp}?, with the constructive basis of Corollary 5).
Finding V0 without enumerating directions remains the open algorithmic
problem; the characterization itself is now unconditional.

## Status

Everything the experiments flagged as "conjecture, 100% record" is now proved:
Theorems 3 and 6 and Corollary 7 close the intersection lemma and the
canonical-core characterization of delta*. Open problems remaining:
(1) poly(h) computation of V0 (vs. poly(2^h) membership scans);
(2) hardness of exact delta* (compare: exact T-count is NP-hard,
    van de Wetering-Amy arXiv:2310.05958);
(3) delta* vs focused rank-width (which dominates?).

---

# Addendum: delta* is polynomial-time computable

(Validation: `delta_poly.py` — 142/142 exact matches against brute-force
coset scans: 120 random h=4,5; 20 planted-and-scrambled h=5; 2 exhaustive
4.2M-codeword scans at h=6. Scale (sparse path): planted d recovered exactly at
h=30/0.06s, h=40/0.7s, h=64 with 2554 gadgets/1.6s, h=128 with 17232
gadgets/190s. This section resolves open problem (1) above, in the positive.)

## Lemma 8 (Annihilator of W_V)

Identify a functional phi on C_h with its coefficient family (phi_T)_{1<=|T|<=3}
via phi(P) = sum_T phi_T P_T, and with the polynomial
phi-hat(x) := sum_T phi_T x^T (degree <= 3, no constant). Then

    phi(Q(m)) = phi-hat(m),

so phi annihilates W_V iff phi-hat vanishes on V. Moreover ALL of Ann(W_V)
arises this way: restriction of no-constant cubics to V is surjective onto
no-constant cubics on V (pull back through dual functionals), so
dim{cubics vanishing on V} = f(h) - f(v) = f(h) - dim W_V = dim Ann(W_V),
and the inclusion is an equality.

Proof of the display: <Q(m), x^T> = [T subset of supp m] (Lemma 1 applied to
the one-element pattern), so phi(Q(m)) = sum_{T subset supp m} phi_T
= phi-hat(m).  QED

## Lemma 9 (Cubics vanishing on a hyperplane)

For w != 0, the space of no-constant cubics vanishing on w^perp equals
{ ml(l_w * q) : deg q <= 2 }, where l_w(x) = w.x and ml is multilinear
reduction (x_i^2 = x_i).

Proof. Inclusion: l_w * q vanishes where l_w does. Dimensions: cubics
vanishing on w^perp correspond to arbitrary degree-<=3 functions on the coset
{l_w = 1}, of dimension f(h) - f(h-1) = 1 + (h-1) + C(h-1,2). The map
q -> ml(l_w q) on the (1+h+C(h,2))-dimensional space of deg-<=2 polynomials
has kernel {q : q = 0 on {l_w=1}} of dimension h, so its image has dimension
1 + C(h,2) - ... = 1 + (h-1) + C(h-1,2) as well (using C(h,2) = C(h-1,2)+h-1).
Image inside, dimensions equal: the spaces coincide.  QED

## Theorem 10 (Polynomial-time rank price)

Define the collapse-flattening M_P in F_2^{h x (1+h+C(h,2))}: rows i in [h],
columns q in {1} u {x_j} u {x_j x_k : j<k}, entry = the coefficient in P of
ml(x_i * q); concretely

    M_P[i, 1]       = P_lin[i]
    M_P[i, x_j]     = P_lin[i]        if j = i,  else P_pair[{i,j}]
    M_P[i, x_j x_k] = P_pair[{i,k}]   if i = j
                      P_pair[{i,j}]   if i = k
                      P_trip[{i,j,k}] otherwise.

Then V0^perp = left kernel of M_P and delta* = rank_F2(M_P). Both are
computable in O(h^4) arithmetic from P, and P is computable from a t-parity
circuit description in O(t h^3). Hence delta* is polynomial-time computable
-- in sharp contrast with the weight objective t*, whose exact optimization
is NP-hard (van de Wetering-Amy, arXiv:2310.05958).

Proof. w in V0^perp iff Phi(c) in W_{w^perp} (Corollary 7). By Lemma 8 this
holds iff phi(P) = 0 for every functional phi with phi-hat vanishing on
w^perp; by Lemma 9 those phi-hat are exactly the ml(l_w q). Since
ml(l_w q) is linear in w for fixed q, the condition over all q is
w M_P = 0 (the row of M_P at basis vector e_i lists the values on the q-basis;
bilinearity extends to all w). Rank-nullity gives delta* = h - dim ker =
rank(M_P).  QED

## Corollary 11 (Constructive sparse representative)

From ker(M_P) compute V0 = (left kernel)^perp, pick a basis, and express P in
the basis {Q(m_S) : |S| <= 3} of W_{V0} (Corollary 5) by solving a linear
system of size f(delta*). This yields an equivalent representation supported
on at most f(delta*) = delta* + C(delta*,2) + C(delta*,3) parities inside a
delta*-dimensional space -- i.e. a constructive t <= O(delta*^3) bound and
the residual-enumeration pipeline (change basis, enumerate 2^{delta*},
Gauss-sum the Clifford rest) is fully polynomial-time-preprocessed.

## Consequences

- The simulation price poly * 2^{delta*} is achievable with polynomial-time
  preprocessing, exactly, for any Clifford+T phase-polynomial block.
- delta* slots into de Colnet et al.'s parametric hybrid as a CONSTRUCTIVE
  price function, satisfying their "computable in polynomial time" interface
  requirement -- something the NP-hard t* cannot do exactly.
- The rank-vs-weight contrast is now complete:
    weight decoding of the RM coset: NP-hard, price 2^{0.396 t*};
    rank decoding of the same coset: polynomial, price 2^{delta*};
    with log2(t*+1) <= delta* <= t*, and delta* << 0.396 t* on dense-core
    families (delta* = Theta(sqrt(t*))).

---

# Theorem 12 (the 4k-1 law for GF(2^k) multipliers)

Premises, each mechanically verified on the benchmark files (gf_law.py, k = 4..16;
measurements consistent through k = 256):

(P1) The circuit's non-Clifford content is exactly k^2 CCZ/CCZ-dagger gates;
     the (i,j)-th acts on three DISTINCT single-variable, constant-free wire
     forms (x_i, y_j, z_{pi(i,j)}), where x = the k a-inputs, y = the k
     b-inputs, and the z's are path variables (Hadamard-opened product wires).
     All other gates are CNOT/X/H/diagonal-Clifford.
(P2) pi(i,j) = i + j: products are grouped by total degree, all 2k-1 degree
     classes occur (Mastrovito structure; reduction CNOTs act between closed
     Hadamard blocks and touch no odd parity).

Claim:  delta* = rho = 4k - 1.

Proof.
1. Grading of one gate. The CCZ phase is omega^{+-4 x y z}; its image in the
   Clifford quotient is the single cubic monomial x y z (the mod-8 function
   +-4xyz has zero linear grade, zero pair grade, triple grade 4/4 = 1;
   CCZ-dagger is -4 = 4 mod 8, identical).
2. Therefore, mod Clifford,
       P  =  T  :=  sum_{i,j in [0,k)} x_i y_j z_{i+j},
   the CONVOLUTION TENSOR, supported on U = span{x_*, y_*, z_*} with
   dim U = k + k + (2k-1) = 4k - 1  (distinctness from P1).
3. Upper bound: the odd pattern c is itself a coset element, so
   V0 <= span(supp c) <= U and delta* <= 4k - 1.
4. Lower bound. By Theorem 10, u in V0^perp iff the rows of M_P vanish on u;
   since P is a pure cubic the only nonzero block is the triple block, and the
   condition is that every contraction D(u)_{JK} = sum_I u_I T_{IJK} vanishes.
   Write u = (alpha, beta, gamma) on the x/y/z blocks.
     {J,K} = {x_i, y_j}:  D = gamma_{i+j};  (i,j) ranges over all pairs, and
        every m in [0, 2k-2] equals i+j for some pair (P2)  =>  gamma = 0.
     {J,K} = {x_i, z_m}, 0 <= m-i <= k-1:  D = beta_{m-i};  every j arises
        as m-i  =>  beta = 0.
     {J,K} = {y_j, z_m}: symmetrically  =>  alpha = 0.
   So V0^perp intersect U = 0, and with step 3, delta* = dim U = 4k - 1.  QED

Corollary 13. (a) rho = delta*: no Clifford/null-identity optimization can
compress a Mastrovito multiplier below its raw parity span — matching the
12/12 benchmark measurements (k = 4..256). (b) The exact single-amplitude
cost is poly * 2^{4k-1}, against a weight price of 2^{0.396 * Theta(k^2)}:
at k = 10, about 5x10^11 residual states versus 2^{162}.

Remark 14 (generalization). The argument uses only that each slot-contraction
of the tensor pins one coordinate at a time: any phase structure of "grouped
products" x_i y_j z_{pi(i,j)} with pi surjective and (i, pi(i,j)) determining
j (and symmetrically) has delta* = (#x) + (#y) + (#classes). Convolution-type
arithmetic — polynomial multiplication, carry-free integer multiplication —
falls in this class; this is why the separation family "occurs in the wild."

---

# Corrections and prior-art scoping after the duplication hunt (pass 3)

A 101-agent adversarial novelty sweep (7 angles, full-text verification)
found NO duplicate of: the rank objective delta* on the Z_8 coset, the
intersection-closure/canonical-core theorem, the poly-time coset-rank
formula, or the poly*2^{delta*} simulation theorem. It found three
mandatory citations and forced one correction.

MANDATORY CITATIONS (adjacent-but-distinct):
- Brier-Langevin 2003 (and the 2026 ten-variable classification,
  arXiv:2606.28473): the "radical"/"effective dimension" of a Boolean CUBIC
  form modulo RM(2,m) under GL(m,2), computed by the trilinear-form
  flattening. This preempts the TOP-GRADE layer of Theorem 10's matrix.
  Our novelty is the full Z_8 lift: the mod-4/mod-2 collapse blocks, the
  intersection lemma over the whole Clifford quotient, the canonical core,
  and the simulation theorem. Scope all claims accordingly.
- Khoruzhii-Gelss-Pokutta (arXiv:2602.15285): same cubic Clifford-quotient
  invariant, same GF(2^k)-multiplier family, but COUNT-type objectives
  (CP rank = CCZ count, Waring rank = T-count) with Karatsuba-style
  O(k^{log2 3}) decompositions. Closest active competitor program.
- Liu-Clark CAMPS (arXiv:2412.17209) and Clifft (arXiv:2604.27058):
  simulation costs already of the shape poly * 2^{GF(2)-dimension}, but as
  CIRCUIT-TRACE quantities (pivot/heuristic-dependent), not operator
  invariants minimized over a Clifford coset. Also cite Kopparty-Potukuchi
  (arXiv:1712.06039) for the RM-syndrome/tensor dictionary, and
  Labib (arXiv:2107.10551) / Bu-Gu-Jaffe (arXiv:2508.15908) for mod-8 cubic
  phases in higher-order Fourier analysis (their "rank" is Green-Tao
  degree-rank, not span dimension).

CORRECTION TO COROLLARY 13(b) — the "t = Theta(k^2)" claim is WRONG at the
coset-optimal level and is hereby rescoped:
- What is Theta(k^2): the RAW parity count of the Mastrovito realization
  (and what shipped tools like pyzx full_reduce retain).
- What is NOT Theta(k^2): the coset-optimal T-count t*. Bilinear-complexity
  decompositions are LEGAL COSET MOVES: a bilinear algorithm for GF(2^k)
  multiplication with R products of linear forms rewrites the invariant as
  R rank-1 trilinear terms on parities of the SAME variables, so
  t* <= 7R = 7 * M_bilinear(k) = O(k^{log2 3}) by Karatsuba, and O(k) by
  Chudnovsky-type constructions. Combined with the hierarchy bound
  t* >= delta* = 4k - 1 (Theorem 12), we get

      t*(GF(2^k) multiplier pattern) = Theta(k),
      within the constant window [4k-1, 7*M_bilinear(k)].

- Two consequences, one negative and one positive:
  (i) The PROVABLE superpolynomial rank-vs-weight separation does NOT hold
      on the multiplier family at the coset optimum: 2^{0.396 t*} with
      t* = Theta(k) and 2^{4k-1} differ only in constants in the exponent;
      which wins depends on M_bilinear(k)/k (rank wins iff
      0.396 * 7 * M(k)/k > 4, i.e. M(k) > 1.44k -- true for all KNOWN
      constructions, open at the optimum). The provable separation lives on
      the GENERIC dense-core family (counting bound t* >= ~d^2/6), which is
      immune to this correction.
  (ii) NEW BRIDGE, a gift from the correction: Theorem 12 plus the
      hierarchy yields a LINEAR LOWER BOUND t* >= 4k-1 on the T-count of
      multiplier phase patterns -- a coset-model complement to bilinear
      complexity lower bounds, connecting T-count optimization of
      convolution-type circuits to the bilinear complexity of
      multiplication (up to the factor 7 and Clifford corrections).

Residual novelty risks (from the sweep's own caveats): the citer sets of
Amy-Mosca/Heyfron-Campbell were spot-checked, not certified-exhaustively
swept; several load-bearing sources are 2026 preprints; Labib appears on
both the HOFA and Clifft teams, so convergence on span-dimension invariants
from that direction is live. Re-run a targeted arXiv check immediately
before posting.
