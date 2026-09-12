# Proof of the explicit-kernel Haar and core-series evaluation, version 1

The proof first evaluates the independently defined valuation series
\(\mathcal L_T\) of section 4 of the controlling brief. It then proves that
the actual explicit-kernel Haar core \(\mathcal J_T\) of section 5 equals
this series, including integrability and every interchange. Identification
with the paper's independently defined spherical coefficient is a separate,
unfinished task. The companion statement gives the exact verified hypotheses.
All sums over countable sets below are unordered sums of absolutely summable
families, except where a limit of damped sums is explicitly specified.

## 1. Minima, Cartan indices, and the independent summand

Fix \(q>2\), put \(t=q^{-1/2}\), and set \(S=1-t^2\).
Let \(k,j,h\in\mathbb Z\) and \(c\in\mathbb N\). The central index
\(r=0\) denotes the matrix with central coordinate zero. Indices \(r=1,2\)
denote central valuation \(-r\); they do not mean valuation zero when
\(r=0\). Set

\[
B=\min(0,k,-k,k+j,h,k+h).
\]

For \(r=0\), set \(u=B\), \(s=\min(B,k+2h)\). For \(r=1,2\), set

\[
u=\min(B,-r),\quad
w=\begin{cases}2h+c&2h=j-r,\\\min(2h,j-r)&2h\ne j-r,\end{cases}
\quad s=\min(B,k-r,-k-r,k+w).
\]

The inherited integer-minimum lemmas prove \(2u\le s\le u\le0\).
Consequently

\[
\ell=-2(s-u),\qquad b=s-2u,\qquad
n=\ell/2=u-s,\qquad H=n+b=-u
\]

are nonnegative integers, and \(\ell\) is even. The new master definitions
use these minima directly. They do not use a proposed row fraction.

Use \(\kappa_0=1\), \(\kappa_1=q(1-q^{-1})\), and \(\kappa_2=-q\).
Off \(2h=j-r\), and for every \(r=0\) triple, let the depth weight be
\(1\) at \(c=0\) and zero otherwise. On this collision locus with
\(r>0\), use

\[
p_0=\frac{q-2}{q-1},\qquad p_c=q^{-c}\quad(c\ge1).
\]

Writing this weight as \(w_r(j,h,c)\), define the actual master term

\[
m_{r,T}(k,j,h,c;U,V)=
\kappa_r S^2\delta^k
t^{3k+2j+2h+3\ell+4b}(TU)^n(TV)^b w_r(j,h,c).
\]

Every valuation exponent remains an integer power; negative valuations have
not been replaced by natural truncations. The natural conversion in the
damping lemma is used only after nonnegativity of \(n,b,H\) is proved.
It gives the exact identity \(m_{r,T}=T^H m_{r,1}\).

## 2. Cancellation-depth summation

The collision probabilities are summed by their independent definition:

\[
\sum_{c\ge1}q^{-c}=\frac{q^{-1}}{1-q^{-1}}=\frac1{q-1},
\qquad \sum_{c\ge0}p_c=1.
\]

Their norms are summable since \(q^{-1}<1\). An off-collision depth
family has one nonzero term, so also has mass one. A uniform summable
majorant for either kind is
\(\mathbf1_{c=0}+|p_c|\). Thus multiplying a norm-summable spatial
family by its actual depth distribution gives a norm-summable product
family. Its depth sum is the spatial term when the Cartan exponents are
depth-independent. This matters even for a row whose spatial domain
contains collision triples: one cannot discard positive depths simply
because that row is not named a collision row.

For the I1 collision rows the distinct parts are \(c=0\) and \(c\ge1\).
For I2 they are \(c=0\), \(c=1\), and \(c\ge2\). Their masses are,
respectively,

\[
\frac{q-2}{q-1},\qquad q^{-1},\qquad
\frac{q^{-2}}{1-q^{-1}}.
\]

The Cartan table is proved constant on each relevant positive-depth part.
The proof then multiplies the *unsummed* spatial term by the corresponding
proved depth sum. It does not assume any infinite row equals a stored value.

## 3. Partitions and geometric sums

The three spatial/depth partitions have respectively 10, 15, and 25 source
rows. I1 uses 17 disjoint cells before combining two pairs of parity cells.
Each partition is proved exhaustive and disjoint on the full integer
lattice, without a finite cutoff. Every reindexing is a Lean `Equiv` with
both inverse laws proved. The row reports give the explicit affine maps,
including parity and strict-boundary offsets; the source map identifies
each exact stored fraction and its `HasSum` declaration.

For illustration, in the positive I0 upper region the map is

\[
k=m,\quad j=-2m-2n-e-1,\quad h=-m-n-e+l,
\qquad m,n,l\in\mathbb N,\quad e\in\{0,1\}.
\]

Its inverse divides the positive offset by 2 and takes its remainder;
the proof checks both parity classes. Put \(X=TV\), \(Y=TU\). The term
on this map is

\[
S^2 X^{e+1}t^2(\delta Xt)^m(X^2t^2)^n(t^2)^l.
\]

Absolute summability follows before summing. The geometric sum in \(l\)
cancels one factor \(S\), and the two parity classes contribute \(X+X^2\).
The resulting exact fraction is
\(SXt^2(1+X)/((1-\delta Xt)(1-X^2t^2))\).
The other rows follow the same proved procedure with their own exact
maps and Cartan indices. The four old I0 rows are reused, not counted as
new infinite-row work.

All reindexed geometric ratios belong to the following list, with a
finite parity index or a finite fixed-coordinate factor where appropriate:

\[
t^2,\quad \delta TVt,\quad TVt/\delta,\quad
(TV)^2t^2,\quad TUt^2,\quad TUt^4.
\]

When \(|U|=|V|=1\), \(0\le T\le1\), \(t\le|\delta|\le1\), and
\(Tt<|\delta|\), each ratio has modulus strictly less than one.
Indeed, the only potentially sharp bound is
\(|TVt/\delta|=Tt/|\delta|<1\); all others follow from \(0<t<1\).
This proves norm summability of every original row via its bijection,
including all depth indices. Finite disjoint assembly proves norm
summability of the complete master family. No rearrangement of a
nonsummable family is invoked.

## 4. Exact normalization and the full family

The source prints normalized intermediate rows
\(\mathcal E_{0,\nu}=S I_{0,\nu}\),
\(\mathcal E_{1,\nu}=-q^{-1}I_{1,\nu}\), and
\(\mathcal E_{2,\nu}=S I_{2,\nu}\).
The inherited `regionTerms` already store the restored \(I_{r,\nu}\).
Their restoration factors relative to the printed rows are \(S^{-1}\),
\(-q\), and \(S^{-1}\). The independent source transcription audit
checks all fifty exact expressions. It is supplementary evidence; the
Lean infinite-row proofs establish the mathematical identities.

Let \(A_i,U_i,V_i\), \(0\le i<8\), be the exact inherited Weyl weights
and monomials, and define

\[
\mathcal L_T=\frac1{C_q}\sum_{i=0}^7 A_i
\sum_{r=0}^2\sum_{(k,j,h,c)\in\mathbb Z^3\times\mathbb N}
m_{r,T}(k,j,h,c;U_i,V_i).
\]

This definition is made before any row evaluation. The new proof also
establishes `HasSum` for the single family indexed by
\(\{0,\ldots,7\}\times\{0,1,2\}\times\mathbb Z^3\times\mathbb N\),
weighted by \(A_i/C_q\). Norm summability justifies converting that
unordered sum to the displayed grouping. It yields

\[
\mathcal L_T=\frac1{C_q}\sum_i A_i
\sum_{\nu=0}^{49}\operatorname{regionTerms}(t,\delta,TU_i,TV_i,\nu).
\]

Damping has been inserted in every original monomial. It has not been
inserted into the already simplified closed formula.

## 5. Undamped evaluation and principal Abel convergence

Assume \(t<|\delta|\le1\). At \(T=1\), the preceding argument gives
norm summability of the full undamped family. Assume also unitary
\(\alpha,\beta\) with \(\alpha\ne1\), \(\beta\ne1\),
\(\alpha\ne\beta\), and \(\alpha\beta\ne1\).
The Weyl denominators are nonzero from these hypotheses. The two Euler
products in the literal closed expression are nonzero because their
individual ratios have moduli \(|\delta|t<1\) and \(t/|\delta|<1\).
The positive real polynomial \(C_q\) is nonzero as well.

Only now apply the inherited theorem `Algebra.finiteCore_eq_closedCore`.
The independent transcription `paperE` uses the brief's ordered Satake
tuple \((\alpha,\alpha^{-1},\beta,\beta^{-1})\), its exact numerator,
and both denominator products. Separate algebraic proofs identify these
with `closedCore` at \(t=q^{-1/2}\). Hence
\(\mathcal L_1=E_q(\alpha,\beta,\delta)\).

For real \(0<T<1\), the damping identity gives
\(|m_{r,T}|\le|m_{r,1}|\), and each term tends to its undamped value as
\(T\uparrow1\). The already proved norm summability supplies a genuine
majorant. Tannery's theorem and finite Weyl/central summation therefore
give \(\mathcal L_T\to\mathcal L_1\). This is convergence of the
actual independent series; no limit is stipulated as a structure field.
Multiplying this evaluation and limit by \(2/(q+1)\) gives exactly the
corrected principal comparison at the series scope.

## 6. The signed special Abel limit

Set \(\delta=\varepsilon t\), \(\varepsilon\in\{1,-1\}\).
For every real \(0<T<1\), the strict inequality \(Tt<|\delta|\)
holds, so the independent series and its row assembly remain justified.
At \(T=1\), the ratio \(V/\varepsilon\) can have modulus one.
A nonzero denominator does not establish ordinary endpoint summability.

For \(\varepsilon=-1\), impose in addition
\(\alpha,\beta\ne-1\). Every rational row denominator has a nonzero
limit: the only new factors are \(1+V_i\), and the inverse Satake
parameters satisfy the same exclusion. Thus the finite damped row
expression is continuous at \(T=1\). Its value there is evaluated by
the inherited finite core identity on this regular endpoint locus.
The proved equality of the damped infinite family and this rational
expression holds throughout \(0<T<1\), and therefore transfers the
one-sided limit. Multiplication by \(2/(q+1)\) gives the desired
whole-product limit.

For \(\varepsilon=1\), the factor \((1-\varepsilon)/(q+1)\) is zero
for every \(T\). The whole product is identically zero and has limit
zero, independently of the behavior of the undamped endpoint core.
The literal endpoint quotient is nonsingular under
\(\alpha,\beta\ne1\). These two arguments combine into

\[
\lim_{T\uparrow1}\frac{1-\varepsilon}{q+1}\mathcal L_T
=\frac{1-\varepsilon}{q+1}
E_q(\alpha,\beta,\varepsilon q^{-1/2}).
\]

There is no further factor in this special comparison. No assertion of
ordinary endpoint convergence, or of parameter continuation through a
Weyl wall or \(\alpha=-1\), \(\beta=-1\) in the negative case, is
needed or made by this proof.

## 7. Intrinsic matrix indices and the measurable explicit kernel

Let F be an actual nonarchimedean local field with its Borel structure and
residue cardinality q>2. Use its canonical additive valuation v, with
v(0)=∞, and the concrete matrix

\[
g(a;x,y,z)=
\begin{pmatrix}1&0&y&z\\0&a&ax&ay\\0&0&a^{-1}&0\\0&0&0&1\end{pmatrix},
\qquad a\in F^\times.
\]

The inherited entry/minor calculation, now applied to the actual canonical
valuation, computes the minimum u of the entries and the minimum s of all
two-by-two minors. An entry equal to 1 and a minor equal to 1 show finiteness.
Every minor has valuation at least 2u by the ultrametric inequality. The
explicit minor list also gives s≤u; for the z-entry use either v(az)≤v(z)
when v(a)≤0, or v(z/a)≤v(z) when v(a)≥0. Hence 2u≤s≤u≤0 everywhere,
including zero coordinates and vanishing individual minors.

Canonical valuation is measurable because its integer level sets are
differences of open/closed valuation balls, with the singleton zero handling
∞. Finite minima and extraction of the proved finite integer values preserve
measurability. Thus n=u−s, b=s−2u, ℓ=2n and H=−u are measurable and
nonnegative. Define the finite Weyl kernel from these actual indices.
The triangle inequality and unitarity of U_i,V_i give

\[
|\Psi(g)|\le\frac{\sum_i|A_i|}{C_q}t^{6n+4b}
=\frac{\sum_i|A_i|}{C_q}q^{-3\ell/2-2b}.
\]

This is a proved explicit-kernel bound, with no spherical coefficient estimate
as a hypothesis. The Lean modules are `KernelIndices`, `KernelShells`,
`ExplicitKernel`, and `HaarKernel`.

## 8. Actual shell measures and collision transport

Normalize additive Haar by μ(O)=1. The integer ideal filtration and a
uniformizer generating the maximal ideal give ball measures q^(−j) for every
j∈ℤ. Subtract adjacent balls to obtain
μ{v(x)=j}=S q^(−j). The compact open subgroup O× constructs actual
multiplicative Haar of unit-subgroup mass one; scale it by S to obtain the
source measure ν. Translation by π^k gives ν{v(a)=k}=S for every k∈ℤ.
The countable shell partition proves sigma-finiteness. These statements are
proved for native nonnegative-extended-real measures as well as their real
values, so no infinite measure is assigned a finite value by `toReal`.

Fix z with v(z)=−r, r>0. On the collision locus 2h=j−r, fix y with v(y)=h
and put x₀=y²/z. Then v(x₀)=j. For x in the j-shell,

\[
v\big(y^2/(xz)-1\big)=v(x-x_0)-j.
\]

For c≥1, the x-set of exact collision depth c is precisely the translated
valuation shell x₀+{v(w)=j+c}; all its points remain in the j-shell. Its
additive measure is S q^(−j−c). At c=0 remove from the entire j-shell the
ball around x₀ of radius level j+1. Its measure is
S q^(−j)−q^(−j−1)=(q−2)q^(−j−1).
Dividing either measure by S q^(−j) gives exactly p_c. No assertion that
the square map is uniformly distributed on units is used.

The sets are measurable. Integrating these fixed-y sections over the h-shell
gives their actual joint x,y mass
S²q^(−j−h)p_c. Off the collision locus, and for central coordinate zero,
there is only c=0 and the full product of the two shell measures. Including
the a-shell yields the actual cell mass

\[
\mu_{\rm core}(S_{r,k,j,h,c})=S^3q^{-j-h}\omega_r(j,h,c).
\]

This is `haarLatticeCell_real_mass` and its native measure version. Its proof
uses `IntegerShells`, `PaperMultiplicativeHaar`, `ShellCollision`, and
`JointCollision`, all about actual field measures.

## 9. Measurable partition and constant integrand values

For fixed central representative, remove x=0, y=0 and xz=y². These sets
are null: the coordinate sets are products of null singletons; for z≠0
the final equation has a single x for each y, so product integration applies.
For z=0 its zero set is already y=0. Haar singleton-nullity and the required
sigma-finite hypotheses are derived for the actual field.

Every remaining point determines unique k,j,h. Off collision set c=0; on
collision the nonzero ratio y²/(xz)−1 has a finite nonnegative integer
valuation c. This constructs the unique lattice cell. Conversely its defining
equalities recover those indices. The cells are measurable, pairwise
disjoint, have finite measure, and cover almost every point. All four
properties are proved, including the inverse uniqueness argument.

On each cell the intrinsic matrix minima equal the independent integer
minima from section 1. The integrand is therefore the constant

\[
F_{r,k,j,h,c}=\delta^k(q^{-k})^{3/2}T^{-u}
 C_q^{-1}\sum_i A_i t^{3\ell+4b}U_i^{\ell/2}V_i^b.
\]

For every integer k, positivity of q gives
\((q^{-k})^{3/2}=t^{3k}\), using the laws of real powers, without
truncating negative exponents. Also q^(−j−h)=t^(2j+2h) and
H=ℓ/2+b. The source prefactors satisfy

\[
a_rS^3=\kappa_rS^2,\qquad(a_0,a_1,a_2)=(S^{-1},q,-q/S).
\]

Multiplication by the actual cell measure now gives exactly

\[
a_r\mu_{\rm core}(S_{r,k,j,h,c})F_{r,k,j,h,c}
=\sum_i\frac{A_i}{C_q}m_{r,T}(k,j,h,c;U_i,V_i).
\]

The declarations `explicitCoreIntegrand_eq_haarCellValue` and
`haarLatticeCell_prefactor_value` prove these equalities independently of the
row fractions. The restoration factors from section 4 are not applied again.

## 10. Integrability before integral/sum interchange

For each r, take norms in the last identity and apply the finite triangle
inequality. Since cell measure is nonnegative,

\[
\mu_{\rm core}(S_{r,k,j,h,c})\,|a_rF_{r,k,j,h,c}|
\le\sum_i\left|\frac{A_i}{C_q}m_{r,T}(k,j,h,c;U_i,V_i)\right|.
\]

The right side is summable over the full lattice/depth family by sections
2–4. Each left-side constant on a finite-measure cell is integrable, and its
norm integral is the displayed left side. The countable-union integrability
theorem therefore proves integrability on the cell union; the proved
almost-everywhere cover yields ordinary global Bochner integrability. The
prefactor a_r is nonzero for q>1, so the original unprefactored integrand is
also integrable.

Only after this step does countable additivity of the integral give `HasSum`
of the cell integrals to the ordinary integral. The exact cell identity and
the proved central Weyl-series `HasSum` have the same summands; uniqueness
identifies their sums. Summing the three central indices gives

\[
\mathcal J_T=J_{0,T}+J_{1,T}+J_{2,T}=\mathcal L_T.
\]

This proof is `HaarCoreAssembly.paperExplicitHaarCore_eq_latticeCore` (the
declaration itself has namespace `FourierJacobi.Analysis`). The generic
countable-fiber integration lemma `integrable_hasSum_of_countable_fibers`
has all of its cell hypotheses discharged by the actual local-field proofs.
The parameter range is 0<T≤1, t≤|δ|≤1, Tt<|δ|. No assumed norm bound,
integrability, row identity or integral-to-series equality enters the final
Haar theorem.

## 11. Transfer of evaluation and the whole signed Abel limit

On the principal interior t<|δ|≤1, section 10 applies at T=1 and at every
0<T<1. Sections 5 and 10 prove the unscaled equality \(\mathcal J_1=E_q\)
and \(\mathcal J_T\to E_q\). Multiplication by 2/(q+1) proves the
corrected principal comparison.

At δ=εt, section 10 applies to every 0<T<1 and supplies ordinary
integrability there. In the negative branch it transfers the signed Abel
limit from section 6 using equality on that open real interval. In the
positive branch the whole signed product is directly zero for every damped
T, so its limit is zero. The endpoint quotient is proved nonsingular under
α,β≠ε. This proves `explicit_haar_core_evaluation`,
`explicit_haar_special_abel`, and both `corrected_*_haar_comparison`
theorems. Their filter is exactly `𝓝[Set.Ioo (0 : ℝ) 1] 1`.

These conclusions are unconditional theorems about the explicit matrix-index
kernel and the actual normalized Haar integrals. They do not redefine an
independently specified spherical coefficient to be this kernel. The remaining
representation-theoretic identification and parameter-continuation questions
are stated separately in the bridge report.
