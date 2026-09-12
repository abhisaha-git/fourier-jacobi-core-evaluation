# Explicit-kernel Haar-core evaluation and infinite-series theorem, version 1




## Parameters and literal closed expression

Let \(q\in\mathbb R\), \(q>2\), \(t=(\sqrt q)^{-1}\). Let
\(\alpha,\beta,\delta\in\mathbb C\). The evaluation assumes

\[
|\alpha|=|\beta|=1,\qquad
\alpha\ne1,\quad\beta\ne1,\quad\alpha\ne\beta,
\quad\alpha\beta\ne1.
\]

With multiplicities retained, put
\(\mathcal A=(\alpha,\alpha^{-1},\beta,\beta^{-1})\) and

\[
\begin{aligned}
C_q&=1+2q^{-1}+2q^{-2}+2q^{-3}+q^{-4},\\
N_1&=\prod_{z\in\mathcal A}(1-zq^{-1}),\\
N_2&=(1-\alpha\beta q^{-1})(1-\alpha^{-1}\beta q^{-1})
 (1-\alpha\beta^{-1}q^{-1})(1-\alpha^{-1}\beta^{-1}q^{-1}),\\
D_1&=\prod_{z\in\mathcal A}(1-z\delta t),\qquad
D_2=\prod_{z\in\mathcal A}(1-z\delta^{-1}t),\\
E_q(\alpha,\beta,\delta)&=
\frac{\frac{(1+\alpha)^2(1+\beta)^2}{\alpha\beta}
 (1-q^{-1})N_1N_2}{C_qD_1D_2}.
\end{aligned}
\]

This is independently transcribed as `Analysis.paperE`, with separate
definitions of all five factors. `Analysis.paperE_eq_closedCore` identifies
it with `Algebra.closedCore` at \(t=q^{-1/2}\). `PaperDomain.lean` proves
the displayed denominator nonzero on every evaluation locus below. The
theorems do not use totalized division to assign a value to a singular
paper quotient.

## Independent left side and convergence range

`Analysis.masterTerm` is the exact summand (L) in the brief. It uses the
integer entry/minor minima and Cartan indices, not row fractions:

\[
m_{r,T}=\kappa_r(1-t^2)^2\delta^k
t^{3k+2j+2h+3\ell+4b}(TU)^{\ell/2}(TV)^b w_r(j,h,c).
\]

Here \((k,j,h,c)\in\mathbb Z^3\times\mathbb N\), \(r=0,1,2\),
\(\kappa=(1,q(1-q^{-1}),-q)\), and \(r=0\) means central coordinate
zero. The collision weight is zero unless \(c=0\) off the collision
locus and at \(r=0\); otherwise it is
\(p_0=(q-2)/(q-1)\), \(p_c=q^{-c}\) for \(c\ge1\).
The exponents \(\ell/2,b\) are proved nonnegative integers, and their
sum is the actual integer height \(-u\). Integer powers are retained
for the valuation exponents.

`Analysis.latticeCore q α β δ T` is the independent definition

\[
\mathcal L_T=C_q^{-1}\sum_{i=0}^7 A_i
\sum_{r=0}^2\sum_{\mathbb Z^3\times\mathbb N}
m_{r,T}(k,j,h,c;U_i,V_i),
\]

with the brief's exact inherited Weyl weights and monomials.
`Analysis.weightedLatticeTerm` is its single full unordered family,
indexed by `Fin 8 × Fin 3 × LatticeIndex`.

Norm summability is proved whenever

\[
0\le T\le1,\qquad t\le|\delta|\le1,
\qquad Tt<|\delta|.
\]

In particular this covers **every real \(0<T<1\)** on the full closed
annulus \(t\le|\delta|\le1\), and **\(T=1\)** on the interior
\(t<|\delta|\le1\). The Weyl-wall exclusions are needed for the
evaluation of the intended rational kernel; the summability helper itself
only needs the two unitary norm hypotheses.

Every one of the fifty original rows has a genuine infinite `HasSum`
proof, and the partitions and inverse reindexing laws are proved. After
norm summability is established, the full assembly gives

\[
\mathcal L_T=C_q^{-1}\sum_i A_i\sum_{\nu=0}^{49}
\operatorname{regionTerms}(t,\delta,TU_i,TV_i,\nu).
\]

The exact declarations are `summable_norm_weightedLatticeTerm`,
`hasSum_weightedLatticeTerm`, and `latticeCore_eq_dampedRational`.
All names in this report beginning `Analysis` have full prefix
`FourierJacobi.Analysis`.

## Principal theorem and corrected comparison

Under the displayed Satake assumptions and \(t<|\delta|\le1\),
`infinite_lattice_core_evaluation` proves, in one conjunction:

1. norm summability of the full undamped weighted family;
2. `HasSum` of that family to \(E_q(\alpha,\beta,\delta)\);
3. nonvanishing of \(C_qD_1D_2\);
4. `Tendsto` of \(T\mapsto\mathcal L_T\) as real \(T\to1\)
   through \(0<T<1\), to \(E_q\).

The unscaled core evaluation is `latticeCore_eq_paperE`. Its Abel
convergence is `tendsto_latticeCore_undamped`, proved from the actual
summand and a summable majorant, and `tendsto_latticeCore_paperE`.
The filter in Lean is `𝓝[Set.Ioo (0 : ℝ) 1] 1`.

`corrected_principal_lattice_comparison` then proves both

\[
\frac2{q+1}\mathcal L_1=\frac2{q+1}E_q
\quad\text{and}\quad
\lim_{T\uparrow1}\frac2{q+1}\mathcal L_T=\frac2{q+1}E_q.
\]

Thus the complete **series analogue** of the corrected comparison
RHS(77) = \([2/(q+1)]\) RHS(184) is proved. In particular the paper's
principal range \(|\delta|=1\) is covered. The Haar version below completes
the integral-to-series bridge. Literal identification with the source's
spherical-coefficient core still requires the Stage C bridge.

## Special theorem and endpoint restrictions

Let \(\varepsilon\in\{1,-1\}\), \(\delta=\varepsilon t\), and
retain the four generic Satake exclusions above. Require additionally
\(\alpha,\beta\ne\varepsilon\), precisely the regular locus of the
literal special quotient.

`infinite_lattice_special_abel` proves, in one conjunction:

1. for every real \(T\in(0,1)\), norm summability of the full weighted
   family and `HasSum` to its independent \(\mathcal L_T\);
2. nonvanishing of the literal \(C_qD_1D_2\) at
   \(\delta=\varepsilon t\);
3. the whole signed-product limit

\[
\lim_{T\uparrow1}\frac{1-\varepsilon}{q+1}\mathcal L_T
=\frac{1-\varepsilon}{q+1}E_q(\alpha,\beta,\varepsilon q^{-1/2}).
\]

The limit alone is `corrected_special_lattice_comparison`.
`tendsto_lattice_special_negative` treats \(\varepsilon=-1\).
`tendsto_lattice_special_positive` proves the identically zero product
for \(\varepsilon=1\) directly, without assumptions on an undamped
endpoint value. No theorem here asserts ordinary endpoint-series
convergence. There is no extra special normalization factor.

This is the full **series analogue** of RHS(80) = RHS(191), on the
stated regular locus. No extension through Weyl walls or through
\(\alpha=-1\), \(\beta=-1\) in the negative special case is claimed.
The principal interior theorem does allow \(\alpha=-1\) or
\(\beta=-1\) whenever the four stated generic exclusions hold.

## Actual local-field left side and strongest theorem

Let F be a field with a valuation relation and its nonarchimedean local-field
topology, with its Borel measurable structure. In Lean these are exactly
`[Field F] [ValuativeRel F] [TopologicalSpace F]`
`[IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]`.
Put q equal to its actual residue cardinality and assume q>2. Choose a
uniformizer \(\varpi\in F^\times\) with canonical additive valuation
\(v(\varpi)=1\). This is the only additional element hypothesis in the
Haar theorems; existence of a canonical uniformizer is proved separately.
No characteristic-zero assumption, abstract shell-volume assumption,
integrability assumption, or spherical-coefficient estimate is used.

Use actual additive Haar \(\mu\), normalized by \(\mu(\mathcal O_F)=1\),
and actual multiplicative Haar \(\nu\), normalized by
\(\nu(\mathcal O_F^\times)=S=1-q^{-1}\). For \(a\ne0\), define

\[
g(a;x,y,z)=
\begin{pmatrix}1&0&y&z\\0&a&ax&ay\\0&0&a^{-1}&0\\0&0&0&1\end{pmatrix}.
\]

Let u be the minimum of the valuations of its sixteen entries, and s the
minimum over all two-by-two minors. Both minima are proved finite, including
when individual entries or minors vanish. Set
\(n=u-s\), \(\ell=2n\), \(b=s-2u\), \(H=n+b=-u\).
The ordering \(2u\le s\le u\le0\) and measurability are proved.
Define the explicit kernel independently of every integral by

\[
\Psi_{\alpha,\beta}(g)=\frac1{C_q}\sum_{i=0}^7
 A_i t^{6n+4b}U_i^nV_i^b.
\]

For clarity, the exact eight Weyl terms are specified by the following table.
Let \(R(z)=(1-t^2z)/(1-z)\); each \(A_i\) is the product of R over the
four entries in its row. This is `Algebra.weylWeights`, with
`Algebra.weylU` and `Algebra.weylV`.

| i | Four arguments of R | U_i | V_i |
|---|---|---|---|
| 0 | β/α, β⁻¹, (αβ)⁻¹, α⁻¹ | αβ | α |
| 1 | α/β, α⁻¹, (αβ)⁻¹, β⁻¹ | αβ | β |
| 2 | (αβ)⁻¹, β, β/α, α⁻¹ | α/β | α |
| 3 | αβ, α⁻¹, β/α, β | α/β | β⁻¹ |
| 4 | (αβ)⁻¹, α, α/β, β⁻¹ | β/α | β |
| 5 | αβ, β⁻¹, α/β, α | β/α | α⁻¹ |
| 6 | β/α, α, αβ, β | (αβ)⁻¹ | β⁻¹ |
| 7 | α/β, β, αβ, α | (αβ)⁻¹ | α⁻¹ |

Take \(z_0=0\), \(z_1=\varpi^{-1}\), \(z_2=\varpi^{-2}\), and
\(a_0=S^{-1}\), \(a_1=q\), \(a_2=-q/S\). Define actual Haar integrals

\[
J_{r,T}=a_r\int_{F^\times\times F\times F}
\delta^{v(a)}\big(q^{-v(a)}\big)^{3/2}T^{H(g)}
\Psi_{\alpha,\beta}(g(a;x,y,z_r))\,d\nu(a)\,d\mu(x)\,d\mu(y),
\qquad \mathcal J_T=\sum_{r=0}^2J_{r,T}.
\]

The real power \((q^{-v(a)})^{3/2}\) is literal in the Lean integrand.
Its equality to \(t^{3v(a)}\) is proved, retaining all integer valuations.
The definitions are `explicitCoreIntegrand`, `explicitHaarCoreShell`, and
`paperExplicitHaarCore`; the latter supplies both actual normalized measures
and the actual residue cardinality. It is not defined using \(\mathcal L_T\).

`paperExplicitHaarCore_eq_latticeCore` proves
\(\mathcal J_T=\mathcal L_T\) for
\(0<T\le1\), \(t\le|\delta|\le1\), \(Tt<|\delta|\).
`explicitCoreIntegrand_integrable` proves ordinary integrability of each of
the three unprefactored integrands in this range. The main regular-locus
evaluation keeps the four Satake exclusions stated above; broader helpers
about the literal totalized Weyl expression are not wall-continuation claims.

On the principal interior, `explicit_haar_core_evaluation` proves:

1. ordinary integrability of every undamped integrand;
2. the unscaled identity \(\mathcal J_1=E_q\);
3. the nonvanishing of \(C_qD_1D_2\);
4. \(\mathcal J_T\to E_q\) through real \(0<T<1\).

`corrected_principal_haar_comparison` proves

\[
\frac2{q+1}\mathcal J_1=\frac2{q+1}E_q,
\qquad \lim_{T\uparrow1}\frac2{q+1}\mathcal J_T=\frac2{q+1}E_q.
\]

At \(\delta=\varepsilon t\), under the same generic assumptions and
\(\alpha,\beta\ne\varepsilon\), `explicit_haar_special_abel` proves
integrability of each actual integrand for every real \(0<T<1\), the
nonvanishing of the literal endpoint denominator, and

\[
\lim_{T\uparrow1}\frac{1-\varepsilon}{q+1}\mathcal J_T
=\frac{1-\varepsilon}{q+1}E_q(\alpha,\beta,\varepsilon t).
\]

The limit declaration is `corrected_special_haar_comparison`.
`tendsto_haar_special_positive` proves the zero-product limit directly;
`tendsto_haar_special_negative` uses equality with the genuinely convergent
damped series before taking its regular rational limit. No undamped endpoint
integrability or endpoint sum is asserted. The additional elementary
denominators q, q+1, q−1, q−2 and αβ are proved nonzero in
`core_scalar_denominators_ne_zero` from the natural hypotheses.

Thus both requested comparisons are obtained **at explicit-kernel Haar scope**.
The symbol \(\Phi_0\) for the paper's independently normalized spherical
coefficient is not identified with \(\Psi\) by this development. The full
source spherical-coefficient goal is therefore still incomplete, exactly at
the Stage C boundary described in the bridge report.

## Inherited results and new progress

The finite fifty-row/eight-Weyl-term evaluation, the integer Cartan
tables, four I0 row sums (cases 1,2,6,7), and v2 local-field results are
inherited and have been rechecked. They are not new achievements here.

New work completes the other 46 infinite rows; proves all required full
lattice/depth partitions, parity bijections, and norm summability;
defines and assembles the independent master family; proves its
unscaled evaluation and both corrected series comparisons; and checks
the exact closed expression and natural denominator conditions.
Further new work proves all integer additive and multiplicative Haar shell
measures, actual joint collision-depth masses, measurable intrinsic matrix
indices, the explicit kernel and its bound, the countable almost-everywhere
partition, constant values on its cells, ordinary integrability and all
integral/sum interchanges. It completes the actual Haar evaluation and both
corrected Haar comparisons. No new representation-theoretic identification
or extension through the excluded special/Weyl parameters is claimed.
