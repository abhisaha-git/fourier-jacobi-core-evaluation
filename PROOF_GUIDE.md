# Guide to the infinite-series and actual Haar proofs

Start with [the exact statement](docs/statement.md), then
[HaarLimits.lean](FourierJacobi/Analysis/HaarLimits.lean). Its main declarations,
all in `FourierJacobi.Analysis`, are:

| Declaration | Conclusion |
|---|---|
| `explicit_haar_core_evaluation` | Three ordinary integrands are integrable in the undamped interior; the unscaled Haar core is \(E_q\); its literal denominator is nonzero; the damped core tends to \(E_q\) |
| `explicit_haar_special_abel` | Every special damped integrand is integrable and the whole signed product has the prescribed Abel limit |
| `corrected_principal_haar_comparison` | The required \(2/(q+1)\) multiplies both the core and \(E_q\) |
| `corrected_special_haar_comparison` | The signed special comparison has no additional factor |

## Independent definitions

[MasterSeries.lean](FourierJacobi/Analysis/MasterSeries.lean) defines
`masterTerm` directly from the existing integer entry/minor minima.
The central index zero means \(z=0\). At zero and off collision, only \(c=0\)
contributes. On collision \(2h=j-r\), the weight is
\((q-2)/(q-1)\) at depth zero and \(q^{-c}\) at positive depth.
The central coefficients are \(1,q(1-q^{-1}),-q\). No restored-row factor is
applied a second time.

The kernel definition follows a separate path.
[KernelIndices.lean](FourierJacobi/Valuations/KernelIndices.lean) takes the actual
entry and two-by-two-minor valuation minima \(u,s\) of the concrete matrices.
Their proved ordering \(2u\le s\le u\le0\) gives nonnegative
\(n=u-s\), \(b=s-2u\), \(\ell=2n\), and \(H=n+b=-u\).
These indices are finite and measurable even at points later removed as null.
[ExplicitKernel.lean](FourierJacobi/Analysis/ExplicitKernel.lean) defines the
finite Weyl formula from those actual indices and proves the pointwise bound
\[
 |\Psi|\le\frac{\sum_i|A_i|}{C_q}\,q^{-3\ell/2-2b}.
\]

[HaarKernel.lean](FourierJacobi/Analysis/HaarKernel.lean) independently defines
the actual integrands and the three integrals. Its `paperExplicitHaarCore`
uses the actual residue cardinality and normalized Haar measures. It is not
defined by the lattice sum or by \(E_q\).

## Complete infinite series

The I0, I1, and I2 developments prove the ten, fifteen, and twenty-five actual
row sums, including depth and parity cases. Their bijections have both inverse
laws proved in Lean. Four I0 infinite proofs and the finite fifty-row/eight-Weyl
calculation come from v2; the other 46 infinite row proofs and their complete
assembly are new.

[LatticeCore.lean](FourierJacobi/Analysis/LatticeCore.lean) proves norm
summability of the full family before rearrangement, then identifies its
independent sum with
\[
 C_q^{-1}\sum_i A_i\sum_{\nu=0}^{49}r_\nu(t,\delta,TU_i,TV_i).
\]
Damping remains in each unsummed monomial. At \(T=1\) in the interior, the
inherited finite-core theorem and the independently matched `paperE`
give the unscaled value.

[MasterDamping.lean](FourierJacobi/Analysis/MasterDamping.lean) proves the
actual summand relation \(H_T=T^H H_1\), with \(H\ge0\). Its summable undamped
norm dominates the interior damped family. This gives Abel convergence of the
actual series by dominated convergence, before any principal prefactor is used.

## Actual Haar-to-lattice identity

The measure modules prove integer additive-shell measures and the source
multiplicative normalization. Write \(s_q=1-q^{-1}\).
The actual lattice cell at \((k,j,h,c)\) has measure
\[
 s_q^3q^{-j-h}\omega_r(j,h,c).
\]
This is proved from actual shell scaling and the transported joint collision
distribution; it is not assumed.

[HaarLatticePartition.lean](FourierJacobi/Analysis/HaarLatticePartition.lean)
defines these cells by actual field valuations. They are measurable, disjoint,
and exhaustive outside the proved Haar-null coordinate/determinant set.
[KernelShells.lean](FourierJacobi/Valuations/KernelShells.lean) gives the exact
integer kernel indices on each cell.

`HaarCellMass`, `HaarCellValue`, and `HaarCellMaster` prove that cell measure
times integrand value and the source prefactor is exactly the master summand.
The prefactors are
\[
 a_0=s_q^{-1},\qquad a_1=q,\qquad a_2=-q/s_q,
\]
so \(a_rs_q^3=\kappa_rs_q^2\). This explains the normalization without an
extra restoration.

[FiberIntegration.lean](FourierJacobi/Analysis/FiberIntegration.lean) proves a
general integration theorem for disjoint measurable countable cells with
proved finite measures and a summable weighted norm.
[HaarCoreAssembly.lean](FourierJacobi/Analysis/HaarCoreAssembly.lean) discharges
all its hypotheses using the actual cells and the complete lattice majorant.
It proves ordinary integrability of all three integrands and
\[
                         J_T=\mathcal L_T.
\]
Integrability is a conclusion, not a bridge hypothesis.

## Principal and special limits

[HaarLimits.lean](FourierJacobi/Analysis/HaarLimits.lean) transfers the proved
series results through the actual Haar identity. The undamped principal core
is evaluated first; only then is \(2/(q+1)\) applied.

At \(\delta=-t\), every damped sum is identified before taking the one-sided
rational limit on the regular endpoint locus. A nonzero modulus-one geometric
denominator is never used to infer ordinary endpoint convergence.
At \(\delta=t\), the signed product is identically zero. No undamped endpoint
integral is required or asserted.

The source spherical-coefficient identification and wall extensions remain
unproved; see [NEXT_STEPS.md](NEXT_STEPS.md) and [the bridge report](docs/bridge.md).
For current build/audit evidence and matching hashes, use
[VERIFICATION.md](VERIFICATION.md). The full local build and exhaustive audit
passed; no hosted CI run is claimed.

