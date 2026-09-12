# Independent review of the explicit Haar path, v1

This review concerns the new publication `publications/fourier-jacobi-core-evaluation`, read on 11 September 2026. It compares the actual local-field definitions and the cell-to-master bridge with sections 4–5 of `equations_77_80_formalization_brief_v1.md` and the current `section_2_expanded_complete.tex`, especially (67), `exp:haar-shells`, `expanded:null`, `expanded:collision`, `unramlemma1eq2`, `unramlemma1eq3`, and `expanded:master-row`. It is a source and hypothesis review, not a replacement for the publication's final Lake build, axiom audit, and source hashes.

**Finding:** no concealed integral-to-series assumption or discrepancy with the requested explicit-kernel Haar object was found in the reviewed chain. The actual shell measures, cancellation distribution, index extraction, cell constancy, normalization, ordinary integrability, and integral-to-series identity are proved from local-field objects and the independently norm-summable master family. The final countable integration assembly has also been reviewed. These results concern the explicit kernel in section 5 of the brief; they do not yet identify it with the independently defined spherical coefficient of the paper.

## Definitions and dependency order

The primary reviewed files are `Valuations/KernelIndices.lean`, `Valuations/KernelShells.lean`, `Analysis/ExplicitKernel.lean`, `Analysis/HaarKernel.lean`, `Analysis/HaarLatticePartition.lean`, `Analysis/HaarCellMass.lean`, `Analysis/HaarCellValue.lean`, `Analysis/HaarCellMaster.lean`, `Analysis/FiberIntegration.lean`, `Analysis/CentralWeylSeries.lean`, `Analysis/HaarCoreAssembly.lean`, and the current `Analysis/HaarLimits.lean`. The review also inspected their relevant foundations in `Algebra/Matrices.lean`, `Valuations/LocalMatrix.lean`, `Measure/NullSets.lean`, `Measure/LocalHaar.lean`, `Measure/IntegerShells.lean`, `Measure/MultiplicativeHaar.lean`, `Measure/PaperMultiplicativeHaar.lean`, `Measure/ShellCollision.lean`, and `Measure/JointCollision.lean`.

| Step | Actual object or proved property | Main declarations |
| --- | --- | --- |
| Matrix | The exact source matrix `diag(1,a,a⁻¹,1) N(x,y,z)`, with all increasing-pair two-by-two minors | `LocalMatrix.g`, `LocalMatrix.secondCompound`, `LocalMatrix.all_two_by_two_minors` |
| Finite intrinsic indices | Entry and minor minima, finite because the multiplicative coordinate is a field unit; `2u ≤ s ≤ u ≤ 0` | `Valuations.actualEntryInteger`, `actualMinorInteger`, `actualInteger_bounds` |
| Cartan-shaped indices | `n=u-s`, `b=s-2u`, `ell=2n`, `H=n+b=-u`, with nonnegativity and measurability | `kernel_indices_nonnegative`, `kernel_height_eq`, `kernel_half_ell`, the `kernel…_measurable` declarations |
| Explicit kernel | The finite Weyl formula evaluated at these actual indices | `Analysis.weylKernelAtIndices`, `explicitWeylKernel`, `explicitWeylKernel_formula` |
| Actual integrand | `δ^v(a) (q^-v(a))^(3/2) T^H Ψ(g)` with a literal real power | `explicitCoreIntegrand`, `explicitCoreIntegrand_measurable` |
| Actual cells | Exact finite coordinate valuations and, only on a collision locus, exact finite cancellation depth | `haarLatticeCell`, `haarLatticeCell_disjoint`, `haarLatticeCell_measurableSet`, `haarLatticeCell_exhaustive_ae` |
| Cell coordinates | Actual matrix indices agree with the integer minima used by the independent master summand | `haarLatticeCell_kernelCoordinates` |
| Actual cell mass | The source-normalized product Haar measure of each cell | `haarLatticeCell_measure_ne_top`, `haarLatticeCell_real_mass`, `haarLatticeCell_complex_mass` |
| Cell value | The independently defined integrand is constant on that cell | `explicitCoreIntegrand_eq_haarCellValue` |
| Normalized cell bridge | Prefactor times actual cell mass times actual cell value equals the finite Weyl combination of master terms | `haarLatticeCell_prefactor_value` |
| Ordinary integration | Norm summability of the actual cell values implies integrability of each prefactored and unprefactored integrand | `integrable_hasSum_of_countable_fibers`, `integrable_prefactor_core_eq_centralLatticeCore`, `explicitCoreIntegrand_integrable` |
| Actual Haar sum | The sum of the three actual integrals equals the independently defined infinite master series | `explicitHaarCoreShell_eq_centralLatticeCore`, `paperExplicitHaarCore_eq_latticeCore` |

`KernelShellCoordinates` is a conjunction of index equalities, rather than a structure which supplies an integral identity. Its equalities are proved in `KernelShells` from actual entry/minor calculations and then discharged from actual cell membership in `HaarLatticePartition`. None remains as an assumed bridge in `explicitCoreIntegrand_eq_haarCellValue` or `haarLatticeCell_prefactor_value`.

The use of integer `untop` is justified by a proof of finiteness. Zero additive coordinates and a zero determinant are not assigned fictitious finite valuations. Nonnegativity is proved by integer inequalities; it is not enforced by truncating negative differences. The conversion of a finite cancellation depth to a natural number in the exhaustion proof occurs only after its nonnegativity has been proved.

## Haar normalization and all integer shells

Write `q = residueCardinality K` and `S = 1-q⁻¹`. The cardinality is `Nat.card` of the field's actual residue field, not an arbitrary prime parameter supplied alongside the field. `additiveHaar` is the actual Haar construction normalized on the compact open valuation ring. The proof of its nonnegative ball volumes uses the finite additive index of powers of the actual maximal ideal. `IntegerShells` then obtains every integer ball volume, including negative valuations, from the multiplicative scaling character of Haar measure and an actual uniformizer of valuation one.

Consequently the proved normalizations are

\[
 \mu\{v(x)\ge j\}=q^{-j},\qquad
 \mu\{v(x)=j\}=S q^{-j}\quad(j\in\mathbb Z).
\]

`multiplicativeHaar` is initially normalized to give the actual subgroup of valuation-ring units volume one. `paperMultiplicativeHaar` scales this measure by `S` exactly once. Its integer shells are proved to be multiplicative translates of that subgroup, and each has volume `S`. The positive finite normalization and sigma-finiteness are derived, not assumed as desired shell formulas.

`paperCoreMeasure` is the actual product

\[
 \nu\otimes(\mu\otimes\mu)
 \quad\text{on }K^\times\times(K\times K),
\]

with the additive coordinates in the order `(x,y)`. This agrees with the product-measure formulation of the requested three integrals. Once ordinary integrability is proved, the corresponding iterated-integral descriptions follow by Fubini; the definitions do not silently rely on such a use before integrability.

## Collision probability and the null set

On `2h=j-r` with `r>0`, the cell depth is exactly

\[
 c=v\!\left(\frac{y^2}{xz}-1\right),\qquad v(z)=-r.
\]

`JointCollision` transports the distribution to actual shells by fixing `y,z` and using the center `y²/z`, whose valuation is `j`. The identity

\[
 y^2-xz=(-z)(x-y^2/z)
\]

reduces the positive-depth sections to translated additive balls and shells. At depth zero the proof subtracts the first tail from the entire shell. The resulting conditional masses are exactly

\[
 p_0=\frac{q-2}{q-1},\qquad p_c=q^{-c}\ (c\ge1).
\]

The joint measure calculation uses measurable sections and the nonnegative product-measure integration theorem. It does not assume integrability of the later complex kernel. It also does not assume that squaring is measure preserving or bijective on the unit group: `y` is fixed while the `x` sections are computed. Thus there is no missing square-root or parity factor in this transport.

Off the collision locus, and for `r=0`, the cells with `c>0` are empty. Only `c=0` contributes. The exact-cancellation point has no additional infinite-depth mass. The disjoint cells cover the complement of `x=0`, `y=0`, and `y²-xz=0`; the latter set is proved null, including `z=0`. Atomlessness of actual local-field Haar measure is derived from the non-isolation of zero. The product null-set result also covers an unbounded multiplicative coordinate. Accordingly the final assembly must use the proved almost-everywhere exhaustion, not assert pointwise exhaustion of the full field product.

The real cell mass is therefore

\[
 \mu_{\rm core}(C_{r,k,j,h,c})
   =S^3 q^{-j-h}\omega_r(j,h,c).
\]

Finiteness is separately proved before converting the native extended-nonnegative-real measure to its real value. This excludes an erroneous use of the totalized `toReal` of infinite measure.

## Cell value and exact source prefactors

The independently defined cell value uses the same actual integer minima as the master summand. The proof of constancy only uses the coordinate and matrix-index equalities established above. For every integer `k` and positive real `q`, `haar_scale_rpow` proves

\[
 (q^{-k})^{3/2}=t^{3k},\qquad t=q^{-1/2},
\]

with the left side a real power and the right side an integer power. The additive shell factors are similarly converted by `haar_shell_zpow_coe`. No integer valuation is silently replaced by a natural exponent. The literal absolute value agrees with the brief's normalization `|a|=q^{-v(a)}`.

`coreCentral` uses `z=0` at `r=0`, then `π⁻¹` and `π⁻²`; it does not treat `r=0` as a central unit of valuation zero. `centralRepresentative_coreCentral` derives their valuations from the standard hypothesis `v(π)=1` on an actual field unit.

The prefactors in `coreIntegralPrefactor` are precisely

\[
 a_0=S^{-1},\qquad a_1=q,\qquad a_2=-q/S.
\]

`coreIntegralPrefactor_mul_shell_volume` proves

\[
 a_r S^3=\kappa_r S^2,
 \qquad (\kappa_0,\kappa_1,\kappa_2)=(1,qS,-q).
\]

Combining this with the cell mass, the real-power conversion, `C_q = poincare(t)`, and the explicit kernel gives exactly

\[
 a_r\mu_{\rm core}(C_{r,k,j,h,c})\,
       \operatorname{value}(C_{r,k,j,h,c})
 =\sum_{i=0}^{7}\frac{A_i}{C_q}
   \kappa_r S^2\delta^k
   t^{3k+2j+2h+3\ell+4b}
   (TU_i)^{\ell/2}(TV_i)^b\omega_r(j,h,c).
\]

This is the independent master term from the brief. Damping enters its unsummed monomial using `H=ell/2+b`; it is not inserted into the simplified closed formula. The restored row quantities `E₀=SI₀`, `E₁=-q⁻¹I₁`, and `E₂=SI₂` do not enter this bridge, so no second restoration is applied. The checked finite row fractions remain the actual `I_r` contributions used by the independent infinite-series theorem.

## Hypotheses, totalization, and scope boundaries

The actual Haar and cell calculations require a nonarchimedean local field in mathlib's sense, its compatible Borel measurable structure, and the source-normalized measures just constructed. Its residue cardinality automatically satisfies `q>1`. An actual uniformizer is a field unit satisfying `v(π)=1`. These are standard object and normalization hypotheses, not mathematical conclusions about the core.

The source assumes characteristic zero and odd residue characteristic. The reviewed cell and explicit-kernel arguments do not need those extra restrictions. The current complete series theorem uses `q>2`, which contains every source residue cardinality. Some I2 helpers use `q-2≠0`; this follows from that natural arithmetic hypothesis. The current evaluation does not thereby cover `q=2`. Its broader local-field formulation may include other fields with residue cardinality greater than two, but does not prove a broader representation-theoretic assertion in even residue characteristic.

The scalar cell bridge assumes only `q>1` and `T≠0`, beyond the standard field data, because it is an algebraic identity for the explicitly written finite Weyl expression. The intended analytic evaluation must additionally retain unitary Satake parameters, the regular Weyl assumptions `α≠1`, `β≠1`, `α≠β`, `αβ≠1`, and the stated ranges of `δ,T`. At the literal special endpoint it must retain `α,β≠ε`. The broad cell identity at excluded parameters is a statement about Lean's written rational expression; it is not a continuity theorem or an interpretation of totalized division as a spherical coefficient.

The finite kernel norm estimate in `explicitWeylKernel_q_norm_le` is proved by the triangle inequality and the unit norm of the Weyl monomials. It has the required form

\[
 |\Psi(g)|\le\frac{\sum_i|A_i|}{C_q}\,q^{-3\ell/2-2b}.
\]

No representation-theoretic coefficient bound is assumed. The countable integration assembly uses the already proved norm summability of the individual actual master families and the exact cell bridge. It derives integrability of each shell integrand before using its Bochner integral as an ordinary integral. It does not rely on cancellation of signed shell sums.

More precisely, `CentralWeylSeries.summable_central_norm_majorant` is obtained by restricting the full proved norm-summable family to one central index and then taking the finite sum of its eight Weyl norms. `HaarCoreAssembly` bounds

\[
 \mu_{\rm core}(C_i)\,|a_r\operatorname{value}(C_i)|
 =\left|\sum_w\operatorname{weightedMasterTerm}_{w,r,i}\right|
 \le\sum_w|\operatorname{weightedMasterTerm}_{w,r,i}|.
\]

The first equality uses a nonnegative finite real cell measure, not the sign of a shell prefactor. `FiberIntegration` applies the pinned library's integration results to the finite-measure disjoint measurable cells: their constant values are integrable on each cell, the sum of their norm integrals is summable, and the almost-everywhere cover transfers integrability to the whole product. Its general hypotheses are explicitly discharged in the actual Haar theorem. Uniqueness of `HasSum` identifies the integral with `centralLatticeCore`. The nonzero source prefactor, proved from `q>1`, then gives the unprefactored integrability assertion. The sum over the three central indices is finite and is grouped using `centralLatticeCore_sum`.

The assembly's analytic assumptions are exactly `q>2`, unitary `α,β`, `0<T≤1`, `t≤|δ|≤1`, and `Tt<|δ|`, with `v(π)=1`. In the damped open interval the last inequality follows from `T<1` and `t≤|δ|`; at `T=1` it is precisely the strict interior condition `t<|δ|`. No integrability, norm summability, row equality, or limit is supplied as a hypothesis of `paperExplicitHaarCore_eq_latticeCore`.

The target at `δ=εt` is the limit of the whole signed product for real `T→1` within `(0,1)`. A nonzero rational denominator at `T=1` is not proof of convergence of an undamped geometric series there. `HaarLimits` respects this distinction: its negative special proof transfers the already proved lattice Abel limit using equality with actual Haar integrals only for `0<T<1`. For `ε=1`, `tendsto_haar_special_positive` is the direct identically-zero-product limit. `explicit_haar_special_abel` also proves that every damped integral used in that product is integrable, and proves regularity of the literal endpoint quotient under `α,β≠ε`. Neither its hypotheses nor its conclusions assert an ordinary undamped endpoint integral.

For the principal target, `paperExplicitHaarCore_eq_paperE` first evaluates the actual unscaled Haar core. `tendsto_paperExplicitHaarCore_paperE` proves its Abel convergence. Only afterward does `corrected_principal_haar_comparison` multiply both by `2/(q+1)`. `corrected_special_haar_comparison` retains `(1-ε)/(q+1)` inside the limit and adds no further normalization. This matches the corrected comparison of RHS(77) with `2/(q+1)` times RHS(184), and of RHS(80) with RHS(191), at the explicit-kernel Haar scope.

Finally, `paperExplicitHaarCore` is the sum of the three independently defined explicit-kernel integrals. It is not defined to be a finite row sum or the closed value. Its proved equality with the independent master series completes a substantive Stage B bridge. To call it the paper's spherical-coefficient core still requires identification of the independently defined normalized spherical coefficient with this Weyl kernel, through the actual Cartan/Macdonald argument. To call it the original stabilized central truncation additionally requires the relevant fixed-cutoff integrability and central-shell cancellation argument. Neither bridge is an assumption hidden in the reviewed theorems. No unresolved flaw in their supplied mathematical proof was found; those larger identifications are distinct mathematical obligations.

## Verification boundary of this review

`HaarCellValue.lean` and `HaarCellMaster.lean` were individually checked and exported with the pinned toolchain and `-DwarningAsError=true`; their current development logs are `build/fourier-jacobi-core-evaluation/haar-cell-value-development.txt` and `haar-cell-master-development.txt`. The collaborating authors reported successful strict checks of the imported new partition and mass modules, `FiberIntegration.lean`, `HaarCoreAssembly.lean`, and `HaarLimits.lean`. The last direct check returned exit code zero and an empty `build/fourier-jacobi-core-evaluation/haar-limits-development.txt`; thus the Stage B principal and whole signed special theorems have passed their direct checks. This report did not edit Lean files or rerun the full publication build. The publication's final current-source Lake build, exhaustive axiom audit, hypothesis review, and source hashes remain the controlling verification record. No hosted CI execution is claimed here.
