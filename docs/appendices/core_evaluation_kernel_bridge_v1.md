# Actual-matrix kernel and lattice-partition bridge, v1

This report records five new modules in
`publications/fourier-jacobi-core-evaluation`. Their scope is the actual
local-field kernel, its bound and measurability, and its valuation-and-cancellation
partition. These modules do not themselves assert integrability or an
integral-to-series identity. Later assembly modules may discharge those
obligations; the publication's final status describes the integrated result.

## Precise mathematical statement

Let \(K\) be a nonarchimedean local field with its canonical normalized integer
valuation \(v\). For every \(a\in K^\times\) and \(x,y,z\in K\), let \(u\) be the
minimum valuation of the actual entries of the source matrix \(g(a;x,y,z)\),
and \(s\) the minimum valuation of its actual two-by-two minors. These minima
are finite, including when a coordinate or \(y^2-xz\) vanishes, and

\[
                       2u\le s\le u\le0.
\]

Thus \(n=u-s\), \(b=s-2u\), \(\ell=2n\), and \(H=n+b=-u\) are nonnegative
integers. Every one of these actual integer indices is Borel measurable on
\(K^\times\times K\times K\times K\).

With the exact existing eight Weyl weights and monomials, define independently

\[
 \Psi_{\alpha,\beta}(a;x,y,z)
 =C_q^{-1}\sum_{i\in\mathrm{Fin}\,8}
      A_i t^{3\ell+4b}U_i^{\ell/2}V_i^b,
 \qquad t=q^{-1/2}.
\]

For real \(q>1\) and unitary Satake parameters on the regular Weyl locus, this
is measurable and satisfies

\[
 |\Psi_{\alpha,\beta}(a;x,y,z)|
 \le \frac{\sum_i|A_i|}{C_q}\,q^{-3n-2b}
 =\frac{\sum_i|A_i|}{C_q}\,q^{-3\ell/2-2b}.
\]

For \(T\ne0\), its damping is exactly

\[
 T^H\Psi=C_q^{-1}\sum_i A_i t^{3\ell+4b}(TU_i)^n(TV_i)^b.
\]

All powers with integer valuation exponents remain integer powers. The regular
Weyl locus is \(\alpha\ne1\), \(\beta\ne1\), \(\alpha\ne\beta\), and
\(\alpha\beta\ne1\). The finite norm inequality is algebraically valid beyond
that locus in Lean's total field operations; no claim is made that totalized
rational weights there represent the intended kernel.

The actual functions \(|a|=q^{-v(a)}\) and
\(\delta^{v(a)}|a|^{3/2}T^H\Psi\) are independently defined; the latter is
measurable. Three actual Bochner integrals are defined with central coordinates
\(0,\varpi^{-1},\varpi^{-2}\) and prefactors

\[
 (1-q^{-1})^{-1},\qquad q,\qquad -q/(1-q^{-1}).
\]

The general definitions take explicit measures. The wrapper
`paperExplicitHaarCore` supplies the actual residue cardinality, the actual
`additiveHaar` of unit-ball mass one, and `paperMultiplicativeHaar`, whose
multiplicative valuation shells have mass \(1-q^{-1}\). The standard measurable
structure on field units is proved Borel; this adds no measurability hypothesis.
For the source central representatives, the uniformizer unit must have actual
valuation one. No integrability or evaluation is assumed by these definitions.

The actual lattice cell at \((k,j,h,c)\in\mathbb Z^3\times\mathbb N\) consists of
the points with \(v(a)=k\), \(v(x)=j\), and \(v(y)=h\), and with:

- \(c=0\) if \(r=0\) or \(2h\ne j-r\);
- \(v(y^2/(xz)-1)=c\) otherwise.

Here \(r=0\) means \(z=0\); for \(r\ne0\), the actual central coordinate has
valuation \(-r\). These cells are measurable and pairwise disjoint. Outside
\(x=0\), \(y=0\), or \(y^2-xz=0\), every point lies in exactly one cell. They
therefore form an almost-everywhere exhaustive partition for every additive
Haar measure and every measure on the multiplicative coordinate. On each cell,
all intrinsic entry, minor, \(\ell,n,b,H\) indices equal the integer master data.

## Human proof and dependency order

1. **Actual minima and finiteness.** The inherited `MatrixBridge` computation
   gives the entry list
   \(\min(0,v(a),v(a^{-1}),v(ax),v(y),v(ay),v(z))\).
   The minor list contains the same entries except \(v(z)\), together with
   \(v(az),v(z/a),v(a(y^2-xz))\). Both contain \(0\), hence are finite and
   nonpositive. Integer extraction uses these finiteness proofs; zero is
   never assigned a finite valuation.

2. **The ordering.** The inherited lower bound \(2u\le s\) follows because
   every determinant term is a product of two entries and valuation is
   ultrametric. For the new upper bound \(s\le u\), only \(v(z)\) is absent
   from the minor list. Writing \(k=v(a)\), if \(k\le0\) then
   \(v(az)=k+v(z)\le v(z)\); if \(k\ge0\), then
   \(v(z/a)=v(z)-k\le v(z)\). Thus \(s\le v(z)\) too. The argument is valid
   at \(z=0\), using extended valuations.

3. **Exponents and height.** The inequalities give \(n=u-s\ge0\) and
   \(b=s-2u\ge0\). Integer arithmetic gives \(\ell=2n\),
   \(\ell/2=n\), and \(H=n+b=-u\ge0\).

4. **Measurability.** The new `IntegerShells` theorem proves canonical
   valuation measurability from the actual integer shells and \(\{0\}\).
   The local field has a compatible rank-one norm and is proper; the needed
   second countability is derived, not assumed. Field expressions and their
   valuation minima are measurable. Measurable finite-value extraction gives
   \(u,s\), and integer arithmetic gives the remaining indices. Their exact
   integer fibers form a countable measurable partition, with negative-index
   fibers empty.

5. **Kernel and majorant.** The finite Weyl formula is a function of the
   measurable pair \((n,b)\). Every function on the countable discrete set
   \(\mathbb Z^2\) is measurable. The inherited explicit Weyl data give
   \(|U_i|=|V_i|=1\) for unitary parameters. The triangle inequality proves
   the \(t\)-majorant. Positivity of \(C_q\) and
   \((q^{-1/2})^{2e}=q^{-e}\), for integer \(e\), give the \(q\)-majorant.
   The identity \(H=n+b\) puts damping in each unsummed monomial.

6. **Actual Haar integrands.** The valuation of a field unit is finite and
   measurable. The character, real absolute-value power, and damping are
   functions of measurable integer indices. Multiplying these by the
   explicit kernel proves integrand measurability. The unit group's Borel
   structure follows from its topological embedding into the field.

7. **Actual lattice partition.** Nonzero coordinates supply unique \(k,j,h\).
   At \(r=0\) and off collision, take \(c=0\). On collision, determinant
   nonvanishing makes \(y^2/(xz)-1\) nonzero. Its valuation is nonnegative by
   the ultrametric inequality, hence is a natural number \(c\). This proves
   existence; actual valuation equalities and the forced-zero rule give
   uniqueness. The cells are intersections of measurable valuation fibers.
   The actual Haar null-set theorem removes precisely the exceptional locus,
   also with the multiplicative parameter. Finally the inherited actual
   matrix-minimum formulas identify every master index on the cells. No
   cell measure is inferred merely from measurability.

## Exact Lean declarations

In `FourierJacobi.Valuations`, module `Valuations/KernelIndices.lean`:

- `actual_minor_minimum_le_entry`;
- `actualEntryInteger`, `actualMinorInteger`, and their `_coe` theorems;
- `actualInteger_bounds`;
- `kernelEntryIndex`, `kernelMinorIndex`, `kernelN`, `kernelB`,
  `kernelEll`, `kernelHeight`;
- `kernel_indices_nonnegative`, `kernel_height_eq`, `kernel_half_ell`;
- `kernel_indices_of_minima`;
- `kernel_entry_minimum_measurable`, `kernel_minor_minimum_measurable`;
- `kernelEntryIndex_measurable`, `kernelMinorIndex_measurable`,
  `kernelN_measurable`, `kernelB_measurable`, `kernelEll_measurable`,
  `kernelHeight_measurable`.

In `FourierJacobi.Valuations`, module `Valuations/KernelShells.lean`:

- `KernelShellCoordinates`, the conjunction of all seven index equalities;
- `kernelShellCoordinates_of_minima`;
- `kernelShellCoordinates_zero`, `kernelShellCoordinates_nonzero`;
- `kernelShell_nonzero_locus`.

In `FourierJacobi.Analysis`, module `Analysis/ExplicitKernel.lean`:

- `weylKernelAtIndices`, `weylKernelAtIndices_norm_le`,
  `weylKernelAtIndices_damping`;
- `poincare_coe_norm`;
- `explicitWeylKernel`, `explicitWeylKernel_formula`;
- `explicitWeylKernel_norm_le`, `explicitWeylKernel_damping`;
- `explicitWeylKernel_measurable`, `damped_explicitWeylKernel_measurable`.

In `FourierJacobi.Analysis`, module `Analysis/HaarKernel.lean`:

- `inverseSqrt_even_zpow`, `explicitWeylKernel_q_norm_le`;
- `coreScaleExponent`, `coreScaleExponent_coe`,
  `coreScaleExponent_measurable`;
- `coreLocalAbs`, `coreLocalAbs_pos`;
- `coreAtCentral`, `coreAtCentral_measurable`;
- `explicitCoreIntegrand`, `explicitCoreIntegrand_measurable`;
- `coreCentral`, `coreCentral_zero`, `coreCentral_one`, `coreCentral_two`;
- `coreIntegralPrefactor`, `explicitHaarCoreShell`, `explicitHaarCore`;
- `coreUnits_borelSpace`, `paperExplicitHaarCore`;
- `kernelCartanFiber`, `kernelCartanFiber_measurableSet`,
  `kernelCartanFiber_disjoint`, `kernelCartanFiber_exhaustive`,
  `kernelCartanFiber_empty_of_negative`.

In `FourierJacobi.Analysis`, module `Analysis/HaarLatticePartition.lean`:

- `CentralRepresentative`, `centralRepresentative_coreCentral`;
- `haarLatticeCell`, `haarLatticeCell_measurableSet`;
- `haarLatticeCell_disjoint`, `haarLatticeCell_exhaustive`;
- `haarLatticeCell_existsUnique`, `haarLatticeCell_exhaustive_ae`;
- `haarLatticeCell_kernelCoordinates`.

## Obligations beyond these five modules

The following require subsequent results and are not assumed by the five
modules above:

- Compute actual cell masses, including the transported collision distribution.
- Prove integrability from cell masses and the full lattice majorant.
- Justify the countable integral/sum interchange and prove the Haar-to-lattice
  identity, then transfer the principal evaluation and whole signed Abel limit.
- Identify the explicit kernel with the paper's independently defined normalized
  spherical coefficient through the actual Cartan/Macdonald bridge.
- Prove actual-object continuity/majorants or cancellation before extending
  an Abel theorem to excluded Weyl walls or endpoint exceptions.

The human proof supplied here for the actual kernel and partition is complete.
The Haar assembly requires actual measure transport, integrability, and
interchange arguments; it is not being described as merely an unknown library
lemma name.

## Verification record

All five listed modules passed direct checks with Lean
`leanprover/lean4:v4.33.1`, pinned mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and
`-DwarningAsError=true`. Every command activated
`build/fourier-jacobi-core-lean/direct-env.ps1`. Exported oleans were written
only to the workspace build cache outside the publication. No pin or global
installation changed. `KernelIndices.lean` also passed the parent task's
targeted new-publication Lake build. The final integrated Lake build, exhaustive
axiom audit, and source-hash manifest are recorded by the parent task.
No hosted CI run is asserted here.

