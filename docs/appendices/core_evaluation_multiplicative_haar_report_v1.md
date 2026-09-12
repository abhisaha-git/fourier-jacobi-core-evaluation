# Actual multiplicative Haar normalization, version 1

The new module is
`publications/fourier-jacobi-core-evaluation/FourierJacobi/Measure/MultiplicativeHaar.lean`.
It imports the new actual-field integer-shell module. It is a further Stage B
ingredient, not an integral-to-series theorem.

**Source normalization:** the complete mathematical source uses
`d×a(O_K^×)=1-q⁻¹`, with `d×a=|a|⁻¹ da` (source lines 221 and 228).
The measure in this module is an auxiliary unit-normalized Haar measure.
The separate `PaperMultiplicativeHaar.lean` defines
`paperMultiplicativeHaar = ENNReal.ofReal(1-q⁻¹) • multiplicativeHaar`
and is the measure intended for the source's core integrals. Its shell
volumes are `1-q⁻¹`. Using the auxiliary measure directly would lose this
factor and is not the source normalization.

Let `K` be any field with a valuative relation, topology, and mathlib's
`IsNonarchimedeanLocalField K` instance. Equip its actual group of field
units `Kˣ` with a measurable space satisfying `BorelSpace Kˣ`. Set

\[
U=\mathcal O_K^\times\subset K^\times,
\qquad S_n^\times=\{u\in K^\times:v(u)=n\}\quad(n\in\mathbb Z),
\]

where `v=localFieldValuation K` is the independently constructed canonical
valuation. The subgroup `U` is defined as `(𝒪[K]).toSubmonoid.units`;
it is not specified by an abstract normalization axiom.

The new declarations in namespace `FourierJacobi.Measure` prove:

- `valuationRingUnits_isCompact` and `valuationRingUnits_isOpen`: the actual
  subgroup `U` is compact and open in `Kˣ`.
- `unitValuationShell_zero_eq`: the valuation-zero locus is exactly `U`.
- `unitValuationShell_eq_uniformizer_smul`: every actual integral `π` with
  canonical valuation one gives `S_n^×=π^n U` for every integer `n`.
- `unitValuationShell_isCompact`, `unitValuationShell_isOpen`, and
  `unitValuationShell_measurableSet`: all these multiplicative shells are
  compact, open, and measurable.
- `unitValuationShell_pairwiseDisjoint`, `existsUnique_unitValuationShell`,
  and `iUnion_unitValuationShell_eq`: they form a countable disjoint
  partition of all `Kˣ`.
- `multiplicativeHaar`: the actual measure obtained from mathlib's Haar
  construction using `U` as a positive compact normalization set.
- `multiplicativeHaar_isHaarMeasure`: this construction is a Haar measure.
- `multiplicativeHaar_valuationRingUnits`: its normalization is `μ×(U)=1`.
- `multiplicativeHaar_unitValuationShell` and
  `multiplicativeHaar_real_unitValuationShell`: every integer shell has
  multiplicative Haar measure one, both in the native extended
  nonnegative-real codomain and as `Measure.real`.
- `multiplicativeHaar_sigmaFinite`: the normalized measure is sigma-finite,
  proved by the actual countable shell cover, without an added
  second-countability assumption.

There is no restriction on residue characteristic or primality. There is
no assumed shell-measure law, measure-preserving parametrization, integral
identity, or desired limit among the hypotheses.

## Mathematical proof

The valuation ring is compact and open. The group of its units inside
`Kˣ` is the intersection of the preimages of the valuation ring under the
continuous maps `u↦u` and `u↦u⁻¹`, so it is open. Its compactness follows
from the closed unit-pair realization inside the product of the compact
valuation ring with itself, as proved in mathlib's general submonoid-unit
compactness theorem.

Every field unit and its inverse have finite integer valuations `m` and
`n`. Multiplicativity gives `m+n=0`. They both belong to the valuation
ring exactly when `m,n≥0`, which together with `m+n=0` is equivalent to
`m=0`. This proves `S_0^×=U`.

The previously verified canonical-uniformizer theorem supplies `π` with
`v(π)=1` and proves `v(π^n)=n` for all integer powers. Therefore

\[
v(\pi^{-n}u)=0\quad\Longleftrightarrow\quad v(u)=n,
\]

giving `S_n^×=π^nU`. Multiplication is a homeomorphism of the actual
topological group, so every shell is compact and open. Every field unit
has exactly one finite valuation, proving both disjointness and exhaustion.

Apply Haar's construction to the positive compact set `U`; the construction's
normalization theorem gives its volume one, and the construction's Haar
invariance theorem gives

\[
\mu^\times(S_n^\times)=\mu^\times(\pi^n U)
=\mu^\times(U)=1
\]

for every integer `n`. These finite-volume shells cover the whole group,
which proves sigma-finiteness.

This normalization result does not yet prove the identity between the
restriction of multiplicative Haar measure to the units and normalized
additive Haar measure. It also does not yet transport the collision law
to a two-variable shell integral. Those are genuine remaining mathematical
formalization obligations in the Stage B bridge; no such identity is
silently assumed here.

## Verification

The following command completed inside the sandbox on 2026-09-11 with
exit code 0 and no warnings or errors:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lean -DwarningAsError=true -o build/fourier-jacobi-lean/.lake/build/lib/lean/FourierJacobi/Measure/MultiplicativeHaar.olean publications/fourier-jacobi-core-evaluation/FourierJacobi/Measure/MultiplicativeHaar.lean
```

The existing Lean `leanprover/lean4:v4.33.1` and mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` were retained. The final
publication-wide build, exhaustive axiom audit, and source hashes are
recorded in the parent verification record. No dependency was added or changed.

Checked source SHA256:
`1ac342347799a7b1cf37f4253eaf8d8d9bf012c2372dc8a489a64efb1df6c9fa`.
