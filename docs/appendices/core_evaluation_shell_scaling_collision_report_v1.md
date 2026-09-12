# Actual shell scaling, source normalization, and collision masses, version 1

This records three further checked Stage B ingredients in the new publication:
`Measure/UnitScaling.lean`, `Measure/PaperMultiplicativeHaar.lean`, and
`Measure/ShellCollision.lean`. None assumes the desired core integral identity.

Throughout, `K` is an actual field with a valuative relation, topology, and
mathlib's `IsNonarchimedeanLocalField K` instance. Let `q` be the actual
residue-field cardinality, `v=localFieldValuation K`, `μ=additiveHaar K`,
and `S_n={x:v(x)=n}` for every integer `n`. The measure spaces are Borel:
additive results use `BorelSpace K`, and the multiplicative normalization uses
`BorelSpace Kˣ`. The already proved `q>1` requires no residue-primality,
characteristic-zero, or oddness hypothesis.

## Actual additive scaling

In namespace `FourierJacobi.Measure`, `valuationRingUnits_smul_integers`
proves that each actual integral unit `u` preserves the valuation ring.
`distribHaarChar_valuationRingUnits` then proves its actual additive Haar
scaling character is one, using the normalized valuation-ring measure.

For every `u:Kˣ`, integer `n`, and equality `v(u)=n`, the theorem
`distribHaarChar_eq_of_canonicalValuation` proves

\[
\Delta(u)=q^{-n}.
\]

`additiveHaar_smul_of_canonicalValuation` therefore gives the native measure
identity `μ(uE)=q^{-n} μ(E)` for every set `E`, and
`additiveHaar_real_smul_of_canonicalValuation` gives its real-valued form.
`additiveHaar_smul_valuationRingUnits` specializes it to measure invariance
under every actual valuation-ring unit.

The proof writes `u=π^n w` using the previously proved actual-shell
parametrization, with `w` an integral unit. The actual Haar character is a
group homomorphism, its value at `π` was proved to be `q⁻¹`, and its value
at `w` is one. No asserted scaling law is supplied as a structure field.

## Source multiplicative normalization

The mathematical source specifies `d×a=|a|⁻¹ da` and hence
`vol×(O_K^×)=1-q⁻¹` (complete TeX lines 221 and 228). The auxiliary
`multiplicativeHaar` is normalized instead by `vol(O_K^×)=1`.

The new definition restores the source normalization explicitly:

\[
\operatorname{paperMultiplicativeHaar}
  =\operatorname{ofReal}(1-q^{-1})\cdot\operatorname{multiplicativeHaar}.
\]

`paperMultiplicativeHaar_isHaarMeasure` and
`paperMultiplicativeHaar_sigmaFinite` prove the actual measure is Haar and
sigma-finite. `paperMultiplicativeHaar_valuationRingUnits`,
`paperMultiplicativeHaar_unitValuationShell`, and
`paperMultiplicativeHaar_real_unitValuationShell` give the exact mass
`1-q⁻¹` on every integer multiplicative shell. The positivity of the
scaling factor is proved by `paperMultiplicativeFactor_pos`.

This is the measure to use with the source prefactors
`S⁻¹`, `q`, and `−q/S`, where `S=1-q⁻¹`. In particular the auxiliary
unit-normalized measure must not be used in the source integral without
this conversion. These results establish the normalization but do not yet
identify the full measure with the independently weighted measure
`|a|⁻¹ da` on arbitrary measurable sets.

## Collision distribution on every actual integer shell

Fix any integer `n` and any actual field element `a` with `v(a)=n`.
For a natural depth `c`, independently define

\[
T_c(a,n)=\{x:v(x)=n,\ v(x-a)\ge n+c\},\qquad
D_c(a,n)=T_c(a,n)\setminus T_{c+1}(a,n).
\]

These are `shellCollisionTail` and `shellCollisionDepth`. Their
measurability is proved in `shellCollisionTail_measurableSet` and
`shellCollisionDepth_measurableSet`. The infinite-cancellation point
`x=a` remains in every finite tail and is excluded by the exact-depth
difference; it is never assigned a finite valuation.

The actual conditional mass is defined as

\[
P_n(E)=\frac{\mu(E\cap S_n)}{\mu(S_n)}.
\]

Its denominator is already proved finite and strictly positive by the
integer-shell theorem. The new checked statements are

\[
P_n(D_0(a,n))=\frac{q-2}{q-1},\qquad
P_n(D_c(a,n))=q^{-c}\quad(c\ge1).
\]

The exact Lean declarations are
`shellConditionalMass_collisionDepth_zero` and
`shellConditionalMass_collisionDepth_pos`. They hold uniformly for every
integer `n`, including negative `n`, and every center in that shell.
`shellConditionalMass_singleton` proves the exact-cancellation point has
conditional mass zero.

Here is the proof in dependency order. At depth zero, the ultrametric
inequality implies `T_0(a,n)=S_n` (`shellCollisionTail_zero_eq`). At every
positive depth, `v(x-a)>v(a)` implies `v(x)=v(a)=n`; therefore the shell
condition is redundant:

\[
T_c(a,n)=a+B_{n+c}\quad(c>0).
\]

This is `shellCollisionTail_eq_preimage`, in subtraction-preimage form.
Translation invariance and the all-integer ball formula give
`μ(T_c)=q^{-(n+c)}`. Exact positive depths similarly are the translates
`a+S_{n+c}` (`shellCollisionDepth_eq_preimage`), with measure
`(1-q⁻¹)q^{-(n+c)}`. Division by
`μ(S_n)=(1-q⁻¹)q^{-n}` gives `q^{-c}`. At depth zero subtract the first
positive tail from `S_n` and divide by the same positive shell mass:

\[
\frac{(1-q^{-1})q^{-n}-q^{-(n+1)}}{(1-q^{-1})q^{-n}}
=\frac{q-2}{q-1}.
\]

Finally actual additive Haar is atomless, as proved in the inherited module,
so the infinite-cancellation point has measure zero. This derives the
arbitrary-shell law directly from actual field sets and actual Haar measure;
it assumes no transported collision distribution.

The joint two-variable determinant shell partition and integration of the
kernel over that partition remain separate obligations. This result is
the fixed-center section needed for their measure calculation.

## Verification

Each listed module completed a direct sandbox check on 2026-09-11 with
exit code 0 and no warnings or errors. For each module `NAME`, the command was:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lean -DwarningAsError=true -o build/fourier-jacobi-lean/.lake/build/lib/lean/FourierJacobi/Measure/NAME.olean publications/fourier-jacobi-core-evaluation/FourierJacobi/Measure/NAME.lean
```

The unchanged pins are Lean `leanprover/lean4:v4.33.1` and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The final publication-wide
build, exhaustive audit and source-hash record are supplied by the parent
verification record. No dependencies or toolchains were installed or changed.

The checked source SHA256 hashes are:

| Module | SHA256 |
|---|---|
| UnitScaling | `bcf89a5396f10760282e2768fb26ca7dd3ac648f3ff4d2660707d715229d19de` |
| PaperMultiplicativeHaar | `ac3782feb6caed22812581ad82ef8c6a182fb8279259cf74d6114692f350e3d7` |
| ShellCollision | `bf77a504c982c0fd580a155b869cafb1d22857e1f2459122764c3ad73e1d497e` |
