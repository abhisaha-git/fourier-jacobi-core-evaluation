# Literal paper denominator domain, version 1

The new verified module is
`publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/PaperDomain.lean`.
It imports the independently transcribed `paperE` from `CoreParameters` and
proves its displayed denominator is nonzero on the natural domains below.

Let `q` be real with `q>1`, put `t=q^(-1/2)=inverseSqrt q`, and let
`a,b` be complex with `‖a‖=‖b‖=1`. The tuple in `paperD1` and `paperD2`
is `(a,a⁻¹,b,b⁻¹)`, retaining all four entries with their multiplicities.

The new declarations in `FourierJacobi.Analysis` are:

- `paperD1_eq_d₁`, `paperD2_eq_d₂`: the two independently written Fin-4
  products equal `Algebra.d₁ t a b d` and `Algebra.d₂ t a b d`. These
  identities hold for every real `q` and complex `a,b,d` as algebraic
  expressions. No nonvanishing is inferred from those identities alone.
- `paperC_ne_zero`: `paperC q ≠ 0` for `q>1`.
- `paperD1_ne_zero_of_norm_le_one`: `paperD1 q a b d ≠ 0` whenever `‖d‖≤1`.
- `paperD2_ne_zero_interior`: `paperD2 q a b d ≠ 0` whenever `t<‖d‖`.
- `paper_denominator_interior_ne_zero`: if `t<‖d‖≤1`, then
  `paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0`.
- `paperD2_special_positive`: at `d=t`, the second denominator is
  `fourFactors a b 1`.
- `paperD2_special_negative`: at `d=-t`, the second denominator is
  `satakeNumerator a b = (1+a)²(1+b)²/(ab)`.
- `paper_denominator_special_positive_ne_zero` and
  `paper_denominator_special_negative_ne_zero`: the corresponding signed
  endpoint denominator is nonzero when `a,b≠1` and `a,b≠-1`, respectively.
- `paper_denominator_special_ne_zero`: for a complex sign `ε` with
  `ε=1` or `ε=-1`, the literal denominator at `d=εt` is nonzero under
  precisely the additional exclusions `a≠ε` and `b≠ε`.

These denominator conclusions do not require the generic Weyl conditions
`a≠1`, `b≠1`, `a≠b`, or `ab≠1` except for the positive endpoint's
explicitly stated `a,b≠ε` requirement. They justify the literal quotient on
a broader domain than a generic finite-Weyl proof. They do not extend an
integral evaluation or an Abel limit across a Weyl wall by themselves.

## Proof

Expand the two Fin-4 products in their given order. Associativity and
commutativity identify them with the four factors at `x=dt` and `x=t/d`.
The already verified identity `paperC_eq_poincare` gives

\[
C_q=(1+t^2)^2(1+t^4)>0.
\]

For any unitary complex `z` and any `x` with `|x|<1`, the equality
`1-zx=0` would imply `1=|zx|=|x|`, a contradiction. The same applies to
`z⁻¹` because its norm is also one. Thus all four factors are nonzero.
In the interior,

\[
|dt|\le t<1,\qquad |t/d|=t/|d|<1.
\]

The first estimate remains valid at both signed endpoints. At `d=t`, the
second product has factors `1-a`, `1-a⁻¹`, `1-b`, and `1-b⁻¹`, all
nonzero precisely under the stated positive endpoint exclusions. At `d=-t`,
its factorization into `(1+a)²(1+b)²/(ab)` is the inherited proved algebra
identity, and unitarity gives `a,b≠0`. The exclusions `a,b≠-1` prove that
this expression is nonzero. Multiplication of the three nonzero factors
proves the final denominator results.

This proof concerns the actual literal rational formula. It does not use a
nonzero geometric denominator to infer convergence at a modulus-one ratio,
and it makes no assertion about an undamped endpoint core.

## Verification

The following command completed inside the sandbox on 2026-09-11 with
exit code 0 and no warnings or errors, using the unchanged project pins:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lean -DwarningAsError=true -o build/fourier-jacobi-lean/.lake/build/lib/lean/FourierJacobi/Analysis/PaperDomain.olean publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/PaperDomain.lean
```

Checked source SHA256:
`762795f1b118484be18046cd8c9205fa560d7cb3ed4a83471ab2193184007cb1`.
The final publication-wide build and exhaustive axiom audit are recorded in
the parent verification record. No dependency or toolchain was changed.
