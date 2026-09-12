# Actual source-normalized Haar mass of every lattice cell, version 1

The new module is
`publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/HaarCellMass.lean`.
It combines the independently defined actual lattice partition with the
checked actual shell and joint collision measures. It does not define a
core integral by the master series or assume an integral-to-series identity.

Let `K` be any actual nonarchimedean local field with its Borel measurable
space and canonical extended additive valuation `v=localFieldValuation K`.
Let `q=residueCardinality K` and `S=1-q⁻¹`. The actual product measure is

\[
M=\operatorname{paperMultiplicativeHaar}\times(\mu\times\mu),
\qquad \mu=\operatorname{additiveHaar},
\]

recorded as `FourierJacobi.Analysis.paperCoreMeasure K`. Here additive Haar
has `μ(O_K)=1`, while the multiplicative measure has unit-shell volume `S`,
exactly the source normalization `d×a=|a|⁻¹ da` requires. The canonical
measurable space on `Kˣ` is proved to be its Borel space in `HaarKernel`.

Fix any integer `r`, field element `z`, and a proof of
`CentralRepresentative K r z`: either `r=0` and `z=0`, or `r≠0` and
`v(z)=-r`. Fix a lattice index `i=(k,j,h,c)`, with `k,j,h` integers and
`c` natural. The set `haarLatticeCell K r z i` is defined by the actual
valuation conditions

\[
v(a)=k,\quad v(x)=j,\quad v(y)=h,
\]

together with the following independently specified depth condition:
`c=0` if `r=0` or `2h≠j-r`; otherwise
`v(y²/(xz)-1)=c`.

The main real-measure theorem is
`FourierJacobi.Analysis.haarLatticeCell_real_mass`:

\[
M(\operatorname{haarLatticeCell}(r,z;k,j,h,c))
=S^3q^{-j}q^{-h}w_r(j,h,c),
\]

where

\[
w_r(j,h,c)=
\begin{cases}
\mathbf 1_{c=0},&r=0\text{ or }2h\ne j-r,\\
(q-2)/(q-1),&r\ne0,\ 2h=j-r,\ c=0,\\
q^{-c},&r\ne0,\ 2h=j-r,\ c>0.
\end{cases}
\]

This real function is `haarCellWeight`. Its independent agreement with
the complex `Analysis.collisionWeight` is `haarCellWeight_coe`.
`haarLatticeCell_complex_mass` states the convenient complex-coercion form
of the actual measure equality, with precisely the `collisionWeight` used
by the independent master lattice family.

`haarLatticeCell_measure_ne_top` proves every cell has finite measure,
including zero-measure depth cells, for all `r,z,i` even without the
central-representative hypothesis. `haarLatticeCell_mass` gives the actual
extended nonnegative-real measure as `ENNReal.ofReal` of the displayed
formula. Thus the real value is justified by finiteness and is not an
interpretation of an infinite measure as `toReal=0`.

No assumption of integrability, positivity of a representation coefficient,
or the desired integral identity occurs in these declarations. There is no
restriction on residue characteristic, primality, or Satake parameters.
The actual residue cardinality satisfies `q>1` by the already checked
local-field theorem.

## Proof

The subset theorem `haarLatticeCell_subset_product` places every cell in

\[
S_k^\times\times(S_j\times S_h).
\]

The previously checked shell theorems give finite measures `S`,
`S q^{-j}`, and `S q^{-h}` to the three factors. Product-measure monotonicity
therefore proves finiteness of every cell before taking any real value.

Off the collision locus, or at `r=0`, the cell is exactly that product
when `c=0`, and is empty otherwise (`haarLatticeCell_eq_off`). Product Haar
measure immediately gives the claimed formula in both cases.

On the collision locus with `r≠0`, the central-representative hypothesis
gives `v(z)=-r`. The cell is exactly

\[
S_k^\times\times J_c(z;j,h),
\]

where `J_c` is the independently defined actual source ratio event from
`JointCollision` (`haarLatticeCell_eq_collision`). The already checked
joint theorem gives `μ×μ(J_c)=S²q^{-j}q^{-h}p_c`. Multiplicative shell
volume `S` supplies the remaining factor. The powers are kept as integer
powers, so the argument covers arbitrary negative valuations without
truncating them to natural numbers.

The resulting actual real measure is embedded into `ℂ`. Expanding the
real branch definition and using the real-to-complex ring homomorphism
proves exact agreement with the independently defined complex collision
weight, including the depth-zero fraction and all negative integer powers.

## Place in the integral bridge

The three source prefactors are `S⁻¹`, `q`, and `−q/S`. Multiplying them
by the extra multiplicative shell factor `S` gives the master coefficients
`κ₀=1`, `κ₁=qS`, and `κ₂=−q`, leaving the two additive factors `S²`.
This explains the normalization needed for the next cellwise integral
calculation. The stored finite row fractions receive no further restoration.

Measurability, disjointness, almost-everywhere exhaustion, and equality of
the actual matrix indices with the integer lattice indices are proved in
the separate `HaarLatticePartition` module. This mass theorem supplies the
measure part of the bridge. Equality of the full integral with the master
series additionally requires cellwise kernel values, norm summability,
integrability, and a justified countable integral/sum interchange. Those
are separate obligations and are not hypotheses concealed in this theorem.

## Verification

Development command, with all writable state inside the workspace:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lean -DwarningAsError=true -o build/fourier-jacobi-lean/.lake/build/lib/lean/FourierJacobi/Analysis/HaarCellMass.olean publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/HaarCellMass.lean
```

The version pins remain Lean `leanprover/lean4:v4.33.1` and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The final publication-wide
build and exhaustive axiom audit are supplied by the parent verification
record; this report does not claim hosted CI ran.

The displayed direct command completed inside the sandbox on 2026-09-11
with exit code 0 and no warnings or errors. The checked source hash is
included in the final publication verification record.
