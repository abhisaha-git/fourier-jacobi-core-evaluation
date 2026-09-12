# Actual Haar cell values and master normalization

The new modules `Analysis/HaarCellValue.lean` and
`Analysis/HaarCellMaster.lean` concern the actual integrand on the actual
valuation-and-cancellation cells. Their left sides use the local-field
definitions in `HaarKernel.lean`, `HaarLatticePartition.lean`, and
`HaarCellMass.lean`. No finite region fraction appears in these modules.
The publication's current build and exhaustive audit record verification
of the delivered sources.

## Precise statements

Let `K` be a field with the project's nonarchimedean local-field structure
and canonical integer valuation. Let `r` be an integer and let `z` be a
`CentralRepresentative`: `z=0` when `r=0`, and `v(z)=-r` otherwise.
For `i=(k,j,h,c)` and every point `p` of `haarLatticeCell K r z i`,

`explicitCoreIntegrand K q a b d T z p = haarCellValue q a b d T r i`.

This is `FourierJacobi.Analysis.explicitCoreIntegrand_eq_haarCellValue`.
The scalar on the right is defined independently by

`d^k · rpow(q^(-k),3/2) · T^(-u) · weylKernelAtIndices(t,a,b,n,B)`,

where `t=(sqrt q)^(-1)`, `u=entryMinimum r k j h`,
`n=(cartanIndices r k j h c).1/2`, and
`B=(cartanIndices r k j h c).2`. All displayed integer powers remain
integer powers. For `q>0`, `haar_scale_rpow` and
`haar_scale_rpow_coe` prove the literal real-power factor is exactly
`t^(3k)` (over the reals and after coercion to the complexes).

For `q>1`, `T≠0`, and `r∈Fin 3`,
`prefactor_cellScalarMass_haarCellValue` proves

`a_r · [S³ q^(-j) q^(-h) ω_r(j,h,c)] · haarCellValue`
`= ∑ w∈Fin 8, (A_w/Cq) · masterTerm(q,t,d,U_w,V_w,T,r,i)`,

with `S=1-q^(-1)` and the source prefactors
`a₀=S^(-1)`, `a₁=q`, and `a₂=-q/S`.
For the actual residue cardinality and source-normalized product measure,
`haarLatticeCell_prefactor_value` replaces the bracketed scalar by the
actual real Haar measure of `haarLatticeCell`, using the independently
proved `haarLatticeCell_complex_mass`.

The algebraic identities do not need generic Satake hypotheses to type
check. Their intended kernel interpretation uses the paper's unitary
parameters and regular Weyl locus, where the literal Weyl quotients have
nonzero denominators. They do not provide a parameter extension across
singular Weyl walls.

## Human proof

Membership in a Haar cell gives the actual valuations of `a,x,y` and,
on a collision, the finite valuation of `y²/(xz)-1`. The theorem
`haarLatticeCell_kernelCoordinates` identifies the actual entry/minor
indices, Cartan exponents, and height with the integer-minimum formulas.
The valuation of the unit coordinate `a` is exactly `k`, as follows by
injectivity of the finite-value embedding into `WithTop ℤ`.
Substitution into the independently defined integrand therefore proves
constancy on the cell.

For the absolute-value factor, `t²=q^(-1)` gives `q^(-k)=t^(2k)` for
every integer `k`. Since `t>0`, the real-power multiplication law yields
`rpow(q^(-k),3/2)=t^(3k)`. This step applies equally to positive and
negative valuations; no valuation is replaced by its natural-number
part.

The exact integer identities give `H=n+B` and `ell=2n`. Distributing
`T^(n+B)` inside the finite Weyl sum gives `(TU_w)^n(TV_w)^B`.
The remaining kernel factor is `t^(6n+4B)`. This is the theorem
`haarCellValue_expanded`, which uses `T≠0` for the integer-power product
law. The final damped range `0<T<1` and the interior value `T=1` both
satisfy that hypothesis.

The actual cell mass is `S³ q^(-j)q^(-h)ω_r`. The three finite scalar
equalities `a_r S³=κ_r S²` give respectively
`κ₀=1`, `κ₁=qS`, and `κ₂=-q`. Finally,
`q^(-j)q^(-h)=t^(2j+2h)`. Multiplying the cell mass and cell value now
gives exactly the independent master summand, with exponent
`3k+2j+2h+6n+4B`, its true cancellation weight, and its actual shell
coefficient. This derives the normalization once from the actual Haar
volumes; it never reapplies a stored row restoration.

These cell identities are the input to the separate integrability and
countable-partition integration argument. They do not by themselves
assert an integral/sum interchange or identify the explicit kernel with
the paper's independently defined spherical coefficient.
