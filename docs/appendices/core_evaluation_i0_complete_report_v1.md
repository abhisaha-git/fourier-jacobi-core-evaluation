# Complete independent I0 valuation series, version 1

This report concerns only the zero-central-coordinate part of the master
series: `r=0` means `z=0`. It does not claim the full fifty-row series, a Haar
integral identification, or the source spherical-coefficient identity.

The development is in
`publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/I0Complete.lean`.
It imports the unchanged v2 `Analysis/ValuationSeries.lean`. Its four existing
row proofs (source cases 1, 2, 6, 7) are inherited results, not new work.
The remaining six original-domain row evaluations, their bijections, the
complete lattice partition and the assembled I0 theorem are new.

## Exact theorem

Let `t,d,U,V,T` be complex numbers. Write

\[
 S=1-t^2,\quad X=TV,\quad Y=TU,\quad
 P=dXt,\quad N=Xt/d,\quad E=X^2t^2,\quad F=Yt^2,\quad G=Yt^4.
\]

Assume

\[
 |t^2|<1,\quad |P|<1,\quad |N|<1,\quad
 |E|<1,\quad |F|<1,\quad |G|<1.
\]

For ordinary Laurent arithmetic also require `t,d,U,V` nonzero. The Lean
identity is algebraically valid more generally in the field's totalized
inverse convention, but that convention is not used to interpret a singular
paper parameter. The natural range with `0<t<1`, unitary `U,V`,
`t≤|d|≤1`, and `0<T<1` satisfies all six strict norm bounds. For `T=1`,
the corresponding interior condition is `t<|d|≤1`.

Let `(ell,b)=cartanIndices 0 k j h 0`, independently defined from the
entry/minor integer minima. Define the actual shell summand

\[
 M(k,j,h)=S^2d^k
 t^{3k+2j+2h+3\ell+4b}Y^{\ell/2}X^b,
 \qquad (k,j,h)\in\mathbb Z^3.
\]

Every integer exponent is an integer power, including negative valuations.
The inherited valuation theorem proves `ell,b≥0`, and the evenness of `ell`
makes `ell/2` its nonnegative integer half. Damping is present in each
unsummed monomial through `Y=TU`, `X=TV`.

The new theorems prove

\[
 \sum_{\mathbb Z^3}|M(k,j,h)|<\infty,
 \qquad
 \sum_{\mathbb Z^3}M(k,j,h)=\sum_{\nu=1}^{10}R_\nu,
\]

where the right side is exactly the first ten stored fractions after the
damping substitution. The precise declarations, in namespace
`FourierJacobi.Analysis`, are `summable_norm_i0_full`, `hasSum_i0_full`, and
`tsum_i0_full`. The `HasSum` statement uses the unordered lattice family, not
merely an iterated sum and not a value stipulated by definition.

## All ten source rows and normalization

All ten source rows belong to `I0eq3`; their evaluated formulas have labels
`I0eqq1` through `I0eqq10`. The expanded source calculates
`E_{0,ν}=(1-q^{-1}) I_{0,ν}`. Consequently each stored `Rν` is its printed
fraction divided by `S=1-t²`, with the common Weyl factor `A_i/C_q` omitted.
The definition `i0Shell` already uses the restored shell coefficient `S²`.
No further restoration factor is applied in `I0Complete`.

| Source case | Stored row | Restored fraction `Rν` | HasSum declaration suffix | Provenance |
|---|---:|---|---|---|
| `I0eqq1` | 0 | `1/(1-P)` | `hasSum_i0_case1_regionTerm` | inherited v2 |
| `I0eqq2` | 1 | `S G/((1-P)(1-G))` | `hasSum_i0_case2_regionTerm` | inherited v2 |
| `I0eqq3` | 2 | `S X t²(1+X)/((1-P)(1-E))` | `hasSum_i0_case3_regionTerm` | new |
| `I0eqq4` | 3 | `S² F/((1-P)(1-E)(1-F))` | `hasSum_i0_case4_regionTerm` | new |
| `I0eqq5` | 4 | `S² F G/((1-P)(1-F)(1-G))` | `hasSum_i0_case5_regionTerm` | new |
| `I0eqq6` | 5 | `N/(1-N)` | `hasSum_i0_case6_regionTerm` | inherited v2 |
| `I0eqq7` | 6 | `N S G/((1-N)(1-G))` | `hasSum_i0_case7_regionTerm` | inherited v2 |
| `I0eqq8` | 7 | `N S X t²(1+X)/((1-N)(1-E))` | `hasSum_i0_case8_regionTerm` | new |
| `I0eqq9` | 8 | `N S² F/((1-N)(1-E)(1-F))` | `hasSum_i0_case9_regionTerm` | new |
| `I0eqq10` | 9 | `N S² F G/((1-N)(1-F)(1-G))` | `hasSum_i0_case10_regionTerm` | new |

The combined theorem `hasSum_i0_region` proves this entire table row by row;
its right side uses `Algebra.regionTerms`, rather than a separate transcription.

## Human proof in dependency order

First take the integer minima defining the Cartan indices. The inherited
theorem `tableZero_correct` verifies the table of `I0eq3` for every integer
triple, without a finite cutoff.

For `k≥0`, separate `j≥-2k` from `j<-2k`. In the first branch split at
`h=-k`, giving cases 1 and 2. In the second branch split at `h=k+j`;
below it is case 5, while the other part splits at `2h=j`, giving cases
3 and 4. For `k<0` use the analogous cuts `j=0`, `h=0`, and then `h=j`,
giving cases 6–10. The new declaration `i0RegionIndex_mem` verifies
exhaustiveness, and `i0Region_unique` verifies disjointness.
`i0Region_partition` combines the two into unique membership for every
integer triple.

For the six new rows, let `m,n,l` be arbitrary nonnegative integers. In the
positive branch put `k=m`; in the negative branch put `k=-m-1`. The following
maps parameterize the remaining rows.

| Cases | Positive `(j,h)` | Negative `(j,h)` | Extra index |
|---|---|---|---|
| 3, 8 | `(-2m-2n-e-1, -m-n-e+l)` | `(-2n-e-1, -n-e+l)` | `e∈{0,1}` |
| 4, 9 | `(-2m-2n-l-1, -m-n-l-1)` | `(-2n-l-1, -n-l-1)` | none |
| 5, 10 | `(-2m-n-1, -m-n-l-2)` | `(-n-1, -n-l-2)` | none |

These are the definitions `i0UpperRowEquiv`, `i0MiddleRowEquiv`, and
`i0LowerRowEquiv`. Each is a Lean `Equiv` with both inverse laws proved.
For the upper row, write the positive integer offset as `2n+e+1`; the inverse
uses integer division and remainder by 2. Thus both parity classes are present.
For the middle row, the two free nonnegative gaps are
`h-j-k` (positive branch) or `h-j` (negative branch), and `j-2h-1`.
For the lower row the gaps are the two strict inequalities, reduced by 1.

Substitution into the independently checked Cartan table yields the three
new `*_cartan` theorems. Substitute these results into `M`. Put `K=P,J=1`
in the positive branch and `K=N,J=N` in the negative branch. The three exact
reindexed monomials are respectively

\[
 S^2 J X^{e+1}t^2 K^m E^n(t^2)^l,
 \qquad S^2 J F K^m E^nF^l,
 \qquad S^2 J FG K^mF^nG^l.
\]

These identities are `i0_upper_reindexed`, `i0_middle_reindexed`, and
`i0_lower_reindexed`. They are exact Laurent calculations on the original
shell summand, not identities between proposed row fractions.

The stated modulus bounds make the norm of every displayed geometric product
summable on its complete product index. In the upper row the parity index is
finite, so it preserves absolute summability. Only after this proof do we
evaluate the geometric sums and transport them back along the bijections.
For the upper row the sum over `l` cancels one factor `S`; the two parity
classes contribute `X+X²`. For the middle and lower rows the displayed
triple products give the stored fractions immediately. This proves all six
new row formulas with exact normalization. The inherited four row formulas
provide the other cases.

Finally the finite measurable-free lattice partition transfers rowwise norm
summability to the entire integer family using `summable_partition`. Its
sigma equivalence and `HasSum.sigma_of_hasSum` then combine the ten actual
row sums. Absolute summability has already been proved before this
rearrangement. This proves `hasSum_i0_full`.

## Endpoint coverage and obligations beyond I0

The strict bounds cover the damped special parameter `d=εt` with unitary
`U,V`, for every real `0<T<1`. They do not cover its undamped endpoint:
there `|N|=1`. A nonzero rational denominator does not change that convergence
issue. The present complete I0 row evaluation alone does not assert an
undamped special core or the signed full-core Abel limit.

Beyond this module, the full-goal dependency chain includes the other forty actual rows and
their collision-depth weights, the full signed assembly and limits, the
independent Haar integral-to-series bridge, and the Cartan/Macdonald
identification with the paper's coefficient. None is a hypothesis hidden in
the I0 theorems. None is discharged merely by their finite algebra output.

## Verification record

The parent verification record supplies the pinned full publication build,
exhaustive axiom audit, exact source hashes and saved command output. The
development command for this module is:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lean -DwarningAsError=true -o build/fourier-jacobi-lean/.lake/build/lib/lean/FourierJacobi/Analysis/I0Complete.olean publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/I0Complete.lean
```

All new source and build output paths are inside this workspace. There is no
new package or toolchain dependency.

The displayed direct command completed successfully with exit code 0 and no
warning or error output on 11 September 2026. The exported module corresponds
to source SHA256
`de1412fb5284c7b193d3da8ec44c24563db9fa8ff1c587af41eb1372a4dfad94`.
The parent full build and exhaustive axiom audit remain the publication-wide
verification record, distinct from this successful module development check.
