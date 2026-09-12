# Actual joint collision-shell mass, version 1

The new module is
`publications/fourier-jacobi-core-evaluation/FourierJacobi/Measure/JointCollision.lean`.
It builds on the checked arbitrary-shell collision theorem and proves its
product-Haar assembly for the source's determinant and ratio expressions.

Let `K` be an actual nonarchimedean local field with its Borel measurable
space, let `q` be its actual residue cardinality, let `v=localFieldValuation K`,
and let `μ=additiveHaar K`, normalized by `μ(O_K)=1`. Put `S=1-q⁻¹`.
Fix integers `j,h,s`, a field element `z` with `v(z)=s`, and a natural
integer `c`. Assume the collision relation

\[
2h=j+s.
\]

Define the actual event in the source coordinate order `(x,y)` by

\[
J_c(z;j,h)=\{(x,y):v(x)=j,\ v(y)=h,
  \ v(y^2/(xz)-1)=c\}.
\]

This is `sourceJointCollisionDepth K z j h c`. Every nonzero divisor used
in the proof is derived from the displayed finite-valuation hypotheses.
Define `p_0=(q-2)/(q-1)` and `p_c=q^{-c}` for `c>0`, recorded independently
as `shellCollisionProbability K c`.

The main checked real-measure statement is
`FourierJacobi.Measure.additiveHaar_real_prod_sourceJointCollisionDepth`:

\[
(\mu\times\mu)(J_c(z;j,h))
=S^2 q^{-j}q^{-h}p_c.
\]

All powers with integer exponents are retained as integer powers in Lean.
The native extended nonnegative-real measure theorem is
`additiveHaar_prod_sourceJointCollisionDepth`. Its right side is
`ENNReal.ofReal(p_c * μ.real(S_j)) * μ(S_h)`; all these shell measures
are independently proved finite and the corresponding real formula is
deduced from that native measure equality. The event's measurability is
`sourceJointCollisionDepth_measurableSet`.

For the requested central shells, substitute `s=-r`. The hypothesis then
reads `2h=j-r`, exactly the collision locus used by the master series.
The theorem applies to `r=1` and `r=2`, with no additional restriction.
It is an actual joint measure computation, not an assumed probability law.

## Proof in dependency order

First, `shellCollisionDepth_mem_iff` identifies the earlier difference of
tails with the exact finite valuation equation
`v(x-a)=j+c` inside `v(x)=j`. The proof retains the value infinity and
excludes it from every finite-depth event.

For fixed `y` with `v(y)=h`, the center `a=y²/z` satisfies

\[
v(a)=2h-s=j
\]

by `collision_center_valuation`. The polynomial identity

\[
y^2-xz=-z(x-y^2/z)
\]

gives
`v(y²-xz)=s+v(x-y²/z)` (`determinant_valuation_at_center`). Thus the
section in the `x` variable of the determinant-depth event is exactly the
previously proved collision-depth event centered at `y²/z`, when `y` lies
in its prescribed shell; otherwise the section is empty.

This section identity is `jointCollisionDepth_section`. The earlier
arbitrary-center collision result gives the same measure
`p_c μ(S_j)` in every nonempty section. The determinant event is measurable
because it is an intersection of measurable valuation-shell preimages
under actual polynomial maps. Apply the product-measure section theorem
and integrate this constant over the actual `y` shell. This gives
`p_c μ(S_j) μ(S_h)`.

The calculation so far uses the temporary coordinate order `(y,x)`.
For the source ratio, direct field algebra and the valuation law give

\[
v(y^2/(xz)-1)=c
\quad\Longleftrightarrow\quad
v(y^2-xz)=j+s+c,
\]

provided `v(x)=j` and `v(z)=s` (`collision_ratio_valuation_iff`). The
zero determinant has infinite valuation on both sides of this equivalence;
it is never assigned a finite depth. The actual coordinate-swap
measure-preserving theorem changes `(y,x)` to `(x,y)`. This proves the
native product measure formula for the source event. Finally substitute
the checked all-integer shell volumes
`μ(S_j)=S q^{-j}` and `μ(S_h)=S q^{-h}`.

The second-countability needed for polynomial measurability and
sigma-finite product Haar is derived from the actual local-field objects
in the checked `KernelIndices` module: a compatible nontrivially normed
field structure is obtained from the rank-one valuation, and local
compactness supplies a proper metric. It is not an extra hypothesis of
the displayed theorem. Sigma-finiteness of additive Haar follows for
that actual locally compact second-countable group.

## Normalization and remaining bridge

The formula here concerns the two additive coordinates. The paper's
multiplicative coordinate uses `paperMultiplicativeHaar`, whose every
integer shell has mass `S`, independently proved in its own module.
Combining that factor with the source prefactors `S⁻¹`, `q`, `−q/S`
produces the shell coefficients `1`, `qS`, `−q`, exactly as required by
the master family. No restoration of the stored row fractions is made
in this collision theorem.

This module does not assert integrability of the explicit kernel, a
countable integral-to-series interchange, or a spherical-coefficient
identification. Those remain separate bridge obligations. The complete
lattice partition, including off-collision and zero-central cases, is
developed independently of this measure computation.

## Verification

The development command, with all writable state in the workspace, is:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lean -DwarningAsError=true -o build/fourier-jacobi-lean/.lake/build/lib/lean/FourierJacobi/Measure/JointCollision.olean publications/fourier-jacobi-core-evaluation/FourierJacobi/Measure/JointCollision.lean
```

The unchanged pins are Lean `leanprover/lean4:v4.33.1` and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The publication-wide final
build, exhaustive axiom audit and checked-source hashes are recorded by
the parent verification record. No new dependencies were needed.

The displayed direct command completed inside the sandbox on 2026-09-11
with exit code 0 and no warnings or errors. Checked source SHA256:
`5750bb80d8977d0cad7c72cd1eabe563f1ac503eb32e405c5aa8a0d5b93d1acc`.
