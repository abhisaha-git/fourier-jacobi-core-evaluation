# Independent review of the Stage A top-level chain, v1

**Conclusion:** I found no defect in the reviewed top-level definitions,
hypotheses, normalization, or limit arguments. The two reviewed modules prove
the corrected comparisons at the independent infinite valuation-series scope.
They do not by themselves identify that series with the actual Haar or spherical
core.

This review inspected `Analysis/LatticeCore.lean` and
`Analysis/LatticeLimits.lean`, and followed their relevant dependencies through
`MasterSeries`, `MasterDamping`, `CoreParameters`, `RationalLimits`,
`PaperDomain`, `Cartan`, and the inherited finite-core theorem. It is a
mathematical/source review, not a replacement for the publication's full build
and exhaustive axiom audit. No shared Lean source was edited.

## Definitions and proof integrity

`latticeCore` is the brief's independent nested lattice sum:
the actual finite eight-Weyl and three-central-index sums surround the
\(\mathbb Z^3\times\mathbb N\) family `masterTerm\), divided by `paperC`.
Neither `finiteCore` nor `paperE` occurs in its definition.

The master summand matches the brief:
\(r=0\) uses the zero central coordinate; \(r=1,2\) use central valuation
\(-r\). The coefficients are \(1,q(1-q^{-1}),-q\).
The depth weight forces \(c=0\) at \(r=0\) and away from \(2h=j-r\);
on collision it is \((q-2)/(q-1)\) at depth zero and \(q^{-c}\) otherwise.
Its monomial contains exactly
\((1-t^2)^2\delta^k t^{3k+2j+2h+6n+4b}(TU)^n(TV)^b\).
The integer Cartan definitions prove \(n,b\ge0\); subtraction is not truncated
to impose nonnegativity. Integer valuation exponents remain integer powers.

`summable_norm_weightedLatticeTerm` proves norm summability of the entire
unordered family from the three actual shell-family norm-summability theorems.
`hasSum_weightedLatticeTerm_of_norm` explicitly receives that proved property
before using product-sum rearrangement. The top-level theorems discharge it from
natural parameter bounds. No assumed row identity, integral bridge, summability,
or limit is hidden in a structure field.

`central_master_sum_eq_rows` uses the three proved infinite `HasSum`
theorems and the exact \(10+15+25=50\) split. The row arguments are \(TU,TV\).
There is no second application of the restored-row factors. Damping is not
inserted into the final formula for \(E_q\).

## Principal evaluation and Abel convergence

The precise main statement is
`infinite_lattice_core_evaluation`. Its hypotheses are:

- real \(q>2\), with \(t=q^{-1/2}\);
- \(|\alpha|=|\beta|=1\);
- \(t<|\delta|\le1\);
- \(\alpha\ne1\), \(\beta\ne1\), \(\alpha\ne\beta\), and
  \(\alpha\beta\ne1\).

It concludes norm summability, a `HasSum` of the full family to the independently
transcribed `paperE`, nonvanishing of the literal denominator
\(C_qD_1D_2\), and Abel convergence through real \(0<T<1\).
The paper's principal case \(|\delta|=1\) is included.

`latticeCore_eq_paperE` first identifies the undamped independent sum with
the finite expression, then applies the inherited
`Algebra.finiteCore_eq_closedCore`. The separate checked identity
`paperE_eq_closedCore` matches the exact brief's \(E_q\), including the
four-factor tuple with multiplicities and \(t=q^{-1/2}\).
Thus the inherited finite algebra is used as a dependency, not presented as the
new infinite-series result.

Abel convergence is stronger than a bare rational-continuity argument:
`masterTerm_damping` proves the actual term identity
\(H_T=T^{H}H_1\), where \(H=-u\ge0\).
`masterTerm_norm_le_undamped` and the proved undamped norm summability then
give dominated convergence of the actual infinite family.
All denominator regularity required by the inherited finite theorem is derived
from the displayed natural assumptions.

Only after the core evaluation and convergence does
`corrected_principal_lattice_comparison` apply the factor:
\[
 \frac{2}{q+1}\mathcal L_1(\delta)
 =\frac{2}{q+1}E_q(\alpha,\beta,\delta),\qquad
 \frac{2}{q+1}\mathcal L_T(\delta)
 \longrightarrow\frac{2}{q+1}E_q(\alpha,\beta,\delta).
\]
This is exactly the corrected series analogue of
\(\mathrm{RHS}(77)=\frac{2}{q+1}\mathrm{RHS}(184)\).
There is no missing or duplicated principal factor.

## Special endpoint treatment

`infinite_lattice_special_abel` uses the same \(q>2\), unitary parameters,
and four regular Weyl exclusions, together with
\(\varepsilon\in\{1,-1\}\) and
\(\alpha,\beta\ne\varepsilon\).
It proves norm summability and `HasSum` for **every damped** \(0<T<1\),
nonvanishing of the literal endpoint quotient's denominator, and
\[
 \frac{1-\varepsilon}{q+1}\,
 \mathcal L_T(\varepsilon t)
 \longrightarrow
 \frac{1-\varepsilon}{q+1}\,
 E_q(\alpha,\beta,\varepsilon t).
\]
The filter is precisely \(\mathcal N[\, (0,1)\,](1)\) on real \(T\).
This is the corrected series analogue of \(\mathrm{RHS}(80)=\mathrm{RHS}(191)\),
with no extra factor.

For \(\varepsilon=1\), `tendsto_lattice_special_positive` invokes the
identically zero whole-product theorem. It neither requires nor asserts an
undamped endpoint core. The unconstrained standalone zero-product lemma is
only an algebraic statement about a total function; the packaged mathematical
theorem separately supplies summability of every damped family.

For \(\varepsilon=-1\), the proof first identifies each damped independent
sum with the row-damped rational expression, using strict convergence bounds.
It then uses continuity of those rational rows at \(T=1\) on the regular
endpoint locus. In particular, the potentially modulus-one row ratio has
denominator \(1+V_i\), nonzero because \(\alpha,\beta\ne-1\).
This is a valid Abel argument: it never infers ordinary endpoint-series
convergence from a nonzero modulus-one geometric denominator.
No assertion about an undamped family at \(\delta=\pm t\) appears in the
packaged special theorem.

## Limitations, not defects

- These two modules evaluate the independent lattice object. Actual Haar
  identification and the paper's independently defined spherical coefficient
  require their separate bridges.
- The arithmetic range remains \(q>2\); no result at \(q=2\) is asserted.
- The four generic Weyl exclusions remain for evaluation. Norm-summability
  helper lemmas that use totalized Weyl weights at a wall do not establish an
  extension of the intended kernel there.
- At the negative special endpoint, \(\alpha=-1\) or \(\beta=-1\) remains
  excluded. No extension to the nonsingular cancelled target \(G_{\rm sp}\)
  is proved here. At the positive endpoint these particular values are not
  additionally excluded if the other displayed regularity conditions hold.
- The review followed the top-level row interfaces; it is not a new independent
  line-by-line audit of all fifty source fractions or all generated inverse laws.

## Reviewed source hashes

- `LatticeCore.lean`:
  `79E4272FB0D7726FD54A8CDB0D1E43FD5D20DC9DE819B5A7198433EC3ED5482A`
- `LatticeLimits.lean`:
  `D2035C18B029546C97EC11335E08B6DD5ECDD1D544EC7F9447DB11BB8B56887E`

A textual scan of both reviewed modules found no `sorry`, `admit`,
new `axiom`, `native_decide`, or `unsafe`.

