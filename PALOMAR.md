# Palomar submission package

The selected claim is the **explicit-kernel Haar-core evaluation and its Abel
limits**. The paper's independently defined spherical coefficient and full
Fourier–Jacobi period identity are outside this submission. Read
[Challenge.lean](Challenge.lean) for the complete formal statement and
[README.md](README.md) for its mathematical context.

The submission uses the ordinary repository-root layout described by the
[Palomar submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
The standard was consulted on 13 September 2026; the recorded minimum Lean
release was v4.28.0. This repository retains Lean v4.33.1 and its existing
mathlib commit. No dependency revision was upgraded.

| Submission field | Value |
|---|---|
| Repository | `abhisaha-git/fourier-jacobi-core-evaluation` |
| Selected project | Repository root; leave the optional directory field empty |
| Comparator configuration | `comparator.json` |
| Metadata | `formalization.yaml` |
| Commit | The full 40-character SHA after committing and pushing this package |
| Repository license | `Apache-2.0`, in the existing root `LICENSE` |

The Challenge imports only Mathlib. It contains all mathematical definitions,
including the root table, actual matrix and minors, canonical valuation,
constructed Haar measures, integrands, and rational expression. Four
intentional theorem placeholders specify the claims. The author explicitly
authorized these statement-only placeholders. There are no definition holes.
The Solution repeats those definitions and theorem types, supplies checked
proofs, imports no Challenge, and audits all its own declarations, including
private helpers, against `propext`, `Classical.choice`, and `Quot.sound`.

| Compared declaration, in `FourierJacobiPalomar` | Claim |
|---|---|
| `measure_normalizations` | The constructed additive and multiplicative measures are Haar, with masses 1 and 1-q⁻¹ on their normalization sets |
| `integrability` | Measurability and ordinary Bochner integrability of each of the three integrands on the stated damped range, including the undamped interior |
| `principal_evaluation` | Nonzero quotient denominator, I₁=E_q, principal Abel convergence, and the same comparison with factor 2/(q+1) |
| `special_abel_limit` | Damped integrability, nonzero endpoint denominator, and the entire signed product's Abel limit at δ=εq⁻¹ᐟ² |

For the special theorem ε=±1 and α,β≠ε. The ε=1 product is identically zero.
No ordinary undamped endpoint integral or extension to exceptional Weyl walls
is asserted. The [theorem PDF](formalized_theorem_v1.pdf) also records
supplementary bounds and measurability consequences checked by
`StatementAudit_v1.lean`; the table above identifies the exact four Palomar
declarations, rather than claiming every auxiliary declaration is selected.

## Reproduce the local checks

With the pinned environment active, run:

```text
lake build --wfail
lake build Challenge
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true StatementAudit_v1.lean
lake env lean -DwarningAsError=true Solution.lean
```

The default build includes `Solution` and its PDF-audit dependency. The separate
Challenge build emits exactly the four authorized placeholder warnings.
The Windows `scripts/verify-lean.ps1` runs these checks; the existing
`scripts/setup-lean.ps1` first obtains project-local tools and dependencies.
The GitHub workflow runs the same proof checks and metadata checks.

For metadata and package checks, use Python 3.11 or later in a project-local
virtual environment and install `scripts/requirements-palomar.txt`, then run:

```text
python scripts/check-palomar.py
```

The checker validates metadata, dependency pins, allowed Challenge imports,
the identical definition and theorem-type text in the two files, the strict
placeholder boundary, local Markdown links, and forbidden source artifacts.
An optional `--schema PATH` additionally validates against a locally obtained
upstream v0.4 JSON schema. `--require-clean` rejects an uncommitted package.
These checks supplement Lean. They are not Comparator or NanoDa verification.
The evidence for this preparation is in
[verification/palomar-v1/README.md](verification/palomar-v1/README.md).

## Final submission steps

1. Review the four statements and `formalization.yaml`, then commit the
   complete package in GitHub Desktop, including the previously untracked
   `formalized_theorem_v1.tex` and `STATUS.md`. Push the commit to the public
   repository and wait for its Lean workflow to pass.
2. Run `python scripts/check-palomar.py --require-clean` and obtain the exact
   commit with `git rev-parse HEAD`. Confirm that the same commit is on GitHub.
3. Open [Palomar submissions](https://submit.palomar-registry.org/) and select
   the repository, full SHA and `comparator.json`. Inspect the displayed
   abstract and theorem selection before initiating review. An agent acting
   for the author must first read that service's
   [llms.txt](https://submit.palomar-registry.org/llms.txt).

Palomar performs its own preparation, protected Comparator comparison,
Lean/NanoDa verification and editorial review against that public commit.
Local type checking and source comparison do not substitute for those checks.
This repository preparation does not submit a request to Palomar, publish a
registration, or claim that its hosted checks have passed.
