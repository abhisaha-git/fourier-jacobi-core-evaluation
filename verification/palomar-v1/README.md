# Palomar preparation verification, version 1

All local preparation checks passed on 13 September 2026, with Lean
`leanprover/lean4:v4.33.1` and the unchanged mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. This folder supplements the
historical proof record without replacing it.

| Check | Result | Evidence |
|---|---|---|
| Default library and Solution build, warnings treated as errors | 3,167 jobs passed | [build.txt](build.txt) |
| Mathlib-only Challenge build | 2,667 jobs passed; exactly four authorized theorem-placeholder warnings | [challenge.txt](challenge.txt) |
| Complete mathematical library audit | 4,609 declarations across 69 modules passed | [axioms.txt](axioms.txt) |
| PDF statement implication audit | 62 named declarations and private helpers passed | [pdf-statement.txt](pdf-statement.txt) |
| Solution audit | 89 declarations, including private helpers, passed | [solution.txt](solution.txt) |
| Source and metadata checks | Identical common definitions and four theorem types; no proof placeholders; upstream v0.4 schema passed | [source-check.json](source-check.json) |
| Dependency source verification | All nine revisions match the manifest; no tracked dependency changes | [dependencies.json](dependencies.json) |
| Source preservation | All 71 original library/root/audit Lean files match the previous verified hashes | [summary.json](summary.json) |

The Challenge has 209 lines and 11,698 UTF-8 bytes, below Palomar's preferred
300-line/32-KiB warning thresholds. There are no definition holes. Each of the
four Solution results depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The Solution does not import Challenge. Its definitions use actual
matrices, canonical valuations and constructed Haar measures; private proved
equalities connect them to the earlier PDF statement audit. Source text
comparison verifies the shared definitions and theorem types, separately from
the transitive axiom audit.

The source review checked both normalizations, the finite Weyl root table,
integer entry/minor minima, the damping height, parameter and denominator
exclusions, and both principal and signed special prefactors. It retains the
precise boundary: an explicit-kernel evaluation, without a spherical-coefficient
identification or a full-period theorem. The positive special factor is zero;
no ordinary undamped endpoint integral is claimed.

From the original workspace root, the completed combined check was:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
& ./publications/fourier-jacobi-core-evaluation/scripts/verify-lean.ps1 -LakeProject build/fourier-jacobi-palomar-lean -OutputDirectory publications/fourier-jacobi-core-evaluation/verification/palomar-v1
```

[workspace-lakefile.toml](workspace-lakefile.toml) records the build configuration.
It selects the delivered publication sources and reuses only the existing
workspace-local dependency and build directories. [output-paths.json](output-paths.json)
records the checked output roots. All Lean compilation ran inside the sandbox.
The original 69 proof modules, original audit and root module were not edited;
the Lakefile adds the Challenge, Solution and PDF-audit targets without changing
dependency pins. No global installation or configuration was changed.

Metadata checks used Python 3.12.14 and the pinned packages in
`scripts/requirements-palomar.txt`, installed only in the workspace `.venv`:

```text
.venv/Scripts/python.exe publications/fourier-jacobi-core-evaluation/scripts/check-palomar.py --schema .cache/palomar/formalization-v0.4.schema.json --output publications/fourier-jacobi-core-evaluation/verification/palomar-v1/source-check.json
```

The schema was downloaded from the [upstream v0.4 schema](https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/v0.4.schema.json);
its SHA-256 is recorded in `source-check.json`. The local checker also passed
license consistency, dependency pin, forbidden-artifact and local-link checks.
The updated PowerShell scripts passed syntax checks and the complete proof
runner executed successfully. The GitHub workflow passed YAML/trigger checks;
execution of that updated workflow remains a post-push check.

`source-check.json` fingerprints all source/data/script/document files outside
`verification/`. It normalizes CRLF to LF for the listed UTF-8 files so a normal
Git checkout on another platform does not invalidate the record; binary files
are hashed byte-for-byte. `scripts/verify-source-record.ps1` verifies that
snapshot and retains an explicit `-Record` option for older snapshots.
[record-sha256.json](record-sha256.json) fingerprints the evidence in this folder
other than itself. No commit hash is fabricated for the uncommitted package.

The remote repository was confirmed public. **This is local preparation
evidence, not official Palomar verification.** Protected Comparator export and
comparison, NanoDa replay, canonical dependency-source checks, the service's
license detector and editorial review remain Palomar's hosted steps against
the public submission commit. No submission, registration or push was performed.
See [PALOMAR.md](../../PALOMAR.md) for the final commit-and-submit sequence.
