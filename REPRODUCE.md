# Reproduction

Pins: Lean `leanprover/lean4:v4.33.1`; mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The checked transitive dependency
revisions are retained in `lake-manifest.json` and `verification/dependencies.json`.

From the original workspace root, activate the environment in each fresh shell:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lake -d build/fourier-jacobi-core-lean build --wfail
lake -d build/fourier-jacobi-core-lean env lean -DwarningAsError=true publications/fourier-jacobi-core-evaluation/Audit.lean
lake -d build/fourier-jacobi-core-lean env lean -DwarningAsError=true publications/fourier-jacobi-core-evaluation/StatementAudit_v1.lean
```

The external Lake configuration's `srcDir` points to THIS publication. It reuses
only workspace-local dependencies and build products, stored outside the
publication. It shares the project module cache with the previous verification;
the full Lake build checks the delivered source files against its build traces.
The corresponding configuration and final source hashes are retained in the
verification record. An old v2 build is not used as verification of new modules.

After copying this directory into a standalone repository, select the pinned
toolchain and run:

```text
lake build --wfail
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true StatementAudit_v1.lean
```

For the included Windows setup, `scripts/setup-lean.ps1` installs missing tools
and obtains dependency caches inside that copied repository. It respects the
pins and checks the manifest. It does not modify the global Lean installation.
The included GitHub workflow runs this local setup, the build, the axiom
audit and the PDF statement implication audit through `scripts/verify-lean.ps1`.
Its presence is configuration, not evidence of a hosted CI run.

The generators are optional: the generated Lean source is the proof artifact.
Python and SymPy are not needed for Lean verification. All proof certificates
are checked by Lean's kernel; no `native_decide` certificate is used.

To check the delivered source snapshot against its recorded hashes, run
`./scripts/verify-source-record.ps1` from the publication. This is a read-only
identity check, not a substitute for compiling changed sources.
For the supplementary fifty-row comparison, use an existing suitable Python
environment with `scripts/requirements-generation.txt` and run
`python scripts/verify-row-restorations.py`. It reads the retained raw
transcriptions and rederives the three restoration factors. The optional
`--source PATH` also checks the complete TeX's hash, all fifty unique labels,
and literal final fractions. Neither Python nor this symbolic check is in the
Lean proof trust chain.

Choose the license before distributing the repository. This packaging decision
does not change the mathematical statements or the local verification commands.

## Standalone theorem PDF

`formalized_theorem_v1.tex` is the complete source of the five-page standalone
statement in `formalized_theorem_v1.pdf`. It has no external mathematical
references, project-file dependencies, or omitted coefficient tables.
`StatementAudit_v1.lean` transcribes its definitions and proves its theorem
clauses from the existing development; it is checked separately from the 69
original project modules. The final audit report is
`verification/pdf-statement-audit-v1.md`.

From the original workspace, using the existing MiKTeX installation read-only:

```powershell
& ./publications/fourier-jacobi-core-evaluation/scripts/build-formalized-theorem-v1.ps1 -WorkspaceRoot (Get-Location).Path
```

From a copied publication, run `./scripts/build-formalized-theorem-v1.ps1`.
Supply `-TexBin PATH` if pdfLaTeX is installed in a different directory.
The script installs nothing, disables shell escape and the package installer,
runs three passes, and keeps all writable TeX state and intermediate files
under the chosen workspace. It copies only the finished PDF to the publication.
The recorded original run required the workspace's narrow compilation exception
after sandbox process launch was denied; Lean checks ran inside the sandbox.

The optional `scripts/audit-formalized-theorem-v1.py` uses an existing Python
with `pypdf` to check PDF structure, self-containment, resolved references,
compiler output paths and file hashes. This is document QA, not a mathematical
proof checker. Its installed package version is recorded in the QA output.
The PDF was also rendered with Poppler and all five pages visually inspected.
