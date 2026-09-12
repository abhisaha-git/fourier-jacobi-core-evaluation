# Verify the implemented lemmas using the currently selected pinned Lean environment.
[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
$leanVerificationRoot = Split-Path -Parent $PSScriptRoot
Push-Location $leanVerificationRoot
try {
    & lake build --wfail
    if ($LASTEXITCODE -ne 0) { throw 'Lean project build failed.' }
    & lake env lean '-DwarningAsError=true' 'Audit.lean'
    if ($LASTEXITCODE -ne 0) { throw 'Lean axiom audit failed.' }
    & lake env lean '-DwarningAsError=true' 'StatementAudit_v1.lean'
    if ($LASTEXITCODE -ne 0) { throw 'PDF statement implication audit failed.' }
    Write-Output 'Verified the implemented lemmas and their axiom dependencies.'
    Write-Output 'Verified the transcribed PDF definitions and theorem consequences.'
    Write-Output 'This does not certify the full period theorem; see STATUS.md.'
}
finally {
    Pop-Location
}
