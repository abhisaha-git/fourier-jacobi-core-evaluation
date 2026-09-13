# Verify the implemented lemmas using the currently selected pinned Lean environment.
[CmdletBinding()]
param([string]$LakeProject = '', [string]$OutputDirectory = '')
$ErrorActionPreference = 'Stop'
$leanVerificationRoot = Split-Path -Parent $PSScriptRoot
$leanLakeArgs = @()
if ($LakeProject) { $leanLakeArgs = @('-d', [IO.Path]::GetFullPath($LakeProject)) }
if ($OutputDirectory) {
    $OutputDirectory = [IO.Path]::GetFullPath($OutputDirectory)
    if (-not $OutputDirectory.StartsWith($leanVerificationRoot + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
        throw 'Verification logs must remain inside this publication.'
    }
    New-Item -ItemType Directory -Force -Path $OutputDirectory | Out-Null
}
function Invoke-LeanVerificationStep([string]$LogName, [string[]]$Arguments) {
    if ($OutputDirectory) {
        & lake @leanLakeArgs @Arguments *> (Join-Path $OutputDirectory $LogName)
    } else {
        & lake @leanLakeArgs @Arguments
    }
    if ($LASTEXITCODE -ne 0) { throw "Lean verification failed: $LogName (exit $LASTEXITCODE)" }
    Write-Output "Passed: $LogName"
}
Push-Location $leanVerificationRoot
try {
    Invoke-LeanVerificationStep 'build.txt' @('build', '--wfail')
    Invoke-LeanVerificationStep 'challenge.txt' @('build', 'Challenge')
    Invoke-LeanVerificationStep 'axioms.txt' @('env', 'lean', '-DwarningAsError=true', (Join-Path $leanVerificationRoot 'Audit.lean'))
    Invoke-LeanVerificationStep 'pdf-statement.txt' @('env', 'lean', '-DwarningAsError=true', (Join-Path $leanVerificationRoot 'StatementAudit_v1.lean'))
    Invoke-LeanVerificationStep 'solution.txt' @('env', 'lean', '-DwarningAsError=true', (Join-Path $leanVerificationRoot 'Solution.lean'))
    Write-Output 'Verified the implemented lemmas and their axiom dependencies.'
    Write-Output 'Verified the transcribed PDF definitions and theorem consequences.'
    Write-Output 'Verified the Palomar Solution and its axiom/safety audit; Challenge has four authorized statement holes.'
    Write-Output 'This does not certify the full period theorem; see STATUS.md.'
}
finally {
    Pop-Location
}
