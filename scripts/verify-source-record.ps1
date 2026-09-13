# Read-only check that the delivered files match this verification snapshot.
# This does not replace Lake or the Lean axiom audit after a source change.
[CmdletBinding()]
param([string]$Record = '')
$ErrorActionPreference = 'Stop'
$fjPublicationRoot = [IO.Path]::GetFullPath((Split-Path -Parent $PSScriptRoot))
if (-not $Record) {
    $Record = Join-Path $fjPublicationRoot 'verification/palomar-v1/source-check.json'
    if (-not (Test-Path -LiteralPath $Record)) {
        $Record = Join-Path $fjPublicationRoot 'verification/source-sha256.json'
    }
}
$fjRecord = Get-Content -LiteralPath $Record -Raw | ConvertFrom-Json
$fjChecked = 0
foreach ($fjEntry in $fjRecord.files.PSObject.Properties) {
    $fjTarget = [IO.Path]::GetFullPath((Join-Path $fjPublicationRoot $fjEntry.Name))
    if (-not $fjTarget.StartsWith($fjPublicationRoot + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Recorded path escapes the publication: $($fjEntry.Name)"
    }
    if ($fjRecord.normalized_text_files -contains $fjEntry.Name) {
        $fjText = [Text.Encoding]::UTF8.GetString([IO.File]::ReadAllBytes($fjTarget)).Replace("`r`n", "`n")
        $fjSha = [Security.Cryptography.SHA256]::Create()
        try {
            $fjHash = [BitConverter]::ToString($fjSha.ComputeHash([Text.Encoding]::UTF8.GetBytes($fjText))).Replace('-', '').ToLowerInvariant()
        } finally { $fjSha.Dispose() }
    } else {
        $fjHash = (Get-FileHash -LiteralPath $fjTarget -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    if ($fjHash -ne $fjEntry.Value) { throw "Source hash mismatch: $($fjEntry.Name)" }
    $fjChecked++
}
Write-Output "Matched all $fjChecked recorded publication source/data/script/document hashes."
