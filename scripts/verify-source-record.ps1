# Read-only check that the delivered files match this verification snapshot.
# This does not replace Lake or the Lean axiom audit after a source change.
[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
$fjPublicationRoot = [IO.Path]::GetFullPath((Split-Path -Parent $PSScriptRoot))
$fjRecord = Get-Content -LiteralPath (Join-Path $fjPublicationRoot 'verification/source-sha256.json') -Raw | ConvertFrom-Json
$fjChecked = 0
foreach ($fjEntry in $fjRecord.files.PSObject.Properties) {
    $fjTarget = [IO.Path]::GetFullPath((Join-Path $fjPublicationRoot $fjEntry.Name))
    if (-not $fjTarget.StartsWith($fjPublicationRoot + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Recorded path escapes the publication: $($fjEntry.Name)"
    }
    $fjHash = (Get-FileHash -LiteralPath $fjTarget -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($fjHash -ne $fjEntry.Value) { throw "Source hash mismatch: $($fjEntry.Name)" }
    $fjChecked++
}
Write-Output "Matched all $fjChecked recorded publication source/data/script/document hashes."

