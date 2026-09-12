# Recreate the pinned Windows x64 Lean environment entirely in this project.
[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'lean-env.ps1')
Push-Location $leanProjectRoot
try {
    foreach ($leanPrerequisite in @('git.exe', 'curl.exe')) {
        if (-not (Get-Command $leanPrerequisite -ErrorAction SilentlyContinue)) {
            throw "Required existing tool is not on PATH: $leanPrerequisite"
        }
    }

    # Official release: https://github.com/leanprover/elan/releases/tag/v4.2.4
    $elanVersion = '4.2.4'
    $elanArchiveHash = 'fad2e980a191c15884cc1d80d170ffc5fa84f3774541020145b66d1a644c6111'
    $elanExe = Join-Path $env:ELAN_HOME 'bin/elan.exe'
    if (-not (Test-Path -LiteralPath $elanExe)) {
        $elanDownloads = Join-Path $leanProjectRoot '.cache/downloads'
        New-Item -ItemType Directory -Force -Path $elanDownloads | Out-Null
        $elanArchive = Join-Path $elanDownloads "elan-v$elanVersion-windows-x86_64.zip"
        if (-not (Test-Path -LiteralPath $elanArchive)) {
            & curl.exe --fail --location --silent --show-error --retry 3 --connect-timeout 30 --max-time 300 `
                "https://github.com/leanprover/elan/releases/download/v$elanVersion/elan-x86_64-pc-windows-msvc.zip" `
                --output $elanArchive
            if ($LASTEXITCODE -ne 0) { throw 'Elan download failed.' }
        }
        if ((Get-FileHash -Algorithm SHA256 -LiteralPath $elanArchive).Hash.ToLowerInvariant() -ne $elanArchiveHash) {
            throw "Elan archive checksum mismatch: $elanArchive"
        }
        $elanUnpack = Join-Path $elanDownloads "elan-v$elanVersion"
        Expand-Archive -LiteralPath $elanArchive -DestinationPath $elanUnpack -Force
        & (Join-Path $elanUnpack 'elan-init.exe') -y --no-modify-path --default-toolchain none
        if ($LASTEXITCODE -ne 0) { throw 'Project-local Elan installation failed.' }
    }
    $elanInstalledVersion = & $elanExe --version
    if ($LASTEXITCODE -ne 0 -or $elanInstalledVersion -notmatch "^elan $([regex]::Escape($elanVersion))( |$)") {
        throw "Unexpected local Elan version; refusing to replace it: $elanInstalledVersion"
    }
    Write-Output $elanInstalledVersion

    $leanPinnedToolchain = (Get-Content -Raw -LiteralPath 'lean-toolchain').Trim()
    & $elanExe toolchain install $leanPinnedToolchain
    if ($LASTEXITCODE -ne 0) { throw 'Lean toolchain installation failed.' }
    & lean --version
    if ($LASTEXITCODE -ne 0) { throw 'Lean compiler check failed.' }
    & lake --version
    if ($LASTEXITCODE -ne 0) { throw 'Lake check failed.' }

    # Generate the manifest only on first setup. Later runs retain its exact pins.
    if (-not (Test-Path -LiteralPath 'lake-manifest.json')) {
        $leanPreviousCacheHook = $env:MATHLIB_NO_CACHE_ON_UPDATE
        try {
            $env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
            & lake update
            if ($LASTEXITCODE -ne 0) { throw 'Lake dependency resolution failed.' }
        }
        finally {
            $env:MATHLIB_NO_CACHE_ON_UPDATE = $leanPreviousCacheHook
        }
    }
    & lake exe cache get
    if ($LASTEXITCODE -ne 0) { throw 'Mathlib precompiled cache download failed.' }
    & (Join-Path $PSScriptRoot 'verify-lean.ps1')
}
finally {
    Pop-Location
}
