param([string]$WorkspaceRoot, [string]$TexBin)
$ErrorActionPreference = 'Stop'
$fjPublication = Split-Path -Parent $PSScriptRoot
if (-not $WorkspaceRoot) { $WorkspaceRoot = $fjPublication }
$fjWorkspace = (Resolve-Path -LiteralPath $WorkspaceRoot).Path
$fjBuild = Join-Path $fjWorkspace 'build/fourier-jacobi-core-statement-v1'
$fjConfig = Join-Path $fjWorkspace '.config/miktex-formalization-documents'
$fjData = Join-Path $fjWorkspace '.local/miktex-formalization-documents'
$fjTemp = Join-Path $fjWorkspace '.tmp/miktex-formalization-documents'
$fjLogs = Join-Path $fjBuild 'miktex-logs'
if (-not $TexBin) {
    $TexBin = Join-Path ([Environment]::GetFolderPath('LocalApplicationData')) 'Programs/MiKTeX/miktex/bin/x64'
}
if (-not (Test-Path -LiteralPath (Join-Path $TexBin 'pdflatex.exe'))) {
    throw 'A suitable installed pdfLaTeX is required; supply -TexBin. No installation is attempted.'
}
foreach ($fjDir in @($fjBuild,$fjConfig,$fjData,$fjTemp,$fjLogs)) {
    $fjAbsolute = [IO.Path]::GetFullPath($fjDir)
    if (-not $fjAbsolute.StartsWith($fjWorkspace + [IO.Path]::DirectorySeparatorChar, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Writable TeX path escapes workspace: $fjAbsolute"
    }
    New-Item -ItemType Directory -Force -Path $fjDir | Out-Null
    if ((Get-Item -LiteralPath $fjDir).Attributes -band [IO.FileAttributes]::ReparsePoint) {
        throw "Inspect redirected writable TeX path before compiling: $fjDir"
    }
}
$env:MIKTEX_USERCONFIG = $fjConfig
$env:MIKTEX_USERDATA = $fjData
$env:MIKTEX_LOG_DIR = $fjLogs
$env:MIKTEX_USERLOGDIRECTORY = $fjLogs
$env:TEXMFVAR = $fjData
$env:TEXMFCONFIG = $fjConfig
$env:TEXMFHOME = Join-Path $fjData 'texmf'
$env:TEXMFCACHE = $fjData
$env:TEMP = $fjTemp
$env:TMP = $fjTemp
$env:TMPDIR = $fjTemp
$env:PATH = "$TexBin;$env:PATH"
Push-Location $fjPublication
try {
    for ($fjPass = 1; $fjPass -le 3; $fjPass++) {
        & (Join-Path $TexBin 'pdflatex.exe') --disable-installer -no-shell-escape `
          -interaction=nonstopmode -halt-on-error -file-line-error -recorder `
          "-output-directory=$fjBuild" formalized_theorem_v1.tex *> (Join-Path $fjBuild "pass-$fjPass.txt")
        if ($LASTEXITCODE -ne 0) {
            Get-Content -LiteralPath (Join-Path $fjBuild "pass-$fjPass.txt") -Tail 65
            throw "pdfLaTeX failed on pass $fjPass"
        }
    }
    Copy-Item -LiteralPath (Join-Path $fjBuild 'formalized_theorem_v1.pdf') -Destination $fjPublication
    Write-Output 'Built formalized_theorem_v1.pdf; the statement implication and visual audits are separate checks.'
} finally { Pop-Location }
