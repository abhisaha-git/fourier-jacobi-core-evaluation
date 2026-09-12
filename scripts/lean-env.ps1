# Process-only environment for the project-local Windows Lean installation.
$leanProjectRoot = Split-Path -Parent $PSScriptRoot
$leanLocalEnvironment = @{
    ELAN_HOME = Join-Path $leanProjectRoot '.tools/elan'
    MATHLIB_CACHE_DIR = Join-Path $leanProjectRoot '.cache/mathlib'
    LAKE_CACHE_DIR = Join-Path $leanProjectRoot '.cache/lake'
    XDG_CACHE_HOME = Join-Path $leanProjectRoot '.cache'
    XDG_CONFIG_HOME = Join-Path $leanProjectRoot '.config'
    XDG_DATA_HOME = Join-Path $leanProjectRoot '.local/share'
    TEMP = Join-Path $leanProjectRoot '.tmp'
    TMP = Join-Path $leanProjectRoot '.tmp'
    TMPDIR = Join-Path $leanProjectRoot '.tmp'
}
foreach ($leanSetting in $leanLocalEnvironment.GetEnumerator()) {
    New-Item -ItemType Directory -Force -Path $leanSetting.Value | Out-Null
    [Environment]::SetEnvironmentVariable($leanSetting.Key, $leanSetting.Value, 'Process')
}
New-Item -ItemType Directory -Force -Path (Join-Path $leanProjectRoot '.config/lake') | Out-Null
$env:LAKE_CONFIG = Join-Path $leanProjectRoot '.config/lake/config.toml'
$leanElanBin = Join-Path $env:ELAN_HOME 'bin'
if (($env:PATH -split ';') -notcontains $leanElanBin) {
    $env:PATH = "$leanElanBin;$env:PATH"
}
# Pass Git settings to child processes without changing any Git configuration file.
$leanGitCount = 0
if ($env:GIT_CONFIG_COUNT) { $leanGitCount = [int]$env:GIT_CONFIG_COUNT }
foreach ($leanGitSetting in @(
    @{ Key = 'core.longpaths'; Value = 'true' }
    @{ Key = 'core.autocrlf'; Value = 'false' }
)) {
    [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$leanGitCount", $leanGitSetting.Key, 'Process')
    [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$leanGitCount", $leanGitSetting.Value, 'Process')
    $leanGitCount++
}
$env:GIT_CONFIG_COUNT = [string]$leanGitCount
