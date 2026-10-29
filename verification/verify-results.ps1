# Independent re-verification of the Lean agent's results. Lives in tools\ (not writable by the agent).
# Usage: powershell -File tools\verify-results.ps1 [-Force] [-Name ramsey33]
param([switch]$Force, [string]$Name = '*')
$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
$resDir = Join-Path $root 'results'
$logDir = Join-Path $root 'logs'
$csv = Join-Path $logDir 'verified.csv'
$reportPath = Join-Path $logDir 'verify-report.txt'
$fc = $env:FC_CHECKOUT   # path to a formal-conjectures checkout with built Mathlib
$tmp = Join-Path $env:TEMP 'lean-verify'
New-Item -ItemType Directory -Force -Path $tmp | Out-Null
$env:PATH += ";$env:USERPROFILE\.elan\bin"
$utf8 = New-Object System.Text.UTF8Encoding $false

# Appended to a temp copy: audit axioms of every declaration made in the file.
# '@2@' is replaced by the subscript two (U+2082) so that this script stays pure ASCII.
$audit = @'

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env <- getEnv
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  for (n, _) in env.constants.map@2@.toList do
    unless n.isInternal do
      let axs <- liftCoreM (collectAxioms n)
      let bad := axs.filter fun a => !(ok.contains a)
      unless bad.isEmpty do logInfo m!"BADAXIOM {n}: {bad}"
  logInfo "AXIOMCHECK-DONE"
'@
$audit = $audit.Replace('@2@', [string][char]0x2082)

$forbidden = @(
  '\bsorry\b', '\badmit\b', '\bsorryAx\b', '\bnative_decide\b', '\bofReduceBool\b', '\btrustCompiler\b',
  '(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?axiom\b', '\bunsafe\b', '\bimplemented_by\b', '\bextern\b',
  '\bmacro\b', '\bmacro_rules\b', '\bsyntax\b', '\belab\b', '\brun_cmd\b', '\brun_elab\b', '\brun_meta\b',
  '\binitialize\b', '#eval', '#exit', '\baddDecl\b'
)

function Strip-Comments([string]$s) {
  $s = [regex]::Replace($s, '(?s)/-.*?-/', ' ')
  [regex]::Replace($s, '--[^\r\n]*', ' ')
}
function Norm([string]$s) { ([regex]::Replace($s, '\s+', ' ')).Trim() }
function Invoke-Lean([string]$path, [int]$limitMs = 600000) {
  Push-Location $fc
  try {
    $out = Join-Path $tmp 'out.txt'
    $p = Start-Process -FilePath lake -ArgumentList 'env', 'lean', "`"$path`"" -NoNewWindow -PassThru -RedirectStandardOutput $out -RedirectStandardError "$out.err"
    $null = $p.Handle
    $done = $p.WaitForExit($limitMs)
    if (-not $done) { taskkill /T /F /PID $p.Id | Out-Null }
    $text = (@(Get-Content $out, "$out.err" -ErrorAction SilentlyContinue) -join "`n")
    [pscustomobject]@{ TimedOut = (-not $done); ExitCode = $(if ($done) { $p.ExitCode } else { -1 }); Text = $text }
  } finally { Pop-Location }
}

# Index of the checkout: short declaration name -> file texts containing it.
Write-Host 'Indexing checkout...'
$index = @{}
foreach ($cf in Get-ChildItem (Join-Path $fc 'FormalConjectures*') -Recurse -Filter *.lean) {
  $t = Strip-Comments ([IO.File]::ReadAllText($cf.FullName))
  foreach ($m in [regex]::Matches($t, "\b(?:theorem|lemma|def|abbrev)\s+([\w.'\u00AB\u00BB]+)")) {
    $short = ($m.Groups[1].Value -split '\.')[-1]
    if (-not $index.ContainsKey($short)) { $index[$short] = New-Object System.Collections.Generic.List[string] }
    if (-not $index[$short].Contains($t)) { $index[$short].Add($t) }
  }
}

function Get-Stmt([string]$text, [string]$kind, [string]$short) {
  $e = [regex]::Escape($short)
  if ($kind -eq 'def') {
    $m = [regex]::Match($text, "(?s)\b(?:def|abbrev)\s+(?:[\w.'\u00AB\u00BB]*\.)?$e\b.*?(?:\r?\n\s*\r?\n|\z)")
  } else {
    $m = [regex]::Match($text, "(?s)\b(?:theorem|lemma)\s+(?:[\w.'\u00AB\u00BB]*\.)?$e\b(.*?):=")
  }
  if ($m.Success) { Norm $m.Value } else { $null }
}

$known = @{}
if (Test-Path $csv) { Import-Csv $csv | ForEach-Object { $known[$_.name] = $_ } }
$report = New-Object System.Collections.Generic.List[string]
$report.Add("Verification run $(Get-Date -Format s)")

foreach ($f in Get-ChildItem $resDir -Filter "$Name.lean") {
  $hash = (Get-FileHash $f.FullName -Algorithm SHA256).Hash
  $k = $known[$f.BaseName]
  if (-not $Force -and $k -and $k.hash -eq $hash -and $k.status -eq 'PASS') { continue }
  $raw = [IO.File]::ReadAllText($f.FullName)
  # Full `import Mathlib` needs 2.5 min warm / 8 min cold just to load: give it 30 min, others 10.
  $limitMs = $(if ($raw -match '(?m)^import Mathlib\s*$') { 1800000 } else { 600000 })
  $clean = Strip-Comments $raw
  $status = 'PASS'; $notes = New-Object System.Collections.Generic.List[string]

  # 1. static scan
  foreach ($pat in $forbidden) { if ($clean -match $pat) { $status = 'FAIL-STATIC'; $notes.Add("forbidden: $pat") } }

  # 2+3. compile with axiom audit
  if ($status -eq 'PASS') {
    $copy = Join-Path $tmp ($f.BaseName + '.lean')
    [IO.File]::WriteAllText($copy, $raw + $audit, $utf8)
    $r = Invoke-Lean $copy $limitMs
    if ($r.TimedOut) { $status = 'FAIL-COMPILE'; $notes.Add("timeout $($limitMs / 60000) min") }
    elseif ($r.ExitCode -ne 0 -or $r.Text -match '(?m):\s*error' -or $r.Text -match 'sorry') {
      $status = 'FAIL-COMPILE'; $notes.Add(($r.Text -split "`n" | Select-Object -First 8) -join ' | ')
    } elseif ($r.Text -match 'BADAXIOM' -or $r.Text -notmatch 'AXIOMCHECK-DONE') {
      $status = 'FAIL-AXIOMS'; $notes.Add(($r.Text -split "`n" | Where-Object { $_ -match 'BADAXIOM' } | Select-Object -First 5) -join ' | ')
      if ($r.Text -notmatch 'AXIOMCHECK-DONE') { $notes.Add('axiom audit did not run (snippet failed?)') }
    }
  }

  # 4. fidelity vs checkout (review aid, never a hard fail)
  $fid = 'SAME'
  $decls = [regex]::Matches($clean, "(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev)\s+([^\s:({\[]+)")
  foreach ($d in $decls) {
    $kind = $(if ($d.Groups[1].Value -in 'def', 'abbrev') { 'def' } else { 'thm' })
    $short = ($d.Groups[2].Value -split '\.')[-1]
    if (-not $index.ContainsKey($short)) { continue }
    $mine = Get-Stmt $clean $kind $short
    $same = $false
    foreach ($src in $index[$short]) { if ((Get-Stmt $src $kind $short) -eq $mine) { $same = $true } }
    if (-not $same) {
      $fid = 'REVIEW'
      $theirs = Get-Stmt $index[$short][0] $kind $short
      $notes.Add("DIFF $short`n  agent : $($mine.Substring(0, [Math]::Min(400, $mine.Length)))`n  source: $(if ($theirs) { $theirs.Substring(0, [Math]::Min(400, $theirs.Length)) } else { '?' })")
    }
  }

  $report.Add("[$status/$fid] $($f.BaseName)")
  foreach ($n in $notes) { $report.Add("    $n") }
  $known[$f.BaseName] = [pscustomobject]@{ name = $f.BaseName; hash = $hash; status = $status; fidelity = $fid; time = (Get-Date -Format s) }
}

$known.Values | Export-Csv $csv -NoTypeInformation -Encoding utf8
$report | Set-Content $reportPath -Encoding utf8
$report