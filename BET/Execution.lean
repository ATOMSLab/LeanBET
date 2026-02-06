import Mathlib
import BET.Instance
import BET.CSVparser
import BET.Function

open BET

set_option linter.style.emptyLine false

/-- Convert raw `(p,n)` pairs from CSV into an isotherm of `Point Float`. -/
def pairsToIsotherm (rows : List (Float × Float)) : Isotherm Float :=
  rows.map (fun (pn : Float × Float) => { p := pn.1, n := pn.2 })

def main : IO Unit := do
  -- 1) read raw CSV data
  let rows : List (Float × Float) ← BET.promptCSV
  if rows.isEmpty then
    IO.println "Error: No valid (p,n) rows found in the CSV file."
    return ()

  -- 2) build isotherm for the BETSI pipeline
  let iso : Isotherm Float := pairsToIsotherm rows

  -- 3) configure filters
  let cfg : BETSIFilter Float := {
    minPts := 10
    minR2 := 0.9
    maxPercError := 20.0 }

  -- 4) run
  let allWins := allWindows iso
  let results := allBETSIpassing iso cfg

  IO.println s!"Total candidate fits (≥ 2 points): {allWins.length}"
  IO.println s!"Total fits passing BETSI criteria (Rouq 1–4; minPts > {cfg.minPts};
    R² ≥ {cfg.minR2}; error ≤ {cfg.maxPercError}%): {results.length}"

  -- 5) top fits by lowest % error
  let sorted := sortBy (fun a b => a.pcError < b.pcError) results
  IO.println "\nTop fits by lowest % error (across all passing fits):"
  for r in sorted.take 49 do
    IO.println (printBETSIResult r)
    IO.println ""

  -- 6) knee-best
  match kneeBest results with
  | some best =>
      IO.println "\nBETSI knee-best selection:"
      IO.println (printBETSIResult best)
      IO.println ""
      IO.println (printSummary best)
  | none =>
      IO.println "No valid BET fit found."


--lake env lean --run BET/Execution.lean
