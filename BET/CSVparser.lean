import Lean

import BET
namespace BET

open IO

/-- Parse a string into a Float; returns none on failure. -/
def parseFloat? (s0 : String) : Option Float := Id.run do
  -- trimAscii : String → String.Slice
  let s : String := (String.trimAscii s0).toString
  if s.isEmpty then return none
  let isNeg : Bool := s.startsWith "-"
  let s : String := if isNeg then (s.drop 1).toString else s
  if s.isEmpty then return none
  let parts : List String := String.splitOn s "."
  match parts with
  | [intStr] =>
      let some intVal ← String.toNat? intStr | return none
      let v := intVal.toFloat
      return if isNeg then some (-v) else some v
  | [intStr, fracStr] =>
      if intStr.isEmpty && fracStr.isEmpty then
        return none
      let intVal : Nat := (String.toNat? intStr).getD 0
      let fracVal : Nat := (String.toNat? fracStr).getD 0
      let fracPow : Float := 10.0 ^ (fracStr.length.toFloat)
      let v : Float := intVal.toFloat + (fracVal.toFloat / fracPow)
      return if isNeg then some (-v) else some v
  | _ => return none

/-- Convert a string to Float; returns 0.0 on failure. -/
def stringToFloat (s : String) : Float :=
  match parseFloat? s with
  | some f => f
  | none   => 0.0

/- ===== Line / CSV parsing ===== -/

/-- Parse one CSV row "p,n" into `(p, n)` as floats. -/
def parseLineToPair (line0 : String) : Option (Float × Float) :=
  let line : String := line0
  match String.splitOn line "," with
  | [p, n] => some (stringToFloat p, stringToFloat n)
  | _ => none

/--
Parse a full CSV file into raw pairs `(p,n)`.
Drops the first line (header).
Skips invalid rows.
-/
def parseCSV (lines : Array String) : List (Float × Float) :=
  (lines.drop 1).foldl (fun acc line =>
    match parseLineToPair line with
    | some pr => pr :: acc
    | none    => acc
  ) [] |>.reverse

/-- Prompt user for CSV file path, read it, and parse into raw `(p,n)` pairs. -/
def promptCSV : IO (List (Float × Float)) := do
  let stdout ← IO.getStdout
  let stdin  ← IO.getStdin
  stdout.putStr "Enter CSV file path: "
  let path ← stdin.getLine
  let contents ← IO.FS.readFile (String.trimAscii path).toString
  let lines := (String.splitOn contents "\n").toArray
  return parseCSV lines

end BET
