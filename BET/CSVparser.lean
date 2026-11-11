import BET.DecimalParser

/-!
# CSV reader for LeanBET
Reads a two-column isotherm file `relative pressure, quantity adsorbed`.
-/

namespace BET

open BET.Parse

/-- Kept for compatibility: read one number, `none` if it is not valid. -/
def parseFloat? (s : String) : Option Float := (parseNumber s).toOption

def isBlankLine (l : String) : Bool := (String.trimAscii l).toString.isEmpty

/-- Read one data row `p,n` (no BET rules yet). -/
def parseRow (lineNo : Nat) (line : String) : Except String (Float × Float) :=
  match line.splitOn "," with
  | [p, n] =>
    match parseNumber p with
    | .error e => .error s!"line {lineNo}: relative pressure is {e}"
    | .ok pv =>
      match parseNumber n with
      | .error e => .error s!"line {lineNo}: quantity adsorbed is {e}"
      | .ok nv => .ok (pv, nv)
  | fs => .error s!"line {lineNo}: expected 2 comma-separated values, found {fs.length}"

/-- BET rule for a single point: `0 < p < 1` and `n > 0`. -/
def betPointOk (pt : Float × Float) : Bool :=
  decide (0.0 < pt.1) && decide (pt.1 < 1.0) && decide (0.0 < pt.2)

/-- Read one data row and check the single-point BET rule. -/
def readPoint (lineNo : Nat) (line : String) : Except String (Float × Float) :=
  match parseRow lineNo line with
  | .error e => .error e
  | .ok pt =>
    if betPointOk pt then .ok pt
    else .error s!"line {lineNo}: need 0 < p < 1 and n > 0, got p = {pt.1}, n = {pt.2}"

/-- Read all data lines.  `lineNo` is the file line number of the first one. -/
def parseDataLines (lineNo : Nat) : List String → Except String (List (Float × Float))
  | [] => .ok []
  | l :: ls =>
    if isBlankLine l then parseDataLines (lineNo + 1) ls
    else
      match readPoint lineNo l with
      | .error e => .error e
      | .ok pt =>
        match parseDataLines (lineNo + 1) ls with
        | .error e => .error e
        | .ok pts => .ok (pt :: pts)

/-- `p` strictly increases from each point to the next. -/
def pressuresIncreasing : List (Float × Float) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && pressuresIncreasing (b :: rest)
  | _ => true

def stripBOM (s : String) : String :=
  if s.startsWith "\uFEFF" then (s.drop 1).toString else s

/-- The data points of a file's lines.  The first line is a header (and is
dropped) exactly when it is not itself a valid data row. -/
def csvBody (lines : List String) : Except String (List (Float × Float)) :=
  match lines with
  | [] => .ok []
  | first :: rest =>
    match parseRow 1 first with
    | .ok _    => parseDataLines 1 (first :: rest)   -- no header line
    | .error _ => parseDataLines 2 rest              -- line 1 is a header

/-- Read the whole text of a CSV file. -/
def parseCSVContents (contents : String) : Except String (List (Float × Float)) :=
  match csvBody ((stripBOM contents).splitOn "\n") with
  | .error e => .error e
  | .ok pts =>
    if pressuresIncreasing pts then .ok pts
    else .error "relative pressures must strictly increase from row to row"

/-- Ask for a CSV path, read it, and return its `(p, n)` points.
Any problem in the file stops the program with a message naming the line. -/
def promptCSV : IO (List (Float × Float)) := do
  let stdout ← IO.getStdout
  let stdin  ← IO.getStdin
  stdout.putStr "Enter CSV file path: "
  let path ← stdin.getLine
  let path := (String.trimAscii path).toString
  let contents ← IO.FS.readFile path
  match parseCSVContents contents with
  | .ok pts => return pts
  | .error e => throw (IO.userError s!"CSV error in {path}: {e}")

end BET
