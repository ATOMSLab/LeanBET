import BET.LinReg
import BET.CSVCat
import Lean.Data.Json.Parser


def bufsize : USize := 20 * 1024
/- defines a 'block' size to read data in, in this case reading 20kb (1kb = 1024b, 1024b * 20) as one 'block' -/

open Lean in




def String.toFloat (s : String) : Except String Float :=
  match Json.Parser.num s.mkIterator with
  | Parsec.ParseResult.success _ res =>
    Except.ok <| Float.ofInt res.mantissa * 10 ^  (-1 * Float.ofNat res.exponent)
  | Parsec.ParseResult.error it err  => Except.error s!"{it} {err}"

def stringToFloatExceptHandler (input: Except String Float) : Float :=
  match input with
  | Except.ok α => α
  | Except.error _ => 0.0

def stringList.toFloats (xs : List String) (xsOut : List Float) : List Float :=
  match xs with
  | [] => xsOut
  | head :: tail =>
    let xsOut := xsOut.append [(stringToFloatExceptHandler (head.toFloat))]
    stringList.toFloats tail xsOut

partial def dump (stream : IO.FS.Stream) (outputArray : Array $ List $ Float) : IO Unit := do
  let buf ← stream.read bufsize
  -- buf now describes the output of stream.read bufsize
  if buf.isEmpty then
    let LRM := exceptHandler <| LRprocess outputArray[0]! outputArray[1]!
    IO.println (LRM)
    pure ()
  else
    --let stdout ← IO.getStdout
    -- stdout now describes the output of IO.getStdout
    let parse_result :=
    match String.fromUTF8? buf with
    | some str => parse str
    | none => Except.error "Failed to decode UTF-8 string"
    let parse_result := CSVParseExceptHandler (parse_result)
    -- Has type Array $ Array $ String
    let xData := stringList.toFloats (parse_result[0]!.toList) []
    let yData := stringList.toFloats (parse_result[1]!.toList) []
    let outputArray := outputArray.push xData
    let outputArray := outputArray.push yData
    -- this writes the 20kb 'block' that was just read by dump to the standard output.
    dump stream outputArray  /- this call is why dump is partial defined. stream can be larger than an argument, if
    stream were infite in size, dump would never terminate. 'partial' prevents Lean from requiring a
    proof that this function terminates. -/

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
-- converts a text file to a POSIX stream that can be passed to the actual function
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
    /- lines 24-28 handle the case where an incorrect/non-existent file name are passed to the function
    though I'm unsure why pure none is used for a blank return rather than pure ()-/
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    -- opens file in read mode and makes a handle out of it. The handle contains a file description
    pure (some (IO.FS.Stream.ofHandle handle))
    -- fills Stream structure with the correct IO action to work with file handles.

-- Stream structure looks like this:
/-
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
-/

def process (exitCode: UInt32) (args : List String) (outputArray : Array $ List $ Float) : IO UInt32 := do
  match args with -- there are three 'branches' available to this match, each one has an implicit 'do' block
  | [] => pure exitCode-- branch 1, nothing left to process, returns the exitCode
  | "-" :: args =>      -- branch 2, standard input given, instead of a file
    let stdin ← IO.getStdin
    let _ ← dump stdin outputArray -- takes one 'block' from standard input and writes it to standard output
    process exitCode args outputArray/- recursive process call, args is now one 'block' smaller → proves termination
                             so partial def is unnecessary -/

  | filename :: args => -- branch 3, an actual file is passed as input
    let stream ← fileStream (filename)
    match stream with
    | none => -- file can't be opened, set exit code to 1, file is skipped (i.e. not processed by dump)
      process 1 args outputArray
    | some stream => -- file can be opened, dump is called on a 'block', 'block' is processed, onto the next.
      let _ ← dump stream outputArray
      process exitCode args outputArray

def main (args : List String) : IO UInt32 :=
  match args with
  | ["help"] => process 0 ["helpfile.txt"] #[]
  | [] => process 0 ["-"] #[] -- no arguments provided, read from standard input
  | _ => process 0 args #[] -- arguments (filenames) provided, read from them in order
