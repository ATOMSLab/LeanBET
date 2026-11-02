/-!
# DecimalParser — a number reader with a written-down specification

This file turns the text of one CSV field (e.g. `"9.59E-05"`) into a number.
It is split into two stages on purpose:

1. **Text → exact decimal** (`parseDecimal`).  The result is an exact value
   `±mant · 10^exp` built from whole numbers only, so Lean can prove facts
   about it.  The proofs are in `BET/ParserSoundness.lean`.
2. **Exact decimal → `Float`** (`Decimal.toFloat`).  The rounding itself is
   done with exact whole-number arithmetic, but Lean's `Float` has no
   definition inside Lean's logic, so this last step cannot be proved; it is
   checked instead by comparing bit-for-bit with Python's `float()`.

## The accepted format (the specification)

A number is, in this order:
* an optional sign `+` or `-`,
* zero or more digits `0-9`,
* optionally a `.` followed by zero or more digits,
* optionally an exponent: `e` or `E`, an optional sign, and one or more digits,

with at least one digit before the exponent.  Nothing else is allowed: no
second `.`, no `.` in the exponent, no underscores, no `nan`/`inf`.

So `5.65E-05`, `5.65e-05`, `5.65E-5`, `5.65E+05`, `5.`, `.5` are accepted and
`5.65.E-05`, `5.65E-5.`, `E-05`, `5.65E`, `5.6_5`, `nan` are rejected.
-/

namespace BET.Parse

/-- An exact decimal number `(-1)^neg · mant · 10^exp`.  No rounding. -/
structure Decimal where
  neg  : Bool
  mant : Nat
  exp  : Int
  deriving DecidableEq, Repr

/-- Do two exact decimals denote the same number?  (`565·10⁻⁷ = 5650·10⁻⁸`.) -/
def Decimal.sameValue (a b : Decimal) : Bool :=
  let m := min a.exp b.exp
  let ma := a.mant * 10 ^ (a.exp - m).toNat
  let mb := b.mant * 10 ^ (b.exp - m).toNat
  ma == mb && (ma == 0 || a.neg == b.neg)

/-! ## 1. Specification: what a valid number looks like, and what it means -/

inductive Sign where
  | none
  | plus
  | minus
  deriving DecidableEq, Repr

def Sign.render : Sign → List Char
  | .none  => []
  | .plus  => ['+']
  | .minus => ['-']

structure Exponent where
  marker : Char
  sign   : Sign
  digits : List Char
  deriving DecidableEq, Repr

/-- The pieces of a number as written: sign, integer digits, optional
fractional digits (`some ds` means a `.` followed by `ds`), optional exponent. -/
structure NumText where
  sign      : Sign
  intDigits : List Char
  frac      : Option (List Char)
  exponent  : Option Exponent
  deriving DecidableEq, Repr

def AllDigits (ds : List Char) : Prop := ∀ c ∈ ds, c.isDigit = true

def fracRender : Option (List Char) → List Char
  | none    => []
  | some ds => '.' :: ds

def expRender : Option Exponent → List Char
  | none   => []
  | some e => e.marker :: (e.sign.render ++ e.digits)

/-- The exact characters a `NumText` is written as. -/
def NumText.render (t : NumText) : List Char :=
  t.sign.render ++ (t.intDigits ++ (fracRender t.frac ++ expRender t.exponent))

/-- The rules a well-formed number must follow (the grammar above). -/
structure NumText.WF (t : NumText) : Prop where
  intDigits_ok      : AllDigits t.intDigits
  frac_ok           : ∀ ds, t.frac = some ds → AllDigits ds
  mantissa_nonempty : t.intDigits ≠ [] ∨ ∃ ds, t.frac = some ds ∧ ds ≠ []
  exp_ok            : ∀ e, t.exponent = some e →
                        (e.marker = 'e' ∨ e.marker = 'E') ∧ AllDigits e.digits ∧ e.digits ≠ []

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- `digitsVal ['9','5','9'] = 959`. -/
def digitsVal (ds : List Char) : Nat := ds.foldl (fun acc c => 10 * acc + digitVal c) 0

def NumText.fracDigits (t : NumText) : List Char := t.frac.getD []

def NumText.expVal (t : NumText) : Int :=
  match t.exponent with
  | none   => 0
  | some e => if e.sign = .minus then -(digitsVal e.digits : Int) else (digitsVal e.digits : Int)

/-- What the text means: all mantissa digits as one whole number, and the
exponent shifted by the number of fractional digits.
`"9.59E-05"` means `959 · 10^(-5-2) = 959 · 10⁻⁷`. -/
def NumText.value (t : NumText) : Decimal :=
  { neg  := t.sign == .minus
    mant := digitsVal (t.intDigits ++ t.fracDigits)
    exp  := t.expVal - (t.fracDigits.length : Int) }

/-! ## 2. The parser (stage 1: text → exact decimal) -/

def parseSign : List Char → Sign × List Char
  | []     => (.none, [])
  | c :: r => if c = '+' then (.plus, r) else if c = '-' then (.minus, r) else (.none, c :: r)

/-- Split off the longest run of leading digits. -/
def spanDigits : List Char → List Char × List Char
  | []     => ([], [])
  | c :: r => if c.isDigit then (c :: (spanDigits r).1, (spanDigits r).2) else ([], c :: r)

def parseFrac : List Char → Option (List Char) × List Char
  | []     => (none, [])
  | c :: r => if c = '.' then (some (spanDigits r).1, (spanDigits r).2) else (none, c :: r)

/-- The exponent must use up the rest of the text exactly. -/
def parseExp : List Char → Option (Option Exponent)
  | []     => some none
  | m :: r =>
    if m = 'e' ∨ m = 'E' then
      if (spanDigits (parseSign r).2).1 ≠ [] ∧ (spanDigits (parseSign r).2).2 = [] then
        some (some ⟨m, (parseSign r).1, (spanDigits (parseSign r).2).1⟩)
      else none
    else none

def mantissaOk (ip : List Char) (fr : Option (List Char)) : Bool :=
  !ip.isEmpty || (match fr with
                  | some ds => !ds.isEmpty
                  | none    => false)

def parseText (cs : List Char) : Option NumText :=
  match parseExp (parseFrac (spanDigits (parseSign cs).2).2).2 with
  | none    => none
  | some ex =>
    if mantissaOk (spanDigits (parseSign cs).2).1 (parseFrac (spanDigits (parseSign cs).2).2).1 then
      some ⟨(parseSign cs).1, (spanDigits (parseSign cs).2).1,
            (parseFrac (spanDigits (parseSign cs).2).2).1, ex⟩
    else none

/-- Stage 1: text → exact decimal, or `none` if the text is not a valid number. -/
def parseDecimal (cs : List Char) : Option Decimal := (parseText cs).map NumText.value

/-! ## 3. Stage 2: exact decimal → `Float` (tested, not proved) -/

/-- The `Float` nearest to the fraction `a / b` (`b > 0`), ties to even —
the rounding rule of IEEE-754, Python's `float()` and C's `strtod`.

All the work is done with exact whole numbers: choose a power of two `2^k`
so that `q = ⌊a / (b·2^k)⌋` has 53 bits (fewer for subnormals), round `q`
using the remainder, then return `q · 2^k`.  Both `q.toFloat` (since
`q ≤ 2^53`) and the scaling by `2^k` are exact, so the only rounding is the
one made explicitly here. -/
def ratToFloat (a b : Nat) : Float :=
  if a = 0 then 0.0 else
  let k0 : Int := (a.log2 : Int) - (b.log2 : Int) - 52
  let divAt (k : Int) : Nat × Nat × Nat :=   -- (quotient, remainder, denominator)
    if 0 ≤ k then (a / (b * 2 ^ k.toNat), a % (b * 2 ^ k.toNat), b * 2 ^ k.toNat)
    else (a * 2 ^ (-k).toNat / b, a * 2 ^ (-k).toNat % b, b)
  -- a/b lies in (2^(k0+51), 2^(k0+53)); step down once if q has only 52 bits
  let k1 : Int := if (divAt k0).1 < 2 ^ 52 then k0 - 1 else k0
  let k  : Int := if k1 < -1074 then -1074 else k1        -- subnormal range
  let (q, r, den) := divAt k
  let q := if 2 * r > den ∨ (2 * r = den ∧ q % 2 = 1) then q + 1 else q
  q.toFloat.scaleB k

/-- Round an exact decimal to the nearest `Float` (see `ratToFloat`). -/
def Decimal.toFloat (d : Decimal) : Float :=
  let m := d.mant
  -- number of decimal digits of `m`, used to short-cut absurd exponents
  -- (e.g. `9E4249496719`) instead of computing gigantic powers of ten
  let nd : Int := (Nat.repr m).length
  let v : Float :=
    if m = 0 then 0.0
    else if nd - 1 + d.exp > 309 then 1.0 / 0.0     -- ≥ 10^310: overflows to ∞ (rejected later)
    else if nd + d.exp < -330 then 0.0              -- < 10^-330: rounds to 0
    else if 0 ≤ d.exp then ratToFloat (m * 10 ^ d.exp.toNat) 1
    else ratToFloat m (10 ^ (-d.exp).toNat)
  if d.neg then -v else v

def isFiniteFloat (x : Float) : Bool := !x.isNaN && !x.isInf

/-- Read one CSV field as a `Float`.  Surrounding whitespace (including the
`\r` of Windows line endings) is ignored.  Anything outside the format above,
or too large for a `Float`, is an error — never a silent default. -/
def parseNumber (s : String) : Except String Float :=
  let t := (String.trimAscii s).toString
  match parseDecimal t.toList with
  | none   => .error s!"not a valid number: {s.quote}"
  | some d =>
    let x := d.toFloat
    if isFiniteFloat x then .ok x else .error s!"number too large for Float: {s.quote}"

end BET.Parse
