import Mathlib
import BET.Instance
open BET
namespace BET

open IO

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.missingEnd false
set_option linter.style.emptyLine false

/- ============================================================
   Types (polymorphic)
   ============================================================ -/

structure Point (α : Type) where
  p : α
  n : α
  deriving Repr

abbrev Isotherm (α : Type) := List (Point α)

structure BETFit (α : Type) where
  slope : α
  intercept : α
  rSquared : α
  nm : α
  c : α
  range : Nat × Nat
  nPoints : Nat
  deriving Repr

structure BETSIResult (α : Type) where
  fit     : BETFit α
  window  : List (Point α)
  p_nm    : α
  p_read  : α
  pcError : α
  deriving Repr

/- ============================================================
   Utilities (polymorphic where possible)
   ============================================================ -/

def insertBy {α} (cmp : α → α → Bool) : α → List α → List α
| x, [] => [x]
| x, y :: ys => if cmp x y then x :: y :: ys else y :: insertBy cmp x ys

def sortBy {α} (cmp : α → α → Bool) : List α → List α
| [] => []
| x :: xs => insertBy cmp x (sortBy cmp xs)

def fmin {α} [BETLike α] (a b : α) : α := if (a ≤ b) then a else b
def fmax {α} [BETLike α] (a b : α) : α := if (a ≤ b) then b else a

/-- Exact monotone nondecreasing check (proof-friendly; no tolerance). -/
def isMonotoneNondecreasingExact {α} [BETLike α] : List α → Bool
| [] => true
| [_] => true
| x :: y :: xs =>
  if x ≤ y then isMonotoneNondecreasingExact (y :: xs) else false


/-- Sum over a list (no BigOperators needed). -/
def listSum {α} [BETLike α] (xs : List α) : α :=
  xs.foldl (· + ·) BETLike.zero
  --xs.foldl (fun s t => s + t) BETLike.zero


/- ============================================================
   Windows (polymorphic)
   ============================================================ -/

def allWindows {α} (iso : Isotherm α) : List (Nat × Nat × List (Point α)) :=
  let n := iso.length
  if n < 2 then [] else
  (List.range n).flatMap fun start =>
    let stops := List.range (n - (start + 1)) |>.map (· + (start + 1))
    stops.map (fun stop =>
      (start, stop, iso.drop start |>.take (stop - start + 1)))

/- ============================================================
   BET linearization + regression (polymorphic)
   ============================================================ -/

def linearizeBET {α} [BETLike α] (pt : Point α) : Option (α × α) :=
  if Point.p pt < BETLike.one then
    let denom := Point.n pt * (BETLike.one - Point.p pt)
    if BET.isZero denom then none
    else some (Point.p pt, Point.p pt / denom)
  else
    none


def linearizeWindow {α} [BETLike α] (window : List (Point α)) : List (α × α) :=
  window.filterMap linearizeBET


/-- Least-squares linear regression returns (slope, intercept, r²). -/
def linearRegression {α} [BETLike α] (data : List (α × α)) : Option (α × α × α) := do
  if data.length < 2 then none else
    let n : α := BETLike.ofNat data.length
    let xs : List α := data.map Prod.fst
    let ys : List α := data.map Prod.snd
    let xBar : α := listSum xs / n
    let yBar : α := listSum ys / n
    let cov : α := listSum <| data.map (fun (x, y) => (x - xBar) * (y - yBar))
    let vr : α := listSum <| data.map (fun (x, _) => (x - xBar) ^ (2 : Nat))
    -- Degenerate case: zero variance in x
    if BET.isZero vr then none else
      let slope : α := cov / vr
      let intercept : α := yBar - slope * xBar
      let yHat : List α := xs.map (fun x => slope * x + intercept)
      let ssTot : α := listSum <| ys.map (fun y => (y - yBar) ^ (2 : Nat))
      let ssRes : α := listSum <| (List.zip ys yHat).map (fun (y, yh) => (y - yh) ^ (2 : Nat))
      -- Convention: if ssTot = 0, r² = 1
      let r2 : α := if BET.isZero ssTot then BETLike.one else BETLike.one - (ssRes / ssTot)
      some (slope, intercept, r2)



def fitWindow {α} [BETLike α]
  (window : List (Point α)) (range : Nat × Nat) : Option (BETFit α) := do
  let data := linearizeWindow window
  let (slope, intercept, r2) ← linearRegression data
  let denomNm := slope + intercept
  if BET.isZero denomNm then none
  else if BET.isZero intercept then none
  else
    let nm : α := BETLike.one / denomNm
    let c  : α := slope / intercept + BETLike.one
    some { slope, intercept, rSquared := r2, nm, c, range, nPoints := window.length }



/- ============================================================
   Float-only numeric hygiene (execution)
   ============================================================ -/

def isNaN (x : Float) : Bool := !(x == x)

def isFinite (x : Float) : Bool :=
  (x == x) && (Float.abs x < 1e308)

def finiteIn01 (x : Float) : Bool :=
  isFinite x && x > 0.0 && x < 1.0

def isMonotonicNonDecreasingFloat (xs : List Float) (tol : Float := 1e-12) : Bool :=
  xs.zip xs.tail |>.all (fun (a, b) => b + tol ≥ a)

/- ============================================================
   PCHIP inversion (Float-only)
   ============================================================ -/

def sameSign (a b : Float) : Bool :=
  (a > 0.0 && b > 0.0) || (a < 0.0 && b < 0.0)

def oppSign (a b : Float) : Bool :=
  (a > 0.0 && b < 0.0) || (a < 0.0 && b > 0.0)

def toSortedXY (iso : Isotherm Float) : Array Float × Array Float :=
  let sorted := sortBy (fun a b => a.p ≤ b.p) iso
  let xs := (sorted.map (·.p)).toArray
  let ys := (sorted.map (·.n)).toArray
  (xs, ys)

def pchipHD (xs ys : Array Float) : Array Float × Array Float := Id.run do
  let n := xs.size
  let mut h : Array Float := Array.mkEmpty (if n == 0 then 0 else n - 1)
  let mut delta : Array Float := Array.mkEmpty (if n == 0 then 0 else n - 1)
  if n ≤ 1 then
    return (h, delta)
  for i in [0:(n - 1)] do
    let hi := xs[i+1]! - xs[i]!
    let dy := ys[i+1]! - ys[i]!
    h := h.push hi
    let di := if hi == 0.0 then 0.0 else dy / hi
    delta := delta.push di
  return (h, delta)

def pchipSlopes (xs ys : Array Float) : Array Float := Id.run do
  let n := xs.size
  if n == 0 then
    return Array.mkEmpty 0
  if n == 1 then
    return Array.replicate 1 0.0
  if n == 2 then
    let d := (ys[1]! - ys[0]!) / (xs[1]! - xs[0]!)
    return #[d, d]
  let (h, delta) := pchipHD xs ys
  let mut m : Array Float := Array.replicate n 0.0
  -- interior slopes
  for i in [1:(n - 1)] do
    let dkm1 := delta[i - 1]!
    let di   := delta[i]!
    if dkm1 == 0.0 || di == 0.0 || oppSign dkm1 di then
      m := m.set! i 0.0
    else
      let w1 := 2.0 * (h[i]!) + (h[i - 1]!)
      let w2 := (h[i]!) + 2.0 * (h[i - 1]!)
      let denom := (w1 / dkm1) + (w2 / di)
      let mi := (w1 + w2) / denom
      m := m.set! i mi
  -- endpoints
  let h0 := h[0]!
  let h1 := h[1]!
  let d0 := delta[0]!
  let d1 := delta[1]!
  let mut m0 :=
    if h0 + h1 == 0.0 then 0.0
    else ((2.0 * h0 + h1) * d0 - h0 * d1) / (h0 + h1)
  if ¬ sameSign m0 d0 then
    m0 := 0.0
  else if oppSign d0 d1 && Float.abs m0 > Float.abs (3.0 * d0) then
    m0 := 3.0 * d0
  m := m.set! 0 m0
  let hn2 := h[n - 2]!
  let hn3 := h[n - 3]!
  let dn2 := delta[n - 2]!
  let dn3 := delta[n - 3]!
  let mut mn1 :=
    if hn3 + hn2 == 0.0 then 0.0
    else ((2.0 * hn2 + hn3) * dn2 - hn2 * dn3) / (hn3 + hn2)
  if ¬ sameSign mn1 dn2 then
    mn1 := 0.0
  else if oppSign dn2 dn3 && Float.abs mn1 > Float.abs (3.0 * dn2) then
    mn1 := 3.0 * dn2
  m := m.set! (n - 1) mn1
  return m

@[inline] def hermiteVal (yk yk1 mk mk1 hk t : Float) : Float :=
  let t2 := t * t
  let t3 := t2 * t
  (2.0*t3 - 3.0*t2 + 1.0) * yk
  + (t3 - 2.0*t2 + t) * hk * mk
  + (-2.0*t3 + 3.0*t2) * yk1
  + (t3 - t2) * hk * mk1

def pchipSolveOnInterval
  (xs ys ms : Array Float) (k : Nat) (target : Float)
  (maxIter : Nat := 60) (tolVal : Float := 1e-12)
  : Option Float := Id.run do
  let x0 := xs[k]!
  let x1 := xs[k + 1]!
  let h  := x1 - x0
  if h ≤ 0.0 then return none
  let y0 := ys[k]!
  let y1 := ys[k + 1]!
  let m0 := ms[k]!
  let m1 := ms[k + 1]!
  if y0 == y1 then
    if target == y0 then return some x0 else return none
  let f0 := y0 - target
  let f1 := y1 - target
  if f0 * f1 > 0.0 then return none
  let mut tL : Float := 0.0
  let mut tR : Float := 1.0
  let mut fL : Float := f0
  let mut fR : Float := f1
  for _ in [0:maxIter] do
    let tm := 0.5 * (tL + tR)
    let fm := hermiteVal y0 y1 m0 m1 h tm - target
    if Float.abs fm ≤ tolVal then
      return some (x0 + tm * h)
    if fL * fm ≤ 0.0 then
      tR := tm; fR := fm
    else
      tL := tm; fL := fm
  let tm := 0.5 * (tL + tR)
  return some (x0 + tm * h)

/-- Float-only inversion: find p such that N(p)=nm using PCHIP over the full isotherm. -/
def findPforN_pchip (iso : Isotherm Float) (nm : Float) : Option Float := Id.run do
  let (xs, ys) := toSortedXY iso
  let n := xs.size
  if n ≤ 1 then return none
  let ms := pchipSlopes xs ys
  for k in [0:(n - 1)] do
    let y0 := ys[k]!
    let y1 := ys[k + 1]!
    let yMin := if y0 ≤ y1 then y0 else y1
    let yMax := if y0 ≤ y1 then y1 else y0
    if nm ≥ yMin && nm ≤ yMax then
      if let some p := pchipSolveOnInterval xs ys ms k nm then
        if isFinite p && p > 0.0 && p < 1.0 then
          return some p
  return none

/- ============================================================
   Area (Float-only constant calculation for reporting)
   ============================================================ -/

def computeSurfaceArea (fit : BETFit Float) : Float :=
  let AVOGADRO : Float := 6.02e23
  let N2_AREA  : Float := 1.62e-19
  let N2_MOL_VOL : Float := 44.64117195
  N2_AREA * AVOGADRO * N2_MOL_VOL * fit.nm * 0.000001

/- ============================================================
   BETSI filter + checks
   ============================================================ -/

structure BETSIFilter (α : Type) where
  minPts : Nat := 10
  minR2 : α
  maxPercError : α
  deriving Repr

/--
Polymorphic BETSI core that takes an inverter:
  invert : Isotherm α → nm → Option p_read
-/

def passesBETSI_core
  {α : Type} [BETLike α]
  (invert : Isotherm α → α → Option α)
  (iso : Isotherm α) (fit : BETFit α) (window : List (Point α))
  (cfg : BETSIFilter α)
  : Option (BETSIResult α) := do

  -- require at least cfg.minPts points
  if fit.nPoints < cfg.minPts then none
  else
    -- Extended Rouquerol 1 (exact monotonicity, proof-friendly)
    let one  : α := BETLike.one (α := α)
    let zero : α := BETLike.zero (α := α)
    let n1m : List α := window.map (fun pt => (Point.n pt) * (one - (Point.p pt)))

    if ¬ isMonotoneNondecreasingExact n1m then none
    else
      let linY : List α :=
        (linearizeWindow window).map Prod.snd

      if linY.isEmpty then none
      else if ¬ isMonotoneNondecreasingExact linY then none
      else if fit.rSquared < cfg.minR2 then none
      else if fit.c ≤ zero then none
      else if fit.nm ≤ zero then none
      else
        let p_nm : α :=
          one / (HasSqrt.sqrt fit.c + one)

        let some p_read := invert iso fit.nm | none

        let (pMin, pMax) :=
          match window with
          | [] => (p_read, p_read)
          | w0 :: ws =>
              let pmin := ws.foldl (fun m pt => fmin m (Point.p pt)) (Point.p w0)
              let pmax := ws.foldl (fun M pt => fmax M (Point.p pt)) (Point.p w0)
              (pmin, pmax)

        if ¬ (pMin < p_read && p_read < pMax) then none
        else if ¬ (zero < p_read) then none
        else if isZero p_read then none
        else
          let err : α :=
            HasAbs.abs (p_read - p_nm) / p_read * (BETLike.ofNat (α := α) 100)

          if err > cfg.maxPercError then none
          else
            some { fit := fit, window := window, p_nm := p_nm, p_read := p_read, pcError := err}



def passesBETSI
  (iso : Isotherm Float) (fit : BETFit Float) (window : List (Point Float))
  (cfg : BETSIFilter Float)
  : Option (BETSIResult Float) := do
  if fit.nPoints ≤ cfg.minPts then none
  -- Extended Rouquerol 1 (tolerant, Float)
  let n1m : List Float := window.map (fun pt => pt.n * (1.0 - pt.p))
  if ¬ isMonotonicNonDecreasingFloat n1m then none

  let linY := (linearizeWindow window).map Prod.snd
  if linY.isEmpty then none
  if ¬ isMonotonicNonDecreasingFloat linY then none
  if fit.rSquared < cfg.minR2 then none
  if fit.c ≤ 0.0 || fit.nm ≤ 0.0 then none

  let p_nm := 1.0 / (Float.sqrt fit.c + 1.0)
  if ¬ finiteIn01 p_nm then none

  let some p_read := findPforN_pchip iso fit.nm | none
  if ¬ finiteIn01 p_read then none

  let (pMin, pMax) :=
    match window with
    | [] => (p_read, p_read)
    | w0 :: ws =>
      let pmin := ws.foldl (fun m pt => fmin m pt.p) w0.p
      let pmax := ws.foldl (fun M pt => fmax M pt.p) w0.p
      (pmin, pmax)

  if ¬(pMin < p_read && p_read < pMax) then none

  let err := Float.abs (p_read - p_nm) / p_read * 100.0
  if isNaN err || ¬ isFinite err then none
  if err > cfg.maxPercError then none

  some { fit := fit, window := window, p_nm := p_nm, p_read := p_read, pcError := err }

/- ============================================================
   Collect passing fits + knee selection (Float execution)
   ============================================================ -/

def allBETSIpassing
  (iso : Isotherm Float) (cfg : BETSIFilter Float)
  : List (BETSIResult Float) :=
  allWindows iso |>.filterMap (fun (start, stop, window) =>
    match fitWindow window (start, stop) with
    | some fit => passesBETSI iso fit window cfg
    | none => none)

def jmaxOf {α} (results : List (BETSIResult α)) : Nat :=
  results.foldl (fun acc r => Nat.max acc r.fit.range.snd) 0

def knee {α} (results : List (BETSIResult α)) : List (BETSIResult α) :=
  let j := jmaxOf results
  results.filter (fun r => r.fit.range.snd == j)

def kneeBest {α} [BETLike α] (results : List (BETSIResult α)) : Option (BETSIResult α) :=
  match knee results with
  | [] => none
  | k :: ks =>
      some <| ks.foldl (fun best r => if r.pcError < best.pcError then r else best) k

/- ============================================================
   Pretty printing (Float)
   ============================================================ -/

def printBETSIResult (r : BETSIResult Float) : String :=
  let area := computeSurfaceArea r.fit
  s!"Range: {r.fit.range}, Points: {r.fit.nPoints}, R²: {r.fit.rSquared}, Area: {area}\n" ++
  s!"c: {r.fit.c}, nm(BET): {r.fit.nm}, p_nm: {r.p_nm}, p_read: {r.p_read}, Error%: {r.pcError}"

def printSummary (best : BETSIResult Float) : String :=
  let area := computeSurfaceArea best.fit
  let absErr := Float.abs (best.p_nm - best.p_read)
  s!"Best area has:\n" ++
  s!"Area: {area}\n" ++
  s!"Total points: {best.fit.nPoints}\n" ++
  s!"R-Squared: {best.fit.rSquared}\n" ++
  s!"Linear Gradient: {best.fit.slope}\n" ++
  s!"Intercept: {best.fit.intercept}\n" ++
  s!"C: {best.fit.c}\n" ++
  s!"Monolayer Loading: {best.fit.nm}\n" ++
  s!"Calculated Pressure: {best.p_nm}\n" ++
  s!"Read pressure: {best.p_read}\n" ++
  s!"Error: {absErr}\n"

end BET
