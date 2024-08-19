import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Analysis.SpecialFunctions.Pow.Real

structure LRM (α : Type) where
-- Must pass type with LRM, allows for polymorph. struct. def. and 'deriving Repr'
  slope : α
  intercept : α
  rVal : α
  MSE : α
  deriving Repr

instance : ToString (LRM (Float)) :=
⟨fun L => "{\n slope: " ++ (Float.toString <| LRM.slope L) ++
          ",\n intercept: " ++ (Float.toString <| LRM.intercept L) ++
          ",\n R-Value: " ++ (Float.toString <|LRM.rVal L) ++
          ",\n Mean Square Error: " ++ (Float.toString <|LRM.MSE L) ++ " \n} \n"⟩

def exceptHandler (xData : Except String (LRM (Float))) : String :=
    match xData with
    | Except.ok (α) => s!"{α}"
    | Except.error (ε : String) => ε

def FloatList.sumHelper [Add α] (soFar : α) : List α → α
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def FloatList.sum [Add α] [Zero α] (xs : List α) : α :=
  sumHelper (Zero.zero) xs

def FloatList.squareSelves [Mul α] (l : List α) : List α :=
  match l with
  |[] => []
  |(head) :: (tail) =>
    (head * head) :: squareSelves (tail)

def FloatList.squareTogether [Mul α] (xs : List α) (ys : List α) : List α :=
  match xs,ys with
    |[],[] => []
    |(headX) :: tailX, (headY) :: tailY =>
      ((headX * headY) :: squareTogether tailX tailY)
    |_ , _ => []

def FloatList.squareMeanDiff [Sub α] [Mul α] (xs: List α) (meanVal : α) : List α :=
  match xs with
  | [] => []
  |((head) :: (tail)) => ((head - meanVal) * (head - meanVal) :: squareMeanDiff tail meanVal)

def FloatList.crossProdMeanDiff [Sub α] [Mul α] (xs : List α) (ys : List α) (xMean : α) (yMean : α) : List α :=
  match xs,ys with
    |[],[] => []
    |(headX) :: tailX, (headY) :: tailY =>
      (((headX - xMean) * (headY - yMean)) :: crossProdMeanDiff tailX tailY xMean yMean)
    |_ , _ => []

def mseCalcHelper [Sub α] [Mul α] [Zero α] (yData : List α) (yDataPred : List α) (yDiffs : List α) : List α :=
  match yData, yDataPred with
  | [],[] => yDiffs
  | (headys :: tailys), (headps :: tailps) =>
    let diff := headys - headps
    let diffSquare := (diff * diff)
    let yDiffs := yDiffs ++ [diffSquare]
    mseCalcHelper (tailys) (tailps) (yDiffs)
  |_ , _ => []

def predValsCalc [Mul α] [Add α] (xData : List α) (slope : α) (intercept : α) (yDataPred : List α) : List α :=
  match xData with
  | [] => yDataPred
  | head :: tail =>
    let yDataPred := yDataPred ++ [((slope * head) + intercept)]
    predValsCalc (tail) (slope ) (intercept) (yDataPred)

def polyListLength [Add α] [Zero α] [One α] (lengthSum : α) (xs : List β) : α :=
  match xs with
  | [] => lengthSum
  | _ :: xs => polyListLength (lengthSum + One.one) (xs)

def mseCalcVert [Mul α] [Div α] [Add α] [Zero α] [Sub α] [One α] (xData : List α) (yData : List α) (slope : α) (intercept : α): α := Id.run do
  let predVals := predValsCalc (xData) (slope) (intercept) ([])
  let MSE := (1/(polyListLength (Zero.zero) (yData))) * (FloatList.sum (mseCalcHelper (yData) (predVals) ([])))
  MSE

def linReg [Add α] [Zero α] [Mul α] [One α] [Sub α] [Div α] (xData : List α) (yData : List α) : (LRM α) :=
  let nVal := (polyListLength Zero.zero xData)
  let xSum := FloatList.sum (xData)
  let xxSum := FloatList.sum (FloatList.squareSelves (xData))
  let ySum := FloatList.sum (yData)
  let yySum := FloatList.sum (FloatList.squareSelves (yData))
  let xySum := FloatList.sum (FloatList.squareTogether (xData) (yData))
  let betaHat := ((nVal * xySum) - (xSum * ySum))/((nVal * xxSum) - (xSum * xSum))
  let alphaHat := ((1/nVal) * ySum) - ((1/nVal) * betaHat * xSum)
  let seSquare := (1 / (nVal * (nVal - (One.one + One.one)))) * ((nVal * yySum) - (ySum * ySum) - ((betaHat * betaHat) * ((nVal * xxSum) - (xSum * xSum))))
  let sbSquare := (nVal * (seSquare)) / ((nVal * xxSum) - (xSum * xSum))
  let saSquare := (1 / nVal) * (sbSquare) * (xxSum)
  let Pearsonr := (((nVal * xySum) - (xSum * ySum)) * ((nVal * xySum) - (xSum * ySum))) / ((((nVal * xxSum) - (xSum * xSum)) * ((nVal * yySum) - (ySum * ySum))))
  -- The above is just the Pearson r-val squared, should be allowed because we're using Simple Lin Reg
  let MSE := mseCalcVert (xData) (yData) (betaHat) (alphaHat)

  let LRM_Out : LRM α := { slope := betaHat, intercept := alphaHat, rVal := Pearsonr, MSE := MSE}
  LRM_Out

def FloatList.checkUnique [BEq α] [Inhabited α] (xData : List α) (initVal : α) : Bool :=
  match xData with
  | [] => false
  | [_] => false
  | (_) :: (tail) =>
      if initVal == tail[0]! then
        checkUnique (tail) (initVal)
      else
        true

def LRprocess [Add α] [Zero α] [Mul α] [One α] [Sub α] [Div α] [BEq α] [Inhabited α] (xData : List α) (yData : List α)
            : Except String (LRM α) := do
  let checkXUnique := FloatList.checkUnique (xData) (xData[0]!)
  let checkYUnique := FloatList.checkUnique (yData) (yData[0]!)
  if (((checkXUnique == true) || (checkYUnique == true)) && (xData.length == yData.length)) then
    if ((xData.length > 2) && (yData.length > 2)) then
      pure ((linReg (xData) (yData)))
    else
      Except.error "Not enough data for meaningful regression (3+ points required)"
  else
    if ((checkYUnique == false) && (checkXUnique == false)) && (xData.length == yData.length) then
      Except.error "\n X and Y data returned as non-unique (all points in data are equivalent) \n"
    else
      Except.error "\n X and Y have mismatched lengths, one array is longer than the other \n"

#eval
  let xData := [1.47,1.5,1.52,1.55,1.57,1.6,1.63,1.65,1.68,1.7,1.73,1.75,1.78,1.8,1.83]
  let yData := [52.21,53.12,54.48,55.84,57.2,58.57,59.93,61.29,63.11,64.47,66.28,68.1,69.92,72.19,74.46]
  let output := linReg xData yData--exceptHandler <| LRprocess (xData) (yData)
  output.MSE

-- List Sort

def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted
        ((dbgTraceIfShared "array to swap" arr).swap ⟨i', by assumption⟩ i)
        ⟨i', by simp [dbgTraceIfShared, *]⟩

/-open List

variable {α : Type uu} [Min α] [DecidableEq α]

def SelectionSort (l : List α) : List α :=
  if 0 < l.length then
    let min := minimum? l
    match min with
    | none => []
    | some μ =>
      if mem : μ ∈ l then
        have : l.length > (l.erase μ).length :=
        calc l.length
          _ = (l.erase μ).length + 1 := by rw [← length_erase_add_one mem]
          _ > (l.erase μ).length := by linarith

        μ :: SelectionSort (l.erase μ)
      else []
  else []
termination_by SelectionSort l => l.length-/
-- ^^ Author : Asei Inoue, https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20Selection.20Sort
-- Includes a full proof / formalization. Is defined slightly differently

partial def selSort (xData : List Float) : List Float :=
  if 0 < xData.length then
    let min := List.minimum? xData
    match min with
    | none => []
    | some μ =>
      if xData.contains μ then
      μ :: selSort (xData.erase μ)
      else []
  else []
  --termination_by selSort xData => xData.length

def plusOne [Add α] [One α] (inputVal : α) : α :=
  inputVal + One.one

def functionIsOneToOne (f : X → Y) : Prop :=
  ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2

theorem PlusOneIsOneToOne : functionIsOneToOne (plusOne : Real → Real) := by
  dsimp [functionIsOneToOne]
  intro x1 x2 h
  dsimp [plusOne] at h
  linarith [h]



structure ChemProps (α : Type) where
StoichProp : String
IonicValue : α
deriving Repr

#eval
  let Boron : ChemProps Float := {StoichProp := "String", IonicValue := 7.0}
  let result := plusOne (Boron.IonicValue)
  Boron
