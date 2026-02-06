import BET.LinReg
--import Mathlib.Algebra.Order.Floor

/-Criteria:
  1. Minimum 10 points, up to n points (n = list length)
  2. R^2 >= 0.995 (variable, user selected)
  3. V(1-P/P0) Monotonic Increase with P/P0
  4. C (1 + slope/int) obtained by LinReg must be > 0, i.e. slope > (-int)
  5. Monolayer loading (Nm Read) must correspond to point in linear region
  6. Nm BET must be equal to Nm Read, 20% tolerance -/

structure Roquerol_Criteria where
  numPoints : String
  rVal : String
  monotonic : String
  slopInt : String
  nRead : String
  nBET : String
  vData : List Float
  pData : List Float
  Fit : LRM (Float)
  deriving Repr

instance : ToString (Roquerol_Criteria) :=
⟨fun L => "{ numPoints: " ++ ((Roquerol_Criteria.numPoints L)) ++
          ", rVal : " ++ (Roquerol_Criteria.rVal L) ++
          ", monotonic : " ++ (Roquerol_Criteria.monotonic L) ++
          ", slopInt : " ++ (Roquerol_Criteria.slopInt L) ++
          ", nRead : " ++ (Roquerol_Criteria.nRead L) ++
          ", nBET : " ++ (Roquerol_Criteria.nBET L) ++
          ", vData : " ++ (toString <| Roquerol_Criteria.vData L) ++
          ", pData : " ++ (toString <| Roquerol_Criteria.pData L) ++
          ", Fit : " ++ (toString <| Roquerol_Criteria.Fit L) ++ " }"⟩

def Roquerol.R_check (LRM_in : LRM (Float)) : String :=
  if LRM_in.rVal > 0.995 then
    "Pass"
  else
    "Fail"

def Roquerol.Monotonic_check (vData : List Float) (pData : List Float) (P0 : Float) (initVal : Float) : String :=
  match vData, pData with
  | [],[] => "Pass"
  | v :: vs, p :: ps =>
    if (v - (v*p/P0)) > initVal then
      Monotonic_check vs ps P0 (v - (v*p/P0))
    else
      "Fail"
  | v :: vs, [] => "Fail"
  | [], p :: ps => "Fail"

def Roquerol.C_check (LRM_in : LRM (Float)) : String :=
  if LRM_in.slope > (-1*(LRM_in.intercept)) then
    "Pass"
  else
    "Fail"

partial def Roquerol.loop (vData : List Float) (pData : List Float) (P0 : Float) (curIdx : Nat) (maxIdx : Nat) (subArrLen : Nat) (roqList : List Roquerol_Criteria) : Except String (List Roquerol_Criteria) :=
  if subArrLen < vData.length then
  let subVData := (vData.toArray[curIdx:(curIdx+subArrLen)]).toArray.toList
  let subPData := (pData.toArray[curIdx:(curIdx+subArrLen)]).toArray.toList
    match subVData, subPData with
    | [],[] =>
      pure (roqList)
    | v :: vs, p :: ps =>
      --if curIdx < maxIdx then
        let outLrm := linReg (subVData) (subPData)
        if (Roquerol.R_check (outLrm) == "Pass") &&
           (Roquerol.C_check (outLrm) == "Pass") &&
           (Roquerol.Monotonic_check (selSort (subVData)) (selSort (subPData)) (P0) (0) == "Pass") then
          let roqRep : Roquerol_Criteria := {numPoints := subVData.length.toFloat.toString, rVal := outLrm.rVal.toString, monotonic := "Pass", slopInt := C_check (outLrm), nRead := "Test", nBET := "Test", vData := subVData, pData := subPData, Fit := outLrm}
          let roqList := roqRep :: roqList
          loop (vData /-List.removeAll vData subVData-/) (pData /-List.removeAll pData subPData-/) (P0) (curIdx + 1) (maxIdx) (subArrLen+1) (roqList)
        else
          loop (vData /-List.removeAll vData subVData-/) (pData /-List.removeAll pData subPData-/) (P0) (curIdx + 1) (maxIdx) (subArrLen+1) (roqList)
    --termination_by loop L1 _ _ i _ _ => L1.length - i
    | v :: vs, [] => Except.error "Mismatched list lengths"
    | [], p :: ps => Except.error "Mismatched list lengths"
  else
    pure (roqList)

def Roquerol.process (vData : List Float) (pData : List Float) (P0 : Float) (subArrLen : Nat) : Except String (List Roquerol_Criteria) :=
  let nVal := vData.length
  if (nVal/10) == Nat.div (nVal) (10) then
    let maxIdx := nVal - 10
    Roquerol.loop (selSort (vData)) (selSort (pData)) (P0) (0) (maxIdx) (subArrLen) ([])
  else
    let maxIdx := Rat.ceil (nVal/10)
    Roquerol.loop (selSort (vData)) (selSort (pData)) (P0) (0) (maxIdx.toNat) (subArrLen) ([])

def exceptHandlerRoq (xData : Except String (List Roquerol_Criteria)) : String :=
    match xData with
    | Except.ok (α) => s!"{xData}"
    | Except.error (ε : String) => ε

#eval
  let xData := ([1,2,3,4,5,6,7,8,9,10,11])--([1.47,1.5,1.52,1.55,1.57,1.6,1.63,1.65,1.68,1.7,2.47,2.5,2.52,2.55,2.57,2.6,2.63,2.65,2.68,2.7,2.73])
  let yData := ([2.2,4.4,6.6,9,11,12.3,14,16,18,20,22])--([52.21,53.12,54.48,55.84,57.2,58.57,59.93,61.29,63.11,64.47,72.21,73.12,74.48,75.84,77.2,78.57,79.93,81.29,83.11,84.47,85.95])
  let output := exceptHandlerRoq <| Roquerol.process (xData) (yData) (60) (10)
  output
