import BET.StreamRead

def CSV_LRM_Model (args : List String) : IO UInt32 := main args


#eval CSV_LRM_Model [
  "AdsorptionData/HKUST-1_tposed.csv",
  "AdsorptionData/HKUST-1.csv",
  "AdsorptionData/NU-1104.csv",
  "AdsorptionData/NU-1104_For_LRM.csv"
  ]
