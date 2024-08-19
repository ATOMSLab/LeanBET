

structure ROFx where
  N : Nat
  F : Float
  deriving Repr

def typedFunc (α : Type) (input1 : α) : α :=
  input1
def typedFunc' [Add α] (input1 : α) (input2 : α) : α :=
  input1 + input2
def typedFuncBoth : ROFx :=
  {N := typedFunc (Nat) (1) , F := typedFunc (Float) (1.0)}


#eval typedFuncBoth.N --"1"
#eval typedFuncBoth.F --"1.000000"