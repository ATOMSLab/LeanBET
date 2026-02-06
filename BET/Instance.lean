import Mathlib

namespace BET


class HasSqrt (α : Type) where
  sqrt : α → α

class HasAbs (α : Type) where
  abs : α → α

class HasIsZero (α : Type) where
  isZero : α → Bool



/-- A “BET-friendly” numeric interface: arithmetic + order (as Prop) + abs + sqrt. -/
class BETLike (α : Type) extends HasSqrt α, HasAbs α, HasIsZero α where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  pow : α → Nat → α

  le : α → α → Prop
  lt : α → α → Prop

  zero : α
  one  : α
  ofNat : Nat → α
  ofInt : Int → α

  le_dec : DecidableRel le
  lt_dec : DecidableRel lt




/-- Convenience notation. -/
@[simp] def isZero {α} [HasIsZero α] (x : α) : Bool :=
  HasIsZero.isZero x


/- ===== Lift BETLike fields into standard notation/classes ===== -/

instance {α : Type} [BETLike α] : Add α where
  add := BETLike.add

instance {α : Type} [BETLike α] : Sub α where
  sub := BETLike.sub

instance {α : Type} [BETLike α] : Mul α where
  mul := BETLike.mul

instance {α : Type} [BETLike α] : Div α where
  div := BETLike.div

instance {α : Type} [BETLike α] : Neg α where
  neg := BETLike.neg

instance {α : Type} [BETLike α] : Pow α Nat where
  pow := BETLike.pow


instance {α : Type} [BETLike α] : LE α where
  le := BETLike.le

instance {α : Type} [BETLike α] : LT α where
  lt := BETLike.lt

instance {α : Type} [BETLike α] : DecidableRel (@LE.le α _) :=
  BETLike.le_dec

instance {α : Type} [BETLike α] : DecidableRel (@LT.lt α _) :=
  BETLike.lt_dec

/- ===== Concrete instances ===== -/

/- Float: executable instance -/
instance : HasSqrt Float where
  sqrt := Float.sqrt

instance : HasAbs Float where
  abs := Float.abs

instance : HasIsZero Float where
  isZero x := x == 0.0


instance : BETLike Float where
  sqrt := Float.sqrt
  abs  := Float.abs
  add  := Float.add
  sub  := Float.sub
  mul  := Float.mul
  div  := Float.div
  neg  := Float.neg
  pow  := fun x n =>
    let rec go (x : Float) : Nat → Float
      | 0 => 1.0
      | k + 1 => x * go x k
    go x n
  le   := fun a b => a ≤ b
  lt   := fun a b => a < b
  zero := 0.0
  one  := 1.0
  ofNat := Float.ofNat
  ofInt := Float.ofInt
  le_dec := inferInstance
  lt_dec := inferInstance



/- ℝ: proof instance (noncomputable is fine) -/
noncomputable instance : HasSqrt ℝ where
  sqrt := Real.sqrt

noncomputable instance : HasAbs ℝ where
  abs := abs

noncomputable instance : HasIsZero ℝ where
  isZero x := decide (x = 0)

noncomputable instance : BETLike ℝ where
  sqrt := Real.sqrt
  abs  := abs
  add  := (· + ·)
  sub  := (· - ·)
  mul  := (· * ·)
  div  := (· / ·)
  neg  := Neg.neg
  pow  := fun x n => x ^ n
  le   := (· ≤ ·)
  lt   := (· < ·)
  zero := 0
  one  := 1
  ofNat := fun n => (n : ℝ)
  ofInt := fun z => (z : ℝ)
  le_dec := inferInstance
  lt_dec := inferInstance

end BET
