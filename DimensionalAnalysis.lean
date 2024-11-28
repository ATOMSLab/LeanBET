import Mathlib.Tactic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Rank

universe u

/-!
### Dimension type classes
-/

class has_time (α : Type u) :=
[dec : DecidableEq α]
(time : α)

class has_length (α : Type u) :=
[dec : DecidableEq α]
(length : α)

class has_mass (α : Type u) :=
[dec : DecidableEq α]
(mass : α)

class has_amount_of_substance (α : Type u) :=
[dec : DecidableEq α]
(amount_of_substance : α)

class has_electric_current (α : Type u) :=
[dec : DecidableEq α]
(electric_current : α)

class has_temperature (α : Type u) :=
[dec : DecidableEq α]
(temperature : α)

class has_luminous_intensity (α : Type u) :=
[dec : DecidableEq α]
(luminous_intensity : α)

attribute [instance] has_time.dec
attribute [instance] has_length.dec
attribute [instance] has_mass.dec
attribute [instance] has_amount_of_substance.dec
attribute [instance] has_electric_current.dec
attribute [instance] has_temperature.dec
attribute [instance] has_luminous_intensity.dec


/-!
### Def of dimensions and its properties
-/

def dimension (α : Type u) := α → ℚ

namespace dimension
def dimensionless (α) : dimension α := Function.const α 0
instance {α} : One (dimension α) := ⟨dimension.dimensionless α⟩
instance {α} : Nonempty (dimension α) := One.instNonempty
noncomputable instance (α : Type u) (a b : dimension α ) : Decidable (a = b) :=
  Classical.propDecidable (a = b)

protected noncomputable def add {α}: dimension α → dimension α → dimension α :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a
protected noncomputable def sub {α}: dimension α → dimension α → dimension α :=
Classical.epsilon $ fun f => ∀ a b, a = b → f a b = a
protected def mul {α} : dimension α → dimension α → dimension α
| a, b => fun i => a i + b i
protected def div {α} : dimension α → dimension α → dimension α
| a, b => fun i => a i - b i
protected def pow {α} : dimension α → ℚ → dimension α
| a, n => fun i => n * (a i)
protected def le {α} : dimension α → dimension α → Prop
| a, b => ite (a = b) true false
protected def lt {α} : dimension α → dimension α → Prop
| a, b => ite (a = b) true false

noncomputable instance {α} : Add (dimension α) := ⟨dimension.add⟩
noncomputable instance {α} : Sub (dimension α) := ⟨dimension.sub⟩
instance {α} : Mul (dimension α) := ⟨dimension.mul⟩
instance {α} : Div (dimension α) := ⟨dimension.div⟩
instance {α} : Pow (dimension α) ℕ := ⟨fun d n => dimension.pow d n⟩
instance {α} : Pow (dimension α) ℤ := ⟨fun d z => dimension.pow d z⟩
instance {α} : Pow (dimension α) ℚ := ⟨dimension.pow⟩
instance {α} : Inv (dimension α) := ⟨fun d => dimension.pow d (-1)⟩
instance {α} : LT (dimension α) := ⟨dimension.lt⟩
instance {α} : LE (dimension α) := ⟨dimension.le⟩

--I would love to add unicode to make specific globabl notation for dimension derivatives and integrals,
--but thats more fluff than important

protected def derivative {α} (b : dimension α): dimension α → dimension α := fun a => a / b
protected def integral {α} (b : dimension α): dimension α → dimension α := fun a => a * b

@[simp] lemma add_def {α} (a b : dimension α) : a.add b = a + b := by rfl
@[simp] lemma add_def' {α} (a : dimension α) : a.add a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.add
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension α → dimension α → dimension α), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension α), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma add_def'' {α} (a : dimension α) : a + a = a := by rw [← add_def, add_def']
@[simp] lemma sub_def {α} (a b : dimension α) : a.sub b = a - b := by rfl
@[simp] lemma sub_def' {α} (a : dimension α) : a.sub a = a := by
  generalize hb : a = b
  nth_rewrite 1 [(symm hb)]
  revert a b hb
  unfold dimension.sub
  convert Classical.epsilon_spec ((⟨fun a _ => a, fun _ _ _ => rfl⟩ :
    ∃ (f : dimension α → dimension α → dimension α), ∀ a b, a = b → f a b = a))
  have h : ∀ (a b : dimension α), a = b → b = a := by
    intros a b h
    exact symm h
  apply h _ _
  trivial

@[simp] lemma sub_def'' {α} (a : dimension α)  : a - a = a := by rw [← sub_def, sub_def']
@[simp] lemma mul_def {α} (a b : dimension α) : a.mul b = a * b := by rfl
@[simp] lemma mul_def' {α} (a b : dimension α) : a * b = fun i => a i + b i := by rfl
@[simp] lemma div_def {α} (a b : dimension α) : a.div b = a / b := by rfl
@[simp] lemma div_def' {α} (a b : dimension α) : a / b = fun i => a i - b i := by rfl
@[simp] lemma pow_def {α} (a : dimension α) (b : ℚ) : a.pow b = a^b := by rfl
@[simp] lemma pow_def' {α} (a : dimension α) (b : ℚ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma npow_def {α} (a : dimension α) (b : ℕ) : a.pow b = a^b := by rfl
@[simp] lemma npow_def' {α} (a : dimension α) (b : ℕ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma zpow_def {α} (a : dimension α) (b : ℤ) : a.pow b = a^b := by rfl
@[simp] lemma zpow_def' {α} (a : dimension α) (b : ℤ) : a ^ b = fun i => b * (a i):= by rfl
@[simp] lemma inv_def {α} (a : dimension α) : a⁻¹ = fun i => (-1 : ℤ) * (a i) := by rfl
@[simp] lemma le_def {α} (a b : dimension α) : a.le b ↔ a ≤ b := by rfl
@[simp] lemma le_def' {α} (a : dimension α) : a ≤ a := by
  rw [← le_def]
  simp only [dimension.le, reduceIte]
@[simp] lemma lt_def {α} (a b : dimension α) : a.lt b ↔ a < b := by rfl
@[simp] lemma lt_def' {α} (a : dimension α) : a < a := by
  rw [← dimension.lt_def]
  simp only [dimension.lt, reduceIte]

/-!
### Definition of the base dimensions
-/
def length (α) [has_length α] : dimension α := Pi.single has_length.length 1
def time (α) [has_time α] : dimension α := Pi.single has_time.time 1
def mass (α) [has_mass α] : dimension α := Pi.single has_mass.mass 1
def amount_of_substance (α) [has_amount_of_substance α] : dimension α :=
  Pi.single has_amount_of_substance.amount_of_substance 1
def electric_current (α) [has_electric_current α] : dimension α :=
  Pi.single has_electric_current.electric_current 1
def temperature (α) [has_temperature α] : dimension α :=
  Pi.single has_temperature.temperature 1
def luminous_intensity (α) [has_luminous_intensity α] : dimension α :=
  Pi.single has_luminous_intensity.luminous_intensity 1


@[simp]
lemma one_eq_dimensionless {α} : 1 = dimensionless α := by rfl

@[simp]
lemma dimensionless_def' {α} : dimensionless α = Function.const α 0 := rfl

protected theorem mul_comm {α} (a b : dimension α) : a * b = b * a := by
  simp only [mul_def']
  funext
  rw [add_comm]

protected theorem div_mul_comm {α} (a b c : dimension α) : a / c * b  = b / c * a := by
  simp only [div_def', mul_def']
  funext
  rw [sub_add_comm]

protected theorem mul_assoc {α} (a b c : dimension α) : a * b * c = a * (b * c) := by
  simp only [mul_def']
  funext
  rw [add_assoc]

protected theorem mul_one {α} (a : dimension α) : a * 1 = a := by simp only [one_eq_dimensionless,
  dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, add_zero]

protected theorem one_mul {α} (a : dimension α) : 1 * a = a := by simp only [one_eq_dimensionless,
  dimensionless_def', Function.const_zero, mul_def', Pi.zero_apply, zero_add]

protected theorem div_eq_mul_inv {α} (a b : dimension α) : a / b = a * b⁻¹ := by
  simp only [div_def', inv_def, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    mul_def']
  funext
  rw [sub_eq_add_neg]

protected theorem mul_left_inv {α} (a : dimension α) : a⁻¹ * a = 1 := by
  simp only [inv_def, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul, mul_def',
    add_left_neg, one_eq_dimensionless, dimensionless_def', Function.const_zero]
  rfl

protected theorem mul_right_inv {α} (a : dimension α) : a * a⁻¹ = 1 := by
  rw [dimension.mul_comm, dimension.mul_left_inv]

protected theorem pow_zero {α} (a : dimension α) : a ^ 0 = 1 := by
  simp only [npow_def', CharP.cast_eq_zero, zero_mul, one_eq_dimensionless, dimensionless_def',
    Function.const_zero]
  rfl

protected theorem pow_succ {α} (a : dimension α) (n : ℕ) : a ^ (n + 1) = a * a^n := by
  simp only [npow_def', Nat.cast_add, Nat.cast_one, mul_def']
  funext
  rw [Rat.add_mul, add_comm, one_mul]

instance {α} : CommGroup (dimension α) where
  mul := dimension.mul
  div := dimension.div
  inv a := dimension.pow a (-1)
  mul_assoc := dimension.mul_assoc
  one := dimensionless α
  npow n a:= dimension.pow a n
  zpow z a:= dimension.pow a z
  one_mul := dimension.one_mul
  mul_one := dimension.mul_one
  mul_comm := dimension.mul_comm
  div_eq_mul_inv a := dimension.div_eq_mul_inv a
  mul_left_inv a := dimension.mul_left_inv a
  npow_zero := dimension.pow_zero
  npow_succ n a := by simp; funext x; rw [add_one_mul]
  zpow_neg' _ _ := by simp; rename_i x1 x2; funext x3; ring
  zpow_succ' _ _ := by simp; rename_i x1 x2; funext; rw [add_one_mul]
  zpow_zero' := dimension.pow_zero

/-!
### Other dimensions
-/
--physics
def velocity (α) [has_length α] [has_time α] : dimension α := length α / time α

def acceleration (α) [has_length α] [has_time α] : dimension α := length α / ((time α) ^ 2)

def force (α) [has_length α] [has_time α] [has_mass α] : dimension α :=
  length α / ((time α) ^ 2) * mass α

end dimension

open dimension
theorem accel_eq_vel_div_time {α} [has_length α] [has_time α] :
  acceleration α = velocity α / (time α) := by
    field_simp [velocity, acceleration]
    funext
    ring_nf
theorem force_eq_mass_mul_accel {α} [has_length α] [has_time α] [has_mass α] :
  force α = mass α * acceleration α := by
    simp [force, acceleration]
    funext
    ring_nf

/-!
# Buckingham-Pi Theorem
-/

--Converts a list (tuple) of dimensions (the variables) into a matrix of exponent values
def dimensional_matrix {n : ℕ} {α} [Fintype α] (d : Fin n → dimension α)
  (perm : Fin (Fintype.card α) → α) : Matrix (Fin (Fintype.card α)) (Fin n) ℚ :=
    Matrix.of.toFun (fun (a : Fin (Fintype.card α)) (i : Fin n) => d i (perm a))

--Calculates the number of dimensionless parameters possible from a list of dimensions
noncomputable def number_of_dimensionless_parameters {n : ℕ} {α} [Fintype α]
  (d : Fin n → dimension α) (perm : Fin (Fintype.card α) → α) :=
    n - Matrix.rank (dimensional_matrix d perm)

--Calculates the dimensionless parameters from a list of dimensions (not unique)
def dimensionless_numbers_matrix {n : ℕ} {α} [Fintype α] (d : Fin n → dimension α)
  (perm : Fin (Fintype.card α) → α) :=
    LinearMap.ker (Matrix.toLin' (dimensional_matrix d perm))

/-!
### examples of systems of base dimensions
-/
inductive system1
| time | length
deriving Fintype

def system1Perm
| (0 : Fin 2) => system1.length
| (1 : Fin 2) => system1.time
open dimension

instance system1.DecidableEq: DecidableEq system1
  | system1.time, system1.time => isTrue rfl
  | system1.time, system1.length => isFalse (fun h => system1.noConfusion h)
  | system1.length, system1.time => isFalse (fun h => system1.noConfusion h)
  | system1.length, system1.length => isTrue rfl

instance : has_time system1 := {dec := system1.DecidableEq, time := system1.time}
instance : has_length system1 := {dec := system1.DecidableEq, length := system1.length}

lemma system1_length_to_has_length : system1.length = has_length.length := by rfl
lemma system1_time_to_has_time : system1.time = has_time.time := by rfl

protected def system1.repr : system1 → String
| system1.length => "length"
| system1.time => "time"

lemma Fin.exists_fin_three {p : Fin 3 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 ∨ p 2 :=
  exists_fin_succ.trans <| or_congr_right exists_fin_two

example : (dimensional_matrix ![length system1, velocity system1, time system1] system1Perm)
  = !![(1 : ℚ), 1, 0; 0, -1, 1] := by

  simp [dimensional_matrix]
  funext a i
  have h1 : (a = (0 : Fin 2)) ∨ (a = (1 : Fin 2)) := by
    rw [← Fin.exists_fin_two]
    use a
  have h2 : (i = (0 : Fin 3)) ∨ ((i = (1 : Fin 3)) ∨ (i = (2 : Fin 3))) := by
    rw [← Fin.exists_fin_three]
    use i

  cases' h1 with h1 h1
  cases' h2 with h2 h2
  simp [h1, h2]
  aesop
  cases' h2
  simp [*]
  tauto
  aesop
  subst h1
  simp_all only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_fin_const]
  rcases h2 with ⟨h⟩ | ⟨h_1⟩
  · subst h
    simp_all only [Fin.isValue, Matrix.cons_val_zero]
    apply Eq.refl
  · rcases h_1 with ⟨h⟩ | ⟨h_2⟩
    · subst h
      simp_all only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      tauto
    · subst h_2
      simp_all only [Fin.isValue, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
        Matrix.tail_cons, Matrix.head_cons]
      apply Eq.refl

example : (dimensional_matrix ![length system1, velocity system1] system1Perm) =
  !![(1 : ℚ), 1; 0, -1] := by
    simp [dimensional_matrix]
    funext a i
    have h1 : (a = (0 : Fin 2)) ∨ (a = (1 : Fin 2)) := by
      rw [← Fin.exists_fin_two]
      use a
    have h2 : (i = (0 : Fin 2)) ∨ (i = (1 : Fin 2)) := by
      rw [← Fin.exists_fin_two]
      use i
    cases' h1 with h1 h1
    cases' h2 with h2 h2
    simp [h1, h2]
    simp [h1, h2, velocity, length, time]
    cases' h2 with h2 h2
    tauto
    simp [h1, h2]
    simp [h1, h2, velocity, length, time]
    tauto
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    subst h1
    simp_all only [Fin.isValue, Matrix.cons_val_one, Matrix.head_fin_const]
    rcases h2 with ⟨h⟩ | ⟨h_1⟩
    · subst h
      simp_all only [Fin.isValue, Matrix.cons_val_zero]
      apply Eq.refl
    · subst h_1
      simp_all only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
      tauto

theorem system1_accel_eq_vel_div_time : acceleration system1 = velocity system1 /
  (dimension.time system1) := accel_eq_vel_div_time

--This show that we index our tuple through the specific base dimension rather than the previous way of vector number

example : (dimension.velocity system1) system1.time = -1 := by tauto

example : (dimension.length system1) * (dimension.length system1) = Pi.single (has_length.length) 2
  := by
    simp [dimension.length]
    funext i
    cases i
    simp
    rw [system1_length_to_has_length, Pi.single_eq_same, Pi.single_eq_same]
    norm_num
