import Mathlib

open BigOperators
open Filter
open Nat
open Set

set_option maxHeartbeats 0

/-!
# BET
This section defines the Brunauer–Emmett–Teller (BET) adsorption theory where we relax the assumption
of the [Langmuir model](./langmuir_kinetics.html) that restricts adsorption on a single site to be one molecule;
instead, molecules can stack on top of each other in layers.
-/


/-!
### Definitions
-/
--noncomputable theorem
namespace BET
structure system :=
  (C_1 C_L s₀ P₀: ℝ)
  (hCL : 0 < C_L)
  (hC1 : 0 < C_1)
  (hs₀ : 0 < s₀)
  (hP₀ : 0 < P₀)


def first_layer_adsorption_rate (S : BET.system) (P : ℝ) := (S.C_1) * P
local notation "Y" => BET.first_layer_adsorption_rate

def n_layer_adsorption_rate (S : BET.system) (P : ℝ) := (S.C_L) * P
local notation "X" => BET.n_layer_adsorption_rate

noncomputable def adsorption_constant (_ : BET.system) (_ : ℝ) := Y / X
local notation "C" => Y/X --BET.adsorption_constant

noncomputable def seq (S : BET.system) (P : ℝ) : ℕ → ℝ
  | 0 => S.s₀
  | (Nat.succ n) => ((X S P)^(n+1))*S.s₀*(C S P)

noncomputable def volume_adsorbed (S : BET.system) (V₀ P : ℝ) := V₀ * ∑'  (k : ℕ), ↑k * (seq S P k)
local notation "V" => BET.volume_adsorbed

noncomputable def catalyst_area (S : BET.system) (P : ℝ) := ∑' (k : ℕ), (seq S P k)
local notation "A" => BET.catalyst_area

noncomputable def brunauer_28 (S : BET.system) := λ P : ℝ => (C S P)*P/((S.P₀-P)*(1+((C S P)-1)*(P/S.P₀)))
noncomputable def brunauer_26 (S : BET.system) := λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P)))

/-!
### Proof
-/

lemma sequence_math {S : BET.system} {P : ℝ} (hx1: (X S P) < 1) (hx2 : 0 < (X S P)) :
  (∑' k : ℕ, ((k + 1:ℕ)*(seq S P (k+1))))/(S.s₀ + ∑' k, (seq S P (k + 1:ℕ))) = (C S P) * (X S P) / ((1 - (X S P)) * (1 - (X S P) + (X S P) * (C S P))) := by
  have hxnorm : ‖X S P‖ < 1 := abs_lt.mpr ⟨by nlinarith, hx1⟩
  have hsig : ∑' (k : ℕ), (↑k + 1) * X S P ^ (k + 1) = X S P / (1 - X S P) ^ 2 := by
    convert tsum_coe_mul_geometric_of_norm_lt_one hxnorm using 1
    have : Function.support (fun n => n * X S P ^ (n : ℕ)) ⊆ Set.range Nat.succ := by
      rw [Function.support_subset_iff']
      simp only [Nat.range_succ, mem_setOf_eq, not_lt, nonpos_iff_eq_zero, _root_.mul_eq_zero,
        cast_eq_zero, pow_eq_zero_iff', ne_eq, forall_eq, not_true_eq_false, and_false, or_false]
    rw [←tsum_subtype_eq_of_support_subset this, tsum_range (fun (n : ℕ) => n * X S P ^ n) Nat.succ_injective]
    simp only [succ_eq_add_one, cast_add, cast_one]
  have hsig_split : (∑' (x : ℕ), X S P ^ (x + 1)) = (∑' (x : ℕ), X S P ^ x * X S P) := by
    apply tsum_congr
    intro x
    rw [← pow_one (X S P)]
    ring
  have xsp_ne_zero : X S P ≠ 0 := Ne.symm (_root_.ne_of_lt hx2)
  have ss0_ne_zero : S.s₀ ≠ 0 := by nlinarith [S.hs₀]
  have one_sub_xsp_ne_zero : 1 - X S P ≠ 0 := by nlinarith [hx1, hx2]
  simp only [seq, ← mul_assoc, cast_add, cast_one, Pi.div_apply, tsum_mul_right]
  rw [hsig, hsig_split, tsum_mul_right, tsum_geometric_of_lt_one (le_of_lt hx2) hx1, pow_two]
  field_simp
  rw [show ((1 - X S P) * (1 - X S P) * X S P * (S.s₀ * ((1 - X S P) * X S P) + X S P * S.s₀ * Y S P)) = ((1 - X S P) * (1 - X S P + Y S P)) * (X S P * S.s₀ * ((1 - X S P) * X S P)) by ring]
  rw [show X S P * S.s₀ * Y S P * ((1 - X S P) * X S P) = Y S P * (X S P * S.s₀ * ((1 - X S P) * X S P)) by ring]
  rw [mul_div_mul_comm]
  field_simp

theorem brunauer_26_from_seq
  {P V₀: ℝ}
  {S : BET.system}
  (hx1: (X S P) < 1)
  (hx2 : 0 < (X S P))
:
  (V S V₀ P) / (A S P) = V₀ * (brunauer_26 S P)
:= by
  intros
  simp [brunauer_26]
  have hsum : Summable (seq S P)
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, _root_.pow_succ', mul_assoc, Pi.div_apply]
    refine Eq.mpr (id (congrArg Summable (funext fun n => Eq.trans (Eq.trans (congrArg (HMul.hMul (X S P)) (Eq.trans
      (congrArg (HMul.hMul (X S P ^ n)) (mul_div_assoc' S.s₀ (Y S P) (X S P)))
      (mul_div_assoc' (X S P ^ n) (S.s₀ * Y S P) (X S P))))
      (mul_div_assoc' (X S P) (X S P ^ n * (S.s₀ * Y S P)) (X S P)))
      (mul_div_cancel_left₀ (X S P ^ n * (S.s₀ * Y S P)) (_root_.ne_of_gt hx2)))))
      ?_
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _
  }
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr ; constructor <;> linarith
  have hsum2 : Summable (λ k : ℕ => ↑k * (seq S P k))
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, ← mul_assoc]
    apply Summable.mul_right _ (Summable.mul_right _ _)
    set u := λ k : ℕ => (k : ℝ) * (X S P) ^ k
    change Summable (λ (n : ℕ) => u (n+1))
    apply (summable_nat_add_iff 1).mpr _
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm }
  simp only [BET.volume_adsorbed, BET.catalyst_area]
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, Nat.pow_zero, one_mul, mul_assoc, Nat.cast_add, mul_div_assoc]
  rw [show seq S P 0 = S.s₀ by {simp [seq]}, tsum_congr, sequence_math hx1 hx2]
  field_simp [mul_comm (X S P) (C S P)]
  simp only [cast_add, cast_one, implies_true]

lemma tendsto_at_top_at_inv_CL (P : ℝ) (S : BET.system) (hP : 0 < P) -- hP hypothesis was added
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioo 0 (1 / S.C_L))) Filter.atTop:= by
  have SC_div : ∀ x : ℝ, x ≠ 0 → S.C_1 * x / (S.C_L * x) = S.C_1 / S.C_L := fun x a => mul_div_mul_right S.C_1 S.C_L a
  have SC_L_del : S.C_L * (1 / S.C_L) = 1 := by
    rw [show S.C_L * (1 / S.C_L) = S.C_L / S.C_L by ring, div_self (ne_of_gt S.hCL)]
  have h1 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (1 / S.C_L)) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; apply tendsto_const_nhds
      rw [show (1 : ℝ) = S.C_L * (1 / S.C_L) by exact Eq.symm SC_L_del]
      exact Continuous.tendsto' (continuous_mul_left S.C_L) (S.C_L * (1 / S.C_L) / S.C_L) (S.C_L * (1 / S.C_L))
          (congrArg (HMul.hMul S.C_L) (congrFun (congrArg HDiv.hDiv SC_L_del) S.C_L))
  have h2 : C S P = S.C_1 / S.C_L := by
      rw [show (Y / X) S P = S.C_1 * P / (S.C_L * P) by rfl, SC_div P (_root_.ne_of_gt hP)]
  have h3 : 0 < (C S P) := by
      rw [h2]
      exact div_pos S.hC1 S.hCL
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  simp only [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, Pi.div_apply, one_div]
  apply Eq.mpr (id (congrFun (congr (congrArg Tendsto (funext fun P => Eq.trans (congr
    (congrArg HDiv.hDiv (div_mul_eq_mul_div (S.C_1 * P) (S.C_L * P) (S.C_L * P))) (congrArg (fun x => (1 - S.C_L * P) * (1 - S.C_L * P + x))
    (div_mul_eq_mul_div (S.C_1 * P) (S.C_L * P) (S.C_L * P)))) (div_div (S.C_1 * P * (S.C_L * P)) (S.C_L * P)
    ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P * (S.C_L * P) / (S.C_L * P)))))) (congr (congrArg nhdsWithin (inv_eq_one_div S.C_L))
    (congrArg (Ioo 0) (inv_eq_one_div S.C_L)))) atTop))
  apply Filter.Tendsto.mul_atTop h3
  · rw [h2, show S.C_1 / S.C_L = S.C_1 / S.C_L * (S.C_L * (1 / S.C_L)) by rw [SC_L_del, mul_one]]
    apply Filter.Tendsto.mul
    · exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (continuous_mul_left S.C_1) (1 / S.C_L) (S.C_1 / S.C_L) (Eq.symm (div_eq_mul_one_div S.C_1 S.C_L)))
    · exact Filter.Tendsto.mul tendsto_const_nhds (tendsto_nhdsWithin_of_tendsto_nhds fun ⦃U⦄ a => a)
  · apply Filter.Tendsto.inv_tendsto_zero
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show (0:ℝ) = S.C_L * (1 / S.C_L) * ((1 - S.C_L * (1 / S.C_L)) * (1 - S.C_L * (1 / S.C_L) + S.C_1 * (1 / S.C_L) * (S.C_L * (1 / S.C_L)) / (S.C_L * (1 / S.C_L))))
      by simp only [SC_L_del, sub_eq_zero.mpr, zero_mul, mul_zero]]
    apply Filter.Tendsto.mul
    · exact Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * (1 / S.C_L)) rfl
    · apply Filter.Tendsto.mul
      · rw [show (1 - S.C_L * (1 / S.C_L)) = 0 by rw [SC_L_del, sub_eq_zero.mpr]; rfl]
        apply h1
      · apply Filter.Tendsto.add
        · rw [show (1 - S.C_L * (1 / S.C_L)) = 0 by rw [SC_L_del, sub_eq_zero.mpr]; rfl]
          apply h1
        · apply Filter.Tendsto.mul
          · exact Filter.Tendsto.mul (Continuous.tendsto' (continuous_mul_left S.C_1) (1 / S.C_L) (S.C_1 * (1 / S.C_L)) rfl)
              (Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * (1 / S.C_L)) rfl)
          · exact Tendsto.inv₀ (Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * (1 / S.C_L)) rfl) (ne_zero_of_eq_one SC_L_del)
    · apply tendsto_principal_principal.mpr
      rintro a ⟨ha1, ha2⟩
      rw [Set.mem_Ioi, show ((1 - S.C_L * a) * (1 - S.C_L * a + S.C_1 * a * (S.C_L * a) / (S.C_L * a))) = ((1 - S.C_L * a) * (1 - S.C_L * a + S.C_1 * a * ((S.C_L * a) / (S.C_L * a)))) by ring]
      rw [show (S.C_L * a / (S.C_L * a)) = 1 by rw [mul_div_mul_comm, div_self (ne_of_gt ha1), mul_one, div_self (ne_of_gt S.hCL)], mul_one]
      have ha : S.C_L * a < 1 := by
        rw [show 1 = S.C_L / S.C_L by rw [div_self (ne_of_gt S.hCL)]]
        refine (div_lt_iff' S.hCL).mp ?_
        rw [mul_comm, show a * S.C_L / S.C_L = a * (S.C_L / S.C_L) by ring, show (S.C_L / S.C_L) = 1 by apply div_self (ne_of_gt S.hCL), mul_one, ← one_div]
        exact ha2
      have hb : 0 < S.C_1 * a := by
        have i1 : 0 < S.C_1 := by exact S.hC1
        aesop
      have hc : 0 < S.C_L * a := Real.mul_pos S.hCL ha1
      exact Real.mul_pos hc (by nlinarith)
