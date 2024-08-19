import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 0

open BigOperators
open Filter
open Nat

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


def first_layer_adsorption_rate (S : BET.system) (P : ℝ):= (S.C_1)*P
local notation "Y" => BET.first_layer_adsorption_rate

def n_layer_adsorption_rate (S : BET.system) (P : ℝ):= (S.C_L)*P
local notation "X" => BET.n_layer_adsorption_rate

noncomputable def adsorption_constant (S: BET.system) (P : ℝ):= Y/X
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
  (∑' k : ℕ, ((k + 1:ℕ)*(seq S P (k+1))))/(S.s₀ + ∑' k, (seq S P (k+1:ℕ))) = (C S P)*(X S P)/((1 - (X S P))*(1 - (X S P) + (X S P)*(C S P))):= by
  simp only [seq]
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr; constructor; linarith; assumption
  simp [← mul_assoc]
  rw [tsum_mul_right, tsum_mul_right, tsum_mul_right, tsum_mul_right]
  have hsig : ∑' (k : ℕ), (↑k + 1) * X S P ^ (k + 1) = X S P / (1 - X S P) ^ 2 := by
    convert tsum_coe_mul_geometric_of_norm_lt_one hxnorm using 1
    have : Function.support (fun n => n * X S P ^ (n : ℕ)) ⊆ Set.range Nat.succ := by
      rw [Function.support_subset_iff']
      simp
    rw [←tsum_subtype_eq_of_support_subset this, tsum_range (fun (n : ℕ) => n * X S P ^ n) Nat.succ_injective]; simp
  rw [hsig]; field_simp; ring_nf
  have hx2' : 0 ≤ (X S P) := by linarith
  have hsig_split : (∑' (x : ℕ), X S P ^ (x + 1)) = (∑' (x : ℕ), X S P ^ x * X S P) := by apply tsum_congr; intro x; rw [← pow_one (X S P)]; ring
  rw [hsig_split, tsum_mul_right, tsum_geometric_of_lt_one hx2' hx1, pow_two]
  have xsp_ne_zero : X S P ≠ 0 := by linarith
  have ss0_ne_zero : S.s₀ ≠ 0 := by {linarith[S.hs₀]}
  have one_sub_xsp_ne_zero : 1 - X S P ≠ 0 := by {linarith [hx1, hx2]}
  field_simp; repeat rw [← inv_mul_eq_div]
  nth_rw 2 [← mul_one (Y S P), show 1 = (1 - X S P) / (1 - X S P) by {apply Eq.symm (div_self one_sub_xsp_ne_zero)}]
  simp [*, xsp_ne_zero, one_sub_xsp_ne_zero, ss0_ne_zero]
  rw [mul_assoc (X S P) (S.s₀) (1 - X S P), mul_assoc (X S P) S.s₀ (Y S P), ← left_distrib (X S P) _ _, mul_inv, mul_comm, ← mul_assoc, ← mul_assoc]
  have step1 := by
    calc
      X S P * X S P * S.s₀ * Y S P * (1 - X S P) * (X S P)⁻¹ * (S.s₀ * (1 - X S P) + S.s₀ * Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ = X S P * ((X S P * (X S P)⁻¹) * S.s₀) * Y S P * (1 - X S P) * (S.s₀ * (1 - X S P) + S.s₀ * Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ := by ring
      _ = X S P * S.s₀ * Y S P * (1 - X S P) * (S.s₀ * (1 - X S P) + S.s₀ * (Y S P))⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ := by rw [show (X S P) * (X S P)⁻¹ = 1 by {apply mul_inv_cancel xsp_ne_zero}, one_mul S.s₀];
  rw [step1, ← left_distrib (S.s₀) _ _, mul_inv]
  have step2 := by
    calc
      X S P * S.s₀ * Y S P * (1 - X S P) * (S.s₀⁻¹ * (1 - X S P + Y S P)⁻¹) * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ = X S P * ((S.s₀) * (S.s₀)⁻¹) * Y S P * (1 - X S P) * ((1 - X S P) + Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹ := by ring
      _ = (X S P * Y S P * (1 - X S P) * ((1 - X S P) + Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹) := by rw [show ((S.s₀) * (S.s₀)⁻¹) = 1 by {apply div_self ss0_ne_zero}, mul_one]
      _ = (X S P * Y S P * (1 - X S P) * ((1 - X S P) + Y S P)⁻¹ * (X S P - X S P * X S P * 2 + X S P ^ 3)⁻¹) * (1) := by ring
  rw [step2]; apply Eq.symm; field_simp; nth_rw 1 [← mul_one (X S P * Y S P)]; nth_rw 1 [show 1 = (1 - X S P) / (1 - X S P) by apply Eq.symm (div_self one_sub_xsp_ne_zero)];
  have step3 : ((1 - X S P + Y S P) * (X S P - X S P * X S P * 2 + X S P ^ 3)) = (X S P + X S P * Y S P + (-(X S P * X S P * 2) - X S P * X S P * Y S P) + X S P ^ 3) * (1 - X S P) := by ring
  rw [step3]; field_simp; rw [mul_comm (X S P + X S P * Y S P + (-(X S P * X S P * 2) - X S P * X S P * Y S P) + X S P ^ 3) (1 - X S P), ← div_div]; field_simp


theorem regression_form
{P V₀: ℝ}
(S : BET.system)
(hx1: (X S P) < 1)
(hx2 : 0 < (X S P))
(hP : 0 < P)
:
  let a := V₀*S.C_1
  let b := S.C_L
  let c := S.C_1
  let q := (V S V₀ P)/(A S P)
  q = a*P/((1-b*P)*(1-b*P+c*P))
:= by
  intros
  have hsum2 : Summable (seq S P)
  { apply (summable_nat_add_iff 1).mp
    simp only [seq, _root_.pow_succ', mul_assoc]
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _ }
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr; constructor; linarith; assumption
  have hsum :Summable (λ k : ℕ => ↑k * (seq S P k))
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, ← mul_assoc]
    apply Summable.mul_right _ (Summable.mul_right _ _)
    set u := λ k : ℕ => (k : ℝ) * (X S P) ^ k
    change Summable (λ (n : ℕ) => u (n+1))
    apply (summable_nat_add_iff 1).mpr _
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm }
  simp only [BET.volume_adsorbed, BET.catalyst_area]
  rw [ tsum_eq_zero_add hsum,  tsum_eq_zero_add hsum2]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, Nat.pow_zero, one_mul, mul_assoc, Nat.cast_add, mul_div_assoc]
  have hsig : (∑' (b : ℕ), (↑b + 1) * seq S P (b + 1)) / (S.s₀ + ∑' (b : ℕ), seq S P (b + 1)) = (∑' k : ℕ, ((k + 1:ℕ)*(seq S P (k+1))))/(S.s₀ + ∑' k, (seq S P (k+1:ℕ))) := by simp [*]
  rw [show seq S P 0 = S.s₀ by {simp [seq]}, hsig, sequence_math hx1 hx2]
  simp [BET.adsorption_constant, BET.n_layer_adsorption_rate]
  have h1 : S.C_L ≠ 0 := by {linarith [S.hCL]}
  have hP : P ≠ 0 := by {linarith [hP]}
  field_simp; left; repeat rw [← inv_mul_eq_div, mul_inv]
  calc
    (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) * (S.C_L * P) + S.C_L * P * Y S P)⁻¹ * (Y S P * (S.C_L * P)) = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) * (S.C_L * P) + (Y S P) * (S.C_L * P))⁻¹ * (Y S P * (S.C_L * P)) := by ring
    _ = (1 - S.C_L * P)⁻¹ * (((1 - S.C_L * P) + Y S P) * (S.C_L *P))⁻¹ * (Y S P * (S.C_L * P)) := by ring
    _ = (1 - S.C_L * P)⁻¹ * (((1 - S.C_L * P) + Y S P)⁻¹ * (S.C_L *P)⁻¹) * (Y S P * (S.C_L * P)) := by rw [mul_inv ((1 - S.C_L * P) + Y S P) (S.C_L *P)]
    _ = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) + Y S P)⁻¹ * (S.C_L * P) * (S.C_L *P)⁻¹ * (Y S P) := by ring
    _ = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) + Y S P)⁻¹ * (S.C_L * S.C_L⁻¹) * (P * P⁻¹) * (Y S P) := by ring
    _ = (1 - S.C_L * P)⁻¹ * ((1 - S.C_L * P) + Y S P)⁻¹ * (Y S P) := by rw [mul_inv_cancel h1, mul_inv_cancel hP, mul_one, mul_one]

theorem brunauer_26_from_seq
{P V₀: ℝ}
{S : BET.system}
(hx1: (X S P) < 1)
(hx2 : 0 < (X S P))
(hP : 0 < P) -- THIS IS BEING USED IN PROOF DO NOT DELETE
(hy : Y S P ≠ X S P - 1) -- THIS WAS ADDED BECAUSE THEOREM IS FALSE OTHERWISE
:  (V S V₀ P)/(A S P) = V₀*(brunauer_26 S P)
:= by
  intros
  simp [brunauer_26]
  have hsum2 : Summable (seq S P)
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, _root_.pow_succ', mul_assoc]
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _ }
  have hxnorm : ‖X S P‖ < 1 := by apply abs_lt.mpr ; constructor <;> linarith
  have hsum : Summable (λ k : ℕ => ↑k * (seq S P k))
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
  rw [show seq S P 0 = S.s₀ by {simp [seq]}]
  rw [tsum_congr, sequence_math hx1 hx2]
  field_simp [mul_comm (X S P) (C S P)]
  rw [mul_comm (1 - X S P)  (X S P), ← left_distrib (X S P) (1 - X S P) (Y S P)]
  have xsp_ne_zero : X S P ≠ 0 := by apply Ne.symm (_root_.ne_of_lt hx2)
  have xsp_sub_ysp_ne_zero : (1 - X S P) + Y S P ≠ 0 := by
    intro h'
    rw [← add_right_inj (X S P - 1), add_zero] at h'
    have hc : Y S P = (X S P - 1) := by rw [← h']; ring
    contradiction
  have xsp_sub_one_ne_zero : ((1 - X S P) * (1 - X S P + Y S P)) ≠ 0 := by
    intro H
    have H' := by apply eq_zero_or_eq_zero_of_mul_eq_zero H
    rcases H' with H1 | H2
    have xsp_ne_one : X S P ≠ 1 := by apply _root_.ne_of_lt hx1
    have xsp_eq_one : X S P = 1 := by apply (add_right_inj (-X S P)).mp; ring; exact (Eq.symm H1)
    contradiction; contradiction
  repeat rw [← mul_assoc]
  rw [mul_comm (1 - X S P) (X S P),  mul_assoc (X S P)  (1 - X S P)  (1 - X S P + Y S P)];
  have hxsp' : ((1 - X S P) * (1 - X S P + Y S P))⁻¹ * (X S P)⁻¹ * X S P * ((1 - X S P) * (1 - X S P + Y S P)) = (((1 - X S P) * (1 - X S P + Y S P)) * ((1 - X S P) * (1 - X S P + Y S P))⁻¹) * ((X S P) * (X S P)⁻¹) := by ring
  have hxsp : X S P / (X S P * ((1 - X S P) * (1 - X S P + Y S P))) = 1 / ((1 - X S P) * (1 - X S P + Y S P)) := by
    apply eq_one_div_of_mul_eq_one_left;
    rw [← inv_mul_eq_div, mul_inv, mul_comm (X S P)⁻¹  ((1 - X S P) * (1 - X S P + Y S P))⁻¹, hxsp', mul_inv_cancel xsp_ne_zero, mul_one, mul_inv_cancel xsp_sub_one_ne_zero]
  have hfin : V₀ * Y S P * X S P / (X S P * ((1 - X S P) * (1 - X S P + Y S P))) = V₀ * Y S P * (X S P / (X S P * ((1 - X S P) * (1 - X S P + Y S P)))) := by ring
  rw [hfin, hxsp]; ring
  intro b
  rw [Nat.cast_add]; simp [*]

lemma tendsto_at_top_at_inv_CL (P : ℝ) (S : BET.system) (hP : 0 < P) -- hP hypothesis was added
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1/S.C_L) (Set.Ioo 0 (1/S.C_L))) Filter.atTop:= by
  have pdiv : P / P = 1 := by apply div_self (ne_of_gt hP)
  have h1 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; apply tendsto_const_nhds;
      rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]]
      apply Filter.Tendsto.const_mul
      exact fun ⦃U⦄ a => a
  have h : 0 < (C S P) := by
      simp [BET.adsorption_constant, BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate];
      have h' : S.C_1 * P / (S.C_L * P) = S.C_1 / S.C_L := by
        calc
          S.C_1 * P / (S.C_L * P) = (S.C_1 / S.C_L) * (P / P) := by ring
          _ = S.C_1 / S.C_L := by rw [pdiv, mul_one]
      rw [h']
      refine div_pos S.hC1 S.hCL
  have h2 : S.C_1 * P / (S.C_L * P) = S.C_1 / S.C_L := by
    rw [mul_div_mul_comm]
    simp_all only [Pi.div_apply, mul_one]
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  simp [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, *]
  apply Filter.Tendsto.mul_atTop h
  simp [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, h2]
  suffices Filter.Tendsto (fun x => S.C_1 * x)
        (nhdsWithin S.C_L⁻¹ (Set.Ioo 0 S.C_L⁻¹)) (nhds (S.C_1 * S.C_L⁻¹)) by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      have hax : S.C_L * x ≠ 0 := by aesop
      have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
        aesop
      rw [h']
      simp_all only [Pi.div_apply, Set.mem_Ioo, ne_eq, _root_.mul_eq_zero, not_false_eq_true, div_mul_cancel, div_self,
        mul_one]
  exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (Continuous.continuousAt (continuous_mul_left S.C_1)))
  suffices Filter.Tendsto (fun x => ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x))⁻¹)
      (nhdsWithin S.C_L⁻¹ (Set.Ioo 0 S.C_L⁻¹)) atTop by
    apply this.congr'
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards with x hx
    have hax : S.C_L * x ≠ 0 := by aesop
    have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
      aesop
    have h'' : S.C_1*x * ((S.C_L*x) / (S.C_L*x)) = S.C_1*x := by
      aesop
    rw [h',h'']
    rfl



  sorry



lemma tendsto_at_bot_at_inv_CL (S : BET.system) (hCL : S.C_1 < S.C_L) {P : ℝ} (hP : 0 < P) -- hP hypothesis was added
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1/S.C_L) (Set.Ioo (1/S.C_L) (1/(S.C_L-S.C_1)))) Filter.atBot:= by
  have h1 : Filter.Tendsto (λ («x» : ℝ) => -(1 - S.C_L * «x»)) (nhds (S.C_L)⁻¹) (nhds (0)) := by
      simp [*]; rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by {apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]}]
      apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hf.h.hf S.C_L⁻¹; exact continuous_id'
      exact tendsto_const_nhds
  have h2 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; apply tendsto_const_nhds;  rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]]
      apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hg.h.hf S.C_L⁻¹; exact continuous_id'
  have h : 0 < (C S P) := by simp [BET.adsorption_constant, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate, mul_div_mul_right S.C_1 S.C_L (ne_of_gt hP), div_pos S.hC1 S.hCL];
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul]
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  --apply Filter.Tendsto.mul_atBot h
  simp [*, BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate]
  sorry
  /-
  rw [← Filter.tendsto_neg_atTop_iff]
  simp [neg_inv]
  have hs : S.C_L * S.C_L⁻¹ = 1 := by rw [mul_inv_cancel (ne_of_gt S.hCL)]
  have hf : (fun x => x⁻¹ * S.C_L⁻¹ * Y S x * (S.C_L * x)) = (fun x => x * x⁻¹ * Y S x) := by
    have hf' : (fun x => x⁻¹ * S.C_L⁻¹ * Y S x * (S.C_L * x)) = (fun x => x * x⁻¹ * (S.C_L * S.C_L⁻¹) * Y S x) := by simp [*]
    rw [hf', hs]; ring
  rw [hf]
  -/
  /-
  apply Filter.Tendsto.inv_tendsto_zero
  simp [nhds_within]
  apply Filter.Tendsto.inf
  rw [show 0 = 0*(C S P) by simp]
  simp only [← neg_mul]
  apply Filter.Tendsto.mul
  exact h1
  rw [show nhds (C S P) = nhds (0 + (C S P)) by simp [*]]
  apply Filter.Tendsto.add,
  exact h2,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply Filter.Tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith[S.hCL]},
  apply Filter.Tendsto.const_mul,
  finish,
  simp,
  intros a ha1 ha2,
  { rw [←neg_neg ((1 - S.C_L * a) * (1 - S.C_L * a + C S * (S.C_L * a))), neg_lt_zero, ← neg_mul,
    BET.adsorption_constant, zero_lt_mul_right],
    field_simp at ha1,
    rw div_lt_iff S.hCL at ha1,
    simp,
    linarith [ha1],
    rw [← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, sub_add, ← sub_mul],
    simp,
    ring_nf,
    rw [← mul_sub],
    field_simp at ha2,
    rw lt_div_iff at ha2,
    linarith [ha2],
    linarith [hCL],},
  simp [nhds_within],
  apply Filter.Tendsto_inf_left,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply Filter.Tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith [S.hCL]},
  apply Filter.Tendsto.const_mul,
  finish,
  -/
lemma tendsto_at_bot_at_inv_CL' (S : BET.system) (hCL : S.C_L ≤ S.C_1) {P : ℝ} (hP : 0 < P)
: Filter.Tendsto (brunauer_26 S) (nhdsWithin (1/S.C_L) (Set.Ioi (1/S.C_L))) Filter.atBot:= by
  have CL_gt_zero : 0 < S.C_L := by
    apply S.hCL
  have inv_CL_gt_zero : 0 < S.C_L⁻¹ := by
    exact inv_pos.mpr CL_gt_zero
  have h1 : Filter.Tendsto (λ («x» : ℝ) => -(1 - S.C_L * «x»)) (nhds (S.C_L)⁻¹) (nhds (0)) := by
      simp [*]; rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]]
      apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hf.h.hf S.C_L⁻¹; exact continuous_id'
      apply tendsto_const_nhds
  have h2 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (S.C_L)⁻¹) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub; apply tendsto_const_nhds;  rw [show (1 : ℝ) = S.C_L*S.C_L⁻¹ by {apply Eq.symm; rw [mul_inv_cancel (ne_of_gt S.hCL)]}]
      apply Filter.Tendsto.const_mul; refine Continuous.tendsto ?hf.h.hf S.C_L⁻¹;
  have h3 : 0 < (C S P) := by simp [BET.adsorption_constant, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate, mul_div_mul_right S.C_1 S.C_L (ne_of_gt hP), div_pos S.hC1 S.hCL];
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul]
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by exact rfl]
  simp [*, BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate]
  suffices Tendsto (fun P => S.C_1 * P / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P)))
    (nhdsWithin S.C_L⁻¹ (Set.Ioi S.C_L⁻¹)) atBot by
      apply this.congr'
      rw [eventuallyEq_nhdsWithin_iff]
      filter_upwards with x hx
      have x_gt_zero : 0 < x := by
        rw [show x ∈ Set.Ioi S.C_L⁻¹ ↔ S.C_L⁻¹ < x by exact
          { mp := fun a => hx, mpr := fun a => hx }] at hx
        linarith
      have SCL_x_div : (S.C_L * x) / (S.C_L * x) = 1 := by
        refine div_self ?_
        aesop
      have h' : S.C_1*x / (S.C_L*x) * (S.C_L*x) = S.C_1*x * ((S.C_L*x) / (S.C_L*x)) := by
        aesop
        calc
          S.C_1 * x / (S.C_L * x) * (S.C_L * x) = S.C_1 * x * ((S.C_L * x) / (S.C_L * x)) := by ring
          _ = S.C_1*x := by aesop
      rw [h']
      simp_all only [Pi.div_apply, Set.mem_Ioo, ne_eq, _root_.mul_eq_zero, not_false_eq_true, div_mul_cancel, div_self,
        mul_one]


  apply Filter.Tendsto.mul_atBot h
  sorry
  rw [← Filter.tendsto_neg_atTop_iff]
  simp [neg_inv]
  apply Filter.Tendsto.inv_tendsto_zero
  simp [nhds_within]
  apply Filter.Tendsto.inf,
  rw [show 0 = 0*(C S), by simp],
  simp only [← neg_mul],
  apply Filter.Tendsto.mul,
  exact h1,
  rw show nhds (C S) = nhds (0 + (C S)), by simp,
  apply Filter.Tendsto.add,
  exact h2,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply Filter.Tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith[S.hCL]},
  apply Filter.Tendsto.const_mul,
  finish,
  simp,
  intros a ha1,
  rw le_iff_lt_or_eq at hCL,
  cases hCL with hCL1 hCL2,
  { rw [←neg_neg ((1 - S.C_L * a) * (1 - S.C_L * a + C S * (S.C_L * a))), neg_lt_zero, ← neg_mul,
    BET.adsorption_constant, zero_lt_mul_right],
    field_simp at ha1,
    rw div_lt_iff S.hCL at ha1,
    simp,
    linarith [ha1],
    rw [← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, sub_add, ← sub_mul],
    simp,
    ring_nf,
    have h3 : S.C_L < S.C_1 ↔  a*(S.C_L - S.C_1) < 0,
    { have h4 : 0 < a, { apply lt_trans _ ha1, simp, linarith [S.hCL],},
      split,
      intro,
      rw [← mul_zero a, mul_lt_mul_left h4],
      linarith [S.hCL],
      intro,
      exact hCL1,},
    rw [← mul_sub],
    apply lt_trans' _ (h3.mp hCL1),
    finish,},
    { rw [←neg_neg ((1 - S.C_L * a) * (1 - S.C_L * a + C S * (S.C_L * a))), neg_lt_zero, ← neg_mul,
      BET.adsorption_constant, zero_lt_mul_right],
      field_simp at ha1,
      rw div_lt_iff S.hCL at ha1,
      simp,
      linarith [ha1],
      rw [← mul_assoc, div_mul, div_self (ne_of_gt S.hCL), div_one, sub_add, ← sub_mul, hCL2],
      finish,},
  simp [nhds_within],
  apply Filter.Tendsto_inf_left,
  rw show nhds (C S) = nhds ((C S)*1), by simp,
  apply Filter.Tendsto.const_mul,
  rw show 1 = S.C_L*S.C_L⁻¹, by {symmetry, rw mul_inv_eq_one₀, linarith [S.hCL]},
  apply Filter.Tendsto.const_mul,
  finish,
  -/


theorem brunauer_28_from_seq
{P V₀: ℝ}
(S : BET.system)
(h27 : S.P₀ = 1/S.C_L)
(hx1: (X S P) < 1)
(hx2 : 0 < (X S P))
(hP : 0 < P)
(hy : Y S P ≠ X S P - 1)
: (V S V₀ P)/(A S P) = V₀*(brunauer_28 S P) := by

  have  h1 : (V S V₀ P)/(A S P) = V₀*(brunauer_26 S P) := by apply brunauer_26_from_seq hx1 hx2 hP hy
  simp [*]; left
  dsimp [brunauer_26, brunauer_28, first_layer_adsorption_rate, n_layer_adsorption_rate];
  apply Eq.symm; rw [h27, ← mul_one (S.C_1 * P)]
  nth_rw 1 [show 1 = S.C_L / S.C_L by apply Eq.symm (div_self (ne_of_gt S.hCL))]; rw [mul_one]
  have step1 : S.C_1 * P / (S.C_L * P) = S.C_1 * (P / (S.C_L * P)) := by ring
  have step2 : P / (S.C_L * P) = 1 / S.C_L := by rw [← inv_mul_eq_div, mul_inv, mul_assoc, show P⁻¹ * P = 1 by rw [mul_comm, mul_inv_cancel (ne_of_gt hP)]]; simp [*]
  have step3 : S.C_1 * (1 / S.C_L) * (S.C_L * P) / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * (1 / S.C_L) * (S.C_L * P))) = S.C_1 * ((1 / S.C_L) * (S.C_L * P)) / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * ((1 / S.C_L) * (S.C_L * P)))) := by ring
  have step4 : (1 / S.C_L) * (S.C_L * P) = P := by rw [mul_comm S.C_L P, mul_comm, ← inv_mul_eq_div, mul_one, mul_assoc, show S.C_L * S.C_L⁻¹ = 1 by apply mul_inv_cancel (ne_of_gt S.hCL), mul_one]
  --simp [*, show P/P = 1 by apply div_self (ne_of_gt hP), show S.C_L / S.C_L = 1 by apply div_self (ne_of_gt S.hCL), show S.C_1 / S.C_1 = 1 by apply div_self (ne_of_gt S.hC1)]
  rw [show S.C_L / S.C_L = 1 by apply div_self (ne_of_gt S.hCL), mul_one, step1, step2, step3, step4]; field_simp
  have step5 : (S.C_L * ((1 / S.C_L - P) * (1 + (S.C_1 / S.C_L - 1) * (P * S.C_L)))) =  ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P)) := by
    ring
    have step5_1 : S.C_L * S.C_L⁻¹ - S.C_L * P + (-(S.C_L ^ 2 * S.C_L⁻¹ * P) - S.C_L ^ 2 * S.C_L⁻¹ * P ^ 2 * S.C_1) +S.C_L ^ 2 * S.C_L⁻¹ ^ 2 * P * S.C_1 + S.C_L ^ 2 * P ^ 2 = (S.C_L * S.C_L⁻¹) - S.C_L * P + (-((S.C_L ^ 2 * S.C_L⁻¹) * P) - (S.C_L ^ 2 * S.C_L⁻¹) * P ^ 2 * S.C_1) + (S.C_L ^ 2 * S.C_L⁻¹ ^ 2) * P * S.C_1 + S.C_L ^ 2 * P ^ 2 := by ring
    have step5_2 : S.C_L * S.C_L⁻¹ = 1 := by apply mul_inv_cancel (ne_of_gt S.hCL)
    have step5_3 : S.C_L^2 * S.C_L⁻¹ = S.C_L := by rw [show S.C_L^2 = S.C_L * S.C_L by ring, mul_assoc, mul_inv_cancel (ne_of_gt S.hCL), mul_one]
    have step5_4 : S.C_L^2 * S.C_L⁻¹ ^ 2 = 1 := by rw [sq, sq, show S.C_L * S.C_L * (S.C_L⁻¹ * S.C_L⁻¹) = (S.C_L * S.C_L⁻¹) * (S.C_L * S.C_L⁻¹) by ring, step5_2, one_mul]
    rw [step5_1, step5_2, step5_3, step5_4]; ring
  rw [step5]

end BET
