import Mathlib

open BigOperators
open Filter
open Nat
open Set

set_option maxHeartbeats 0

/-!
# BET
This section defines the Brunauer–Emmett–Teller (BET) adsorption theory where we relax the
assumption of the [Langmuir model](./langmuir_kinetics.html) that restricts adsorption on a single
site to be one molecule; instead, molecules can stack on top of each other in layers.
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

variable (S : BET.system) (P V₀ : ℝ)

def first_layer_adsorption_rate := S.C_1 * P
notation "Y" => BET.first_layer_adsorption_rate

def n_layer_adsorption_rate := S.C_L * P
notation "X" => BET.n_layer_adsorption_rate

noncomputable def adsorption_constant := Y / X
notation "C" => Y / X --BET.adsorption_constant

noncomputable def seq : ℕ → ℝ
  | 0 => S.s₀
  | (Nat.succ n) => (X S P ^ (n + 1)) * S.s₀ * C S P

noncomputable def volume_adsorbed :=
  V₀ * ∑'  (k : ℕ), ↑k * (seq S P k)
notation "V" => BET.volume_adsorbed

noncomputable def catalyst_area := ∑' (k : ℕ), seq S P k
notation "A" => BET.catalyst_area

noncomputable def brunauer_28 :=
  fun P : ℝ => C S P * P / ((S.P₀ - P) * (1 + (C S P - 1) * (P / S.P₀)))

noncomputable def brunauer_26 :=
  fun P => C S P * X S P / ((1 - X S P) * (1 - X S P + C S P * X S P))

/-!
### Proof
-/

lemma sequence_math
  (hx1 : X S P < 1)
  (hx2 : 0 < X S P)
:
  (∑' k, ((k + 1:ℕ) * (seq S P (k + 1)))) / (S.s₀ + ∑' k, (seq S P (k + 1:ℕ))) = C S P * X S P
  / ((1 - X S P) * (1 - X S P + X S P * C S P))
:= by
  have hxnorm : ‖X S P‖ < 1 := abs_lt.mpr ⟨by nlinarith, hx1⟩
  have ne_zero : X S P * S.s₀ * ((1 - X S P) * X S P) ≠ 0 := by
    apply _root_.ne_of_gt
    apply Real.mul_pos (Real.mul_pos hx2 S.hs₀)
    exact Real.mul_pos (sub_pos.mpr hx1) hx2
  have hsig : ∑' (k : ℕ), (↑k + 1) * X S P ^ (k + 1) = X S P / (1 - X S P) ^ 2 := by
    convert tsum_coe_mul_geometric_of_norm_lt_one hxnorm using 1
    have : Function.support (fun n => n * X S P ^ (n : ℕ)) ⊆ Set.range Nat.succ := by
      rw [Function.support_subset_iff']
      simp only [Nat.range_succ, mem_setOf_eq, not_lt, nonpos_iff_eq_zero, _root_.mul_eq_zero,
        cast_eq_zero, pow_eq_zero_iff', ne_eq, forall_eq, not_true_eq_false, and_false, or_false]
    rw [←tsum_subtype_eq_of_support_subset this, tsum_range (fun (n : ℕ) => n * X S P ^ n)
      Nat.succ_injective]
    simp only [succ_eq_add_one, cast_add, cast_one]
  have hsig_split : (∑' (x : ℕ), X S P ^ (x + 1)) = (∑' (x : ℕ), X S P ^ x * X S P) := by
    apply tsum_congr
    intro x
    rw [← pow_one (X S P)]
    ring
  simp only [seq, ← mul_assoc, cast_add, cast_one, Pi.div_apply, tsum_mul_right]
  rw [hsig, hsig_split, tsum_mul_right, tsum_geometric_of_lt_one (le_of_lt hx2) hx1, pow_two]
  field_simp [Ne.symm (_root_.ne_of_lt hx2), _root_.ne_of_gt S.hs₀, _root_.ne_of_gt (sub_pos.mpr
    hx1)]
  rw [show ((1 - X S P) * (1 - X S P) * X S P * (S.s₀ * ((1 - X S P) * X S P) + X S P * S.s₀ *
    Y S P)) = ((1 - X S P) * (1 - X S P + Y S P)) * (X S P * S.s₀ * ((1 - X S P) * X S P)) by ring,
    show X S P * S.s₀ * Y S P * ((1 - X S P) * X S P) = Y S P * (X S P * S.s₀ * ((1 - X S P) *
    X S P)) by ring, mul_div_mul_comm, div_self ne_zero, mul_one]

theorem brunauer_26_from_seq
  (hx1: X S P < 1)
  (hx2 : 0 < X S P)
:
  V S P V₀ / A S P = V₀ * brunauer_26 S P
:= by
  have hxnorm : ‖X S P‖ < 1 := abs_lt.mpr ⟨by nlinarith, hx1⟩
  have hsum : Summable (seq S P)
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, _root_.pow_succ', mul_assoc, Pi.div_apply]
    apply Eq.mpr (id (congrArg Summable (funext fun n => Eq.trans (Eq.trans (congrArg (HMul.hMul
      (X S P)) (Eq.trans (congrArg (HMul.hMul (X S P ^ n)) (mul_div_assoc' S.s₀ (Y S P) (X S P)))
      (mul_div_assoc' (X S P ^ n) (S.s₀ * Y S P) (X S P))))
      (mul_div_assoc' (X S P) (X S P ^ n * (S.s₀ * Y S P)) (X S P)))
      (mul_div_cancel_left₀ (X S P ^ n * (S.s₀ * Y S P)) (_root_.ne_of_gt hx2)))))
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _
  }
  have hsum2 : Summable (λ k : ℕ => ↑k * (seq S P k))
  { apply (summable_nat_add_iff 1).mp _
    simp only [seq, ← mul_assoc]
    apply Summable.mul_right _ (Summable.mul_right _ _)
    set u := λ k : ℕ => (k : ℝ) * (X S P) ^ k
    change Summable (λ (n : ℕ) => u (n + 1))
    apply (summable_nat_add_iff 1).mpr _
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm }
  rw [brunauer_26, BET.volume_adsorbed, BET.catalyst_area]
  rw [tsum_eq_zero_add hsum, tsum_eq_zero_add hsum2]
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, Nat.pow_zero, one_mul, mul_assoc,
    Nat.cast_add, mul_div_assoc]
  rw [seq, tsum_congr, sequence_math S P hx1 hx2]
  field_simp [mul_comm (X S P) (C S P)]
  simp only [cast_add, cast_one, implies_true]

lemma tendsto_at_top_at_inv_CL
  (hP : 0 < P) -- hP hypothesis was added by Colin J.
:
  Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioo 0 (1 / S.C_L))) Filter.atTop
:= by
  have SC_L_del : S.C_L * (1 / S.C_L) = 1 := by
    rw [show S.C_L * (1 / S.C_L) = S.C_L / S.C_L by ring, div_self (ne_of_gt S.hCL)]
  have h1 : Filter.Tendsto (λ («x» : ℝ) => 1 - S.C_L * «x») (nhds (1 / S.C_L)) (nhds (0)) := by
      rw [show (0 : ℝ) = 1 - 1 by norm_num]
      apply Filter.Tendsto.sub (tendsto_const_nhds)
      rw [show (1 : ℝ) = S.C_L * (1 / S.C_L) by exact Eq.symm SC_L_del]
      exact Continuous.tendsto' (continuous_mul_left S.C_L) (S.C_L * (1 / S.C_L) / S.C_L) (S.C_L *
        (1 / S.C_L)) (congrArg (HMul.hMul S.C_L) (congrFun (congrArg HDiv.hDiv SC_L_del) S.C_L))
  have h2 : 0 < (C S P) := by
      rw [Pi.div_apply, Pi.div_apply, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate,
        mul_div_mul_right S.C_1 S.C_L (_root_.ne_of_gt hP)]
      exact div_pos S.hC1 S.hCL
  rw [show brunauer_26 S = λ P => (C S P)*(X S P)/((1-(X S P))*(1-(X S P)+(C S P)*(X S P))) by
    exact rfl]
  simp only [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, Pi.div_apply, one_div]
  apply Eq.mpr (id (congrFun (congr (congrArg Tendsto (funext fun P => Eq.trans (congr
    (congrArg HDiv.hDiv (div_mul_eq_mul_div (S.C_1 * P) (S.C_L * P) (S.C_L * P))) (congrArg (fun x
      => (1 - S.C_L * P) * (1 - S.C_L * P + x))
    (div_mul_eq_mul_div (S.C_1 * P) (S.C_L * P) (S.C_L * P)))) (div_div (S.C_1 * P * (S.C_L * P))
    (S.C_L * P) ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P * (S.C_L * P) / (S.C_L * P))))))
    (congr (congrArg nhdsWithin (inv_eq_one_div S.C_L)) (congrArg (Ioo 0) (inv_eq_one_div S.C_L))))
    atTop))
  apply Filter.Tendsto.mul_atTop h2
  · rw [Pi.div_apply, Pi.div_apply, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate,
      mul_div_mul_right S.C_1 S.C_L (_root_.ne_of_gt hP), show S.C_1 / S.C_L = S.C_1 / S.C_L *
      (S.C_L * (1 / S.C_L)) by rw [SC_L_del, mul_one]]
    apply Filter.Tendsto.mul
      (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (continuous_mul_left S.C_1) (1 /
      S.C_L) (S.C_1 / S.C_L) (Eq.symm (div_eq_mul_one_div S.C_1 S.C_L))))
      (Filter.Tendsto.mul tendsto_const_nhds (tendsto_nhdsWithin_of_tendsto_nhds fun ⦃U⦄ a => a))
  · apply Filter.Tendsto.inv_tendsto_zero
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show (0:ℝ) = S.C_L * (1 / S.C_L) * ((1 - S.C_L * (1 / S.C_L)) * (1 - S.C_L * (1 / S.C_L) +
      S.C_1 * (1 / S.C_L) * (S.C_L * (1 / S.C_L)) / (S.C_L * (1 / S.C_L))))
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
            (Filter.Tendsto.mul (Continuous.tendsto' (continuous_mul_left S.C_1) (1 / S.C_L) (S.C_1
               * (1 / S.C_L)) rfl) (Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L)
               (S.C_L * (1 / S.C_L)) rfl))
            (Tendsto.inv₀ (Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L *
              (1 / S.C_L)) rfl) (ne_zero_of_eq_one SC_L_del))
    · apply tendsto_principal_principal.mpr
      rintro a ⟨ha1, ha2⟩
      rw [Set.mem_Ioi, show ((1 - S.C_L * a) * (1 - S.C_L * a + S.C_1 * a * (S.C_L * a) /
        (S.C_L * a))) = ((1 - S.C_L * a) * (1 - S.C_L * a + S.C_1 * a * ((S.C_L * a) / (S.C_L * a))
        )) by ring]
      rw [show (S.C_L * a / (S.C_L * a)) = 1 by rw [mul_div_mul_comm, div_self (ne_of_gt ha1),
        mul_one, div_self (ne_of_gt S.hCL)], mul_one]
      have ha : S.C_L * a < 1 := by
        rw [show 1 = S.C_L / S.C_L by rw [div_self (ne_of_gt S.hCL)]]
        refine (div_lt_iff' S.hCL).mp ?_
        rw [mul_comm, show a * S.C_L / S.C_L = a * (S.C_L / S.C_L) by ring, show (S.C_L / S.C_L) =
          1 by apply div_self (ne_of_gt S.hCL), mul_one, ← one_div]
        exact ha2
      have hb : 0 < S.C_1 * a := Real.mul_pos S.hC1 ha1
      have hc : 0 < S.C_L * a := Real.mul_pos S.hCL ha1
      exact Real.mul_pos hc (by nlinarith)

lemma tendsto_at_bot_at_inv_CL
  (hCL : S.C_1 < S.C_L)
  (hP : 0 < P) -- hP hypothesis was added by Colin J.
:
Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1))))
  Filter.atBot
:= by
  have rearrange1 : (fun x => -(S.C_L * x * ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x *
    (S.C_L * x) / (S.C_L * x))))⁻¹) = (fun x => (-1)⁻¹ * (S.C_L * x * ((1 - S.C_L * x) *
    (1 - S.C_L * x + S.C_1 * x * (S.C_L * x) / (S.C_L * x))))⁻¹) := by
      funext x
      ring_nf!
  have rearrange2 : (fun x => (-1)⁻¹ * (S.C_L * x * ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x *
    (S.C_L * x) / (S.C_L * x))))⁻¹) = (fun x => (-1 * (S.C_L * x * ((1 - S.C_L * x) *
    (1 - S.C_L * x + S.C_1 * x * (S.C_L * x) / (S.C_L * x)))))⁻¹):= by
      funext x
      rw [← mul_inv]
  have SC_L_del : S.C_L * (1 / S.C_L) = 1 := by
    rw [show S.C_L * (1 / S.C_L) = S.C_L / S.C_L by ring, div_self (ne_of_gt S.hCL)]
  have h1 : 0 < (C S P) := by
      rw [Pi.div_apply, Pi.div_apply, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate,
        mul_div_mul_right S.C_1 S.C_L (_root_.ne_of_gt hP)]
      exact div_pos S.hC1 S.hCL
  rw [div_eq_inv_mul, show brunauer_26 S = fun P => C S P * X S P / ((1 - X S P) * (1 - X S P +
    C S P * X S P)) by rfl]
  simp only [BET.n_layer_adsorption_rate, BET.first_layer_adsorption_rate, Pi.div_apply, one_div]
  apply Eq.mpr (id (congrFun (congr (congrArg Tendsto (funext fun P => Eq.trans (congr (congrArg
    HDiv.hDiv (div_mul_eq_mul_div (S.C_1 * P) (S.C_L * P) (S.C_L * P))) (congrArg (fun x =>
    (1 - S.C_L * P) * (1 - S.C_L * P + x)) (div_mul_eq_mul_div (S.C_1 * P) (S.C_L * P) (S.C_L * P))
    )) (div_div (S.C_1 * P * (S.C_L * P)) (S.C_L * P) ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P
    * (S.C_L * P) / (S.C_L * P)))))) (congr (congrArg nhdsWithin (Eq.trans (Eq.trans (congrArg
    (fun x => x * 1) (inv_eq_one_div S.C_L)) (div_mul_eq_mul_div 1 S.C_L 1)) (congrArg (fun x => x
    / S.C_L) (mul_one 1)))) (congr (congrArg Ioo (Eq.trans (Eq.trans (congrArg (fun x => x * 1)
    (inv_eq_one_div S.C_L)) (div_mul_eq_mul_div 1 S.C_L 1)) (congrArg (fun x => x / S.C_L)
    (mul_one 1)))) (inv_eq_one_div (S.C_L - S.C_1))))) atBot))
  apply Filter.Tendsto.mul_atBot h1
  · rw [Pi.div_apply, Pi.div_apply, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate,
      mul_div_mul_right S.C_1 S.C_L (_root_.ne_of_gt hP), show S.C_1 / S.C_L = S.C_1 / S.C_L *
      (S.C_L * (1 / S.C_L)) by rw [SC_L_del, mul_one]]
    simp only [one_div, Pi.div_apply]
    apply Filter.Tendsto.mul
      (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (continuous_mul_left S.C_1)
          S.C_L⁻¹ (S.C_1 / S.C_L) rfl))
      (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto (continuous_mul_left S.C_L)
          S.C_L⁻¹))
  · rw [← tendsto_neg_atTop_iff, rearrange1, rearrange2]
    simp only [one_mul, one_div]
    refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show (0:ℝ) = -1 * (S.C_L * S.C_L⁻¹ * ((1 - S.C_L * S.C_L⁻¹) * (1 - S.C_L * S.C_L⁻¹ + S.C_1
      * S.C_L⁻¹ * (S.C_L * S.C_L⁻¹) / (S.C_L * S.C_L⁻¹)))) by field_simp [_root_.ne_of_gt S.hCL]]
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    · apply Filter.Tendsto.mul
      · refine Continuous.tendsto' (continuous_mul_left S.C_L) S.C_L⁻¹ (S.C_L * S.C_L⁻¹) rfl
      · apply Filter.Tendsto.mul
        · apply Filter.Tendsto.sub (tendsto_const_nhds)
            (Continuous.tendsto' (continuous_mul_left S.C_L) S.C_L⁻¹ (S.C_L * S.C_L⁻¹) rfl)
        · apply Filter.Tendsto.add
          · apply Filter.Tendsto.sub (tendsto_const_nhds)
              (Continuous.tendsto' (continuous_mul_left S.C_L) S.C_L⁻¹ (S.C_L * S.C_L⁻¹) rfl)
          · apply Filter.Tendsto.mul
            · apply Filter.Tendsto.mul
              · refine Continuous.tendsto' (continuous_mul_left S.C_1) S.C_L⁻¹ (S.C_1 * S.C_L⁻¹) rfl
              · refine Continuous.tendsto' (continuous_mul_left S.C_L) S.C_L⁻¹ (S.C_L * S.C_L⁻¹) rfl
            · refine (tendsto_inv_iff₀ ?_).mpr (Continuous.tendsto' (continuous_mul_left S.C_L)
                S.C_L⁻¹ (S.C_L * S.C_L⁻¹) rfl)
              rw [mul_ne_zero_iff]
              exact ⟨_root_.ne_of_gt S.hCL, inv_ne_zero (_root_.ne_of_gt S.hCL)⟩
    refine tendsto_principal_principal.mpr ?h₂.a
    rintro a ⟨ha1, ha2⟩
    rw [Set.mem_Ioi]
    simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, _root_.ne_of_gt S.hCL,
      _root_.ne_of_gt (gt_trans ha1 (inv_pos.mpr S.hCL)), or_self, not_false_eq_true,
      IsUnit.mul_div_cancel_right, neg_mul, one_mul, Left.neg_pos_iff]
    have hi1 : 1 < S.C_L * a := by
      rw [← inv_mul_cancel (_root_.ne_of_gt S.hCL), mul_comm]
      nlinarith [ha1, S.hCL]
    have hi2 : S.C_L * S.C_L⁻¹ < S.C_L * a := by
      simp_all only [mul_inv_rev, neg_mul, one_mul, one_div, Pi.div_apply]
    have hi3 : (S.C_L - S.C_1) * a < (S.C_L - S.C_1) * (S.C_L - S.C_1)⁻¹ := by
      simp_all only [mul_inv_rev, neg_mul, one_mul, one_div, Pi.div_apply, gt_iff_lt, sub_pos,
        mul_lt_mul_left]
    have hi4 : (S.C_L - S.C_1) * a < 1 :=
      calc
        (S.C_L - S.C_1) * a
          < (S.C_L - S.C_1) * (S.C_L - S.C_1)⁻¹ := by nlinarith
        _ = 1 := by rw [mul_comm, inv_mul_cancel (by nlinarith [S.hCL, S.hC1])]
    have hi5 : 0 < S.C_L * a := Real.mul_pos S.hCL (by nlinarith)
    exact mul_neg_of_pos_of_neg hi5 (by nlinarith)

lemma tendsto_at_bot_at_inv_CL'
(hCL : S.C_L ≤ S.C_1)
(hP : 0 < P)
:
Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioi (1 / S.C_L))) Filter.atBot
:= by
  have rearrange1 : (fun x => -(S.C_1 * x * (S.C_L * x) / (S.C_L * x * ((1 - S.C_L * x) *
    (1 - S.C_L * x + S.C_1 * x * (S.C_L * x) / (S.C_L * x)))))) = (fun x => (-S.C_1 * x *
    (S.C_L * x) / (S.C_L * x * ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x * (S.C_L * x) /
    (S.C_L * x)))))) := by
      funext x
      ring_nf!
  have rearrange2 : (fun x => (-S.C_1 * x * (S.C_L * x) / (S.C_L * x * ((1 - S.C_L * x) *
    (1 - S.C_L * x + S.C_1 * x * (S.C_L * x) / (S.C_L * x)))))) = (fun x => ((S.C_1 * x *
    (S.C_L * x)) / (-1 * (S.C_L * x * ((1 - S.C_L * x) * (1 - S.C_L * x + S.C_1 * x * (S.C_L * x) /
    (S.C_L * x))))))) := by
      funext x
      rw [neg_one_mul, div_neg_eq_neg_div]
      field_simp
  have inv_CL_gt_zero : 0 < S.C_L⁻¹ := inv_pos.mpr S.hCL
  have h1 : 0 < (C S P) := by
    rw [Pi.div_apply, Pi.div_apply, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate,
      mul_div_mul_right S.C_1 S.C_L (_root_.ne_of_gt hP)]
    exact div_pos S.hC1 S.hCL
  simp only [brunauer_26, BET.n_layer_adsorption_rate, div_eq_inv_mul]
  rw [show brunauer_26 S = λ P => C S P * X S P / ((1 - X S P) * (1 - X S P + C S P * X S P)) by
    rfl]
  simp only [Pi.div_apply, first_layer_adsorption_rate, n_layer_adsorption_rate, mul_one]
  field_simp
  rw [← tendsto_neg_atTop_iff, rearrange1, rearrange2]
  apply Filter.Tendsto.mul_atTop h1
  · rw [one_div, Pi.div_apply, Pi.div_apply, first_layer_adsorption_rate, n_layer_adsorption_rate,
      mul_div_mul_comm, div_self (_root_.ne_of_gt hP), mul_one]
    apply tendsto_nhdsWithin_of_tendsto_nhds
    rw [show (S.C_1 / S.C_L) = (S.C_1 * S.C_L⁻¹) * (S.C_L * S.C_L⁻¹) by
      rw [mul_comm S.C_L, inv_mul_cancel (_root_.ne_of_gt S.hCL), mul_one, ← one_div, mul_one_div]]
    apply Filter.Tendsto.mul
      (Continuous.tendsto' (continuous_mul_left S.C_1) S.C_L⁻¹ (S.C_1 * S.C_L⁻¹) rfl)
      (Continuous.tendsto' (continuous_mul_left S.C_L) S.C_L⁻¹ (S.C_L * S.C_L⁻¹) rfl)
  · refine Filter.Tendsto.inv_tendsto_zero ?_
    rw [nhdsWithin]
    apply Filter.Tendsto.inf
    rw [show (0:ℝ) = -1 * (S.C_L * S.C_L⁻¹ * ((1 - S.C_L * S.C_L⁻¹) * (1 - S.C_L * S.C_L⁻¹ + S.C_1
      * S.C_L⁻¹ * (S.C_L * S.C_L⁻¹) / (S.C_L * S.C_L⁻¹)))) by field_simp [_root_.ne_of_gt S.hCL]]
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    · apply Filter.Tendsto.mul
      · refine Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * S.C_L⁻¹)
          (by field_simp)
      · apply Filter.Tendsto.mul
        · apply Filter.Tendsto.sub (tendsto_const_nhds)
          refine Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * S.C_L⁻¹)
            (by field_simp)
        · apply Filter.Tendsto.add
          · apply Filter.Tendsto.sub (tendsto_const_nhds)
            refine Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * S.C_L⁻¹)
              (by field_simp)
          · apply Filter.Tendsto.mul
            · apply Filter.Tendsto.mul
              · refine
                Continuous.tendsto' (continuous_mul_left S.C_1) (1 / S.C_L) (S.C_1 * S.C_L⁻¹)
                  (by field_simp)
              · refine
                Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * S.C_L⁻¹)
                  (by field_simp)
            · refine (tendsto_inv_iff₀ ?_).mpr (Continuous.tendsto' (continuous_mul_left S.C_L)
                (1 / S.C_L) (S.C_L * S.C_L⁻¹) (by field_simp))
              rw [mul_ne_zero_iff]
              exact ⟨_root_.ne_of_gt S.hCL, inv_ne_zero (_root_.ne_of_gt S.hCL)⟩
    · refine tendsto_principal_principal.mpr ?h₂.a
      rintro a ha
      rw [Set.mem_Ioi, one_div] at ha
      rw [Set.mem_Ioi]
      clear rearrange1 rearrange2
      simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, _root_.ne_of_gt S.hCL,
        _root_.ne_of_gt (gt_trans ha (by assumption)), or_self, not_false_eq_true,
        IsUnit.mul_div_cancel_right, neg_mul, one_mul, Left.neg_pos_iff]
      have hi1 : 0 < a :=
        calc
          0 < S.C_L⁻¹ := by assumption
          _ < a := ha
      have hi2 : 1 < S.C_L * a := by
        rw [← inv_mul_cancel (_root_.ne_of_gt S.hCL), mul_comm]
        nlinarith [hi1, S.hCL]
      have hi3 : S.C_L * a ≤ S.C_1 * a := by
        simp_all only [inv_pos, one_div, neg_sub, Pi.div_apply, sub_pos,
          gt_iff_lt, _root_.mul_le_mul_right]
      refine mul_neg_of_pos_of_neg ?_ ?_ <;>
      nlinarith

theorem brunauer_28_from_seq
(h27 : S.P₀ = 1 / S.C_L)
(hx1: X S P < 1)
(hx2 : 0 < X S P)
(hP : 0 < P)
:
V S P V₀ / A S P = V₀ * brunauer_28 S P
:= by
  rw [brunauer_26_from_seq S P V₀ hx1 hx2, brunauer_26, brunauer_28]
  simp only [Pi.div_apply, first_layer_adsorption_rate, n_layer_adsorption_rate,
    mul_eq_mul_left_iff]
  left
  apply Eq.symm
  rw [h27, ← mul_one (S.C_1 * P)]
  nth_rw 1 [show 1 = S.C_L / S.C_L by apply Eq.symm (div_self (ne_of_gt S.hCL))]
  rw [mul_one]
  have step1 : S.C_1 * P / (S.C_L * P) = S.C_1 * (P / (S.C_L * P)) := by ring
  have step2 : P / (S.C_L * P) = 1 / S.C_L := by
    rw [← inv_mul_eq_div, mul_inv, mul_assoc, show P⁻¹ * P = 1 by rw [mul_comm, mul_inv_cancel
      (ne_of_gt hP)]]
    simp only [mul_one, one_div]
  have step3 : S.C_1 * (1 / S.C_L) * (S.C_L * P) / ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 *
    (1 / S.C_L) * (S.C_L * P))) = S.C_1 * ((1 / S.C_L) * (S.C_L * P)) / ((1 - S.C_L * P) * (1 -
    S.C_L * P + S.C_1 * ((1 / S.C_L) * (S.C_L * P)))) := by ring
  have step4 : (1 / S.C_L) * (S.C_L * P) = P := by
    rw [mul_comm S.C_L P, mul_comm, ← inv_mul_eq_div, mul_one, mul_assoc, show S.C_L * S.C_L⁻¹ = 1
      by apply mul_inv_cancel (ne_of_gt S.hCL), mul_one]
  have step5 : (S.C_L * ((1 / S.C_L - P) * (1 + (S.C_1 / S.C_L - 1) * (P * S.C_L)))) =
    ((1 - S.C_L * P) * (1 - S.C_L * P + S.C_1 * P)) := by
      ring_nf!
      have step5_1 : S.C_L * S.C_L⁻¹ - S.C_L * P + (-(S.C_L ^ 2 * S.C_L⁻¹ * P) - S.C_L ^ 2 *
        S.C_L⁻¹ * P ^ 2 * S.C_1) +S.C_L ^ 2 * S.C_L⁻¹ ^ 2 * P * S.C_1 + S.C_L ^ 2 * P ^ 2 =
        (S.C_L * S.C_L⁻¹) - S.C_L * P + (-((S.C_L ^ 2 * S.C_L⁻¹) * P) - (S.C_L ^ 2 * S.C_L⁻¹) *
        P ^ 2 * S.C_1) + (S.C_L ^ 2 * S.C_L⁻¹ ^ 2) * P * S.C_1 + S.C_L ^ 2 * P ^ 2 := by ring
      have step5_2 : S.C_L * S.C_L⁻¹ = 1 := by apply mul_inv_cancel (ne_of_gt S.hCL)
      have step5_3 : S.C_L^2 * S.C_L⁻¹ = S.C_L := by rw [show S.C_L^2 = S.C_L * S.C_L by ring,
        mul_assoc, mul_inv_cancel (ne_of_gt S.hCL), mul_one]
      have step5_4 : S.C_L^2 * S.C_L⁻¹ ^ 2 = 1 := by rw [sq, sq, show S.C_L * S.C_L * (S.C_L⁻¹ *
        S.C_L⁻¹) = (S.C_L * S.C_L⁻¹) * (S.C_L * S.C_L⁻¹) by ring, step5_2, one_mul]
      rw [step5_1, step5_2, step5_3, step5_4]; ring
  rw [show S.C_L / S.C_L = 1 by apply div_self (ne_of_gt S.hCL), mul_one, step1, step2, step3,
    step4]
  field_simp
  rw [step5]
