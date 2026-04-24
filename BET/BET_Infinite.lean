import Mathlib

open BigOperators
open Filter
open Nat
open Set

set_option linter.style.setOption false
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
### Definitions
-/
--noncomputable theorem
namespace BET
structure system :=
  (C_1 C_L s₀ P₀ : ℝ)
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
    apply mul_pos (mul_pos hx2 S.hs₀)
    exact mul_pos (sub_pos.mpr hx1) hx2
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

theorem brunauer_26_from_seq
  (hx1 : X S P < 1)
  (hx2 : 0 < X S P)
:
  V S P V₀ / A S P = V₀ * brunauer_26 S P
:= by
  have hxnorm : ‖X S P‖ < 1 := abs_lt.mpr ⟨by nlinarith, hx1⟩
  have hsum : Summable (seq S P) := by
    apply (summable_nat_add_iff 1).mp _
    simp only [seq, _root_.pow_succ', mul_assoc, Pi.div_apply]
    apply Eq.mpr (id (congrArg Summable (funext fun n => Eq.trans (Eq.trans (congrArg (HMul.hMul
      (X S P)) (Eq.trans (congrArg (HMul.hMul (X S P ^ n)) (mul_div_assoc' S.s₀ (Y S P) (X S P)))
      (mul_div_assoc' (X S P ^ n) (S.s₀ * Y S P) (X S P))))
      (mul_div_assoc' (X S P) (X S P ^ n * (S.s₀ * Y S P)) (X S P)))
      (mul_div_cancel_left₀ (X S P ^ n * (S.s₀ * Y S P)) (_root_.ne_of_gt hx2)))))
    exact (summable_geometric_of_lt_one hx2.le hx1).mul_right _
  have hsum2 : Summable (fun k : ℕ => ↑k * (seq S P k)) := by
    apply (summable_nat_add_iff 1).mp _
    simp only [seq, ← mul_assoc]
    apply Summable.mul_right _ (Summable.mul_right _ _)
    set u := fun k : ℕ => (k : ℝ) * (X S P) ^ k
    change Summable (fun (n : ℕ) => u (n + 1))
    apply (summable_nat_add_iff 1).mpr _
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm
  rw [BET.volume_adsorbed, BET.catalyst_area, hsum2.tsum_eq_zero_add, hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [mul_div_assoc, seq]
  have hseq :
      (∑' b, ↑(b + 1) * seq S P (b + 1)) / (S.s₀ + ∑' b, seq S P (b + 1)) =
        C S P * X S P / ((1 - X S P) * (1 - X S P + X S P * C S P)) := by
    simpa [Nat.cast_add, Nat.cast_one] using sequence_math S P hx1 hx2
  rw [hseq, brunauer_26]
  ring

private lemma brunauer_26_factor :
    brunauer_26 S = fun x =>
      (C S x * X S x / (1 - X S x + C S x * X S x)) * (1 - X S x)⁻¹ := by
  funext x
  rw [brunauer_26, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, ← mul_assoc]

private lemma tendsto_X_at_inv_CL {l : Filter ℝ}
    (hId : Tendsto (fun x : ℝ => x) l (nhds (1 / S.C_L))) :
    Tendsto (fun x => X S x) l (nhds 1) := by
  have hCL0 : S.C_L ≠ 0 := _root_.ne_of_gt S.hCL
  have hlin : Tendsto (fun x : ℝ => S.C_L * x) l (nhds (S.C_L * (1 / S.C_L))) :=
    (Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * (1 / S.C_L)) rfl).comp
      hId
  simpa [BET.n_layer_adsorption_rate, hCL0] using hlin

private lemma tendsto_C_at_inv_CL {l : Filter ℝ}
    (hId : Tendsto (fun x : ℝ => x) l (nhds (1 / S.C_L))) :
    Tendsto (fun x => C S x) l (nhds (S.C_1 / S.C_L)) := by
  have hCL0 : S.C_L ≠ 0 := _root_.ne_of_gt S.hCL
  have hnum : Tendsto (fun x : ℝ => S.C_1 * x) l (nhds (S.C_1 * (1 / S.C_L))) :=
    (Continuous.tendsto' (continuous_mul_left S.C_1) (1 / S.C_L) (S.C_1 * (1 / S.C_L)) rfl).comp
      hId
  have hden : Tendsto (fun x : ℝ => S.C_L * x) l (nhds (S.C_L * (1 / S.C_L))) :=
    (Continuous.tendsto' (continuous_mul_left S.C_L) (1 / S.C_L) (S.C_L * (1 / S.C_L)) rfl).comp
      hId
  have hden0 : S.C_L * (1 / S.C_L) ≠ 0 := by
    simp [hCL0]
  simpa [BET.adsorption_constant, BET.first_layer_adsorption_rate, BET.n_layer_adsorption_rate,
    Pi.div_apply, hCL0] using hnum.div hden hden0

private lemma tendsto_core_at_inv_CL {l : Filter ℝ}
    (hId : Tendsto (fun x : ℝ => x) l (nhds (1 / S.C_L))) :
    Tendsto (fun x => C S x * X S x / (1 - X S x + C S x * X S x)) l (nhds 1) := by
  have hC : Tendsto (fun x => C S x) l (nhds (S.C_1 / S.C_L)) := tendsto_C_at_inv_CL S hId
  have hX : Tendsto (fun x => X S x) l (nhds 1) := tendsto_X_at_inv_CL S hId
  have hnum : Tendsto (fun x => C S x * X S x) l (nhds (S.C_1 / S.C_L)) := by
    simpa using hC.mul hX
  have hsub : Tendsto (fun x => (1 : ℝ) - X S x) l (nhds (1 - 1)) := by
    exact Tendsto.sub (show Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) from tendsto_const_nhds) hX
  have hden : Tendsto (fun x => 1 - X S x + C S x * X S x) l (nhds (S.C_1 / S.C_L)) := by
    simpa using hsub.add (hC.mul hX)
  have hCpos : 0 < S.C_1 / S.C_L := div_pos S.hC1 S.hCL
  simpa [hCpos.ne', div_self] using hnum.div hden hCpos.ne'

lemma tendsto_at_top_at_inv_CL
  (hP : 0 < P)
:
  Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioo 0 (1 / S.C_L))) Filter.atTop
:= by
  let l := nhdsWithin (1 / S.C_L) (Set.Ioo 0 (1 / S.C_L))
  have hCL0 : S.C_L ≠ 0 := _root_.ne_of_gt S.hCL
  have hId : Tendsto (fun x : ℝ => x) l (nhds (1 / S.C_L)) := by
    simpa [l] using (tendsto_nhdsWithin_of_tendsto_nhds (f := fun x : ℝ => x) tendsto_id)
  have hCore : Tendsto (fun x => C S x * X S x / (1 - X S x + C S x * X S x)) l (nhds 1) :=
    tendsto_core_at_inv_CL S hId
  have hX : Tendsto (fun x => X S x) l (nhds 1) := tendsto_X_at_inv_CL S hId
  have hToZero : Tendsto (fun x => 1 - X S x) l (nhds 0) := by
    have hsub : Tendsto (fun x => (1 : ℝ) - X S x) l (nhds (1 - 1)) := by
      exact Tendsto.sub (show Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) from tendsto_const_nhds) hX
    simpa using hsub
  have hPos : Tendsto (fun x => 1 - X S x) l (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    change Tendsto (fun x => 1 - X S x) l (nhds 0 ⊓ 𝓟 (Set.Ioi 0))
    refine tendsto_inf.2 ⟨hToZero, ?_⟩
    refine tendsto_principal.2 ?_
    have hs : Set.Ioo 0 (1 / S.C_L) ∈ l := by
      change Set.Ioo 0 (1 / S.C_L) ∈ nhdsWithin (1 / S.C_L) (Set.Ioo 0 (1 / S.C_L))
      rw [nhdsWithin]
      rw [mem_inf_iff]
      exact ⟨Set.univ, univ_mem, Set.Ioo 0 (1 / S.C_L), mem_principal_self _, by simp⟩
    filter_upwards [hs] with x hx
    rw [Set.mem_Ioi]
    have hxmul : S.C_L * x < 1 := by
      have hmul : S.C_L * x < S.C_L * (1 / S.C_L) := mul_lt_mul_of_pos_left hx.2 S.hCL
      simpa [hCL0] using hmul
    have hpos : 0 < 1 - S.C_L * x := by
      nlinarith
    simpa [BET.n_layer_adsorption_rate] using hpos
  have hInv : Tendsto (fun x => (1 - X S x)⁻¹) l atTop := hPos.inv_tendsto_nhdsGT_zero
  simpa [l, brunauer_26_factor S] using hCore.pos_mul_atTop zero_lt_one hInv

lemma tendsto_at_bot_at_inv_CL
  (hCL : S.C_1 < S.C_L)
  (hP : 0 < P) -- hP hypothesis was added by Colin J.
:
Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1))))
  Filter.atBot
:= by
  let l := nhdsWithin (1 / S.C_L) (Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1)))
  have hCL0 : S.C_L ≠ 0 := _root_.ne_of_gt S.hCL
  have hId : Tendsto (fun x : ℝ => x) l (nhds (1 / S.C_L)) := by
    simpa [l] using (tendsto_nhdsWithin_of_tendsto_nhds (f := fun x : ℝ => x) tendsto_id)
  have hCore : Tendsto (fun x => C S x * X S x / (1 - X S x + C S x * X S x)) l (nhds 1) :=
    tendsto_core_at_inv_CL S hId
  have hX : Tendsto (fun x => X S x) l (nhds 1) := tendsto_X_at_inv_CL S hId
  have hToZero : Tendsto (fun x => 1 - X S x) l (nhds 0) := by
    have hsub : Tendsto (fun x => (1 : ℝ) - X S x) l (nhds (1 - 1)) := by
      exact Tendsto.sub (show Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) from tendsto_const_nhds) hX
    simpa using hsub
  have hNeg : Tendsto (fun x => 1 - X S x) l (nhdsWithin (0 : ℝ) (Set.Iio 0)) := by
    change Tendsto (fun x => 1 - X S x) l (nhds 0 ⊓ 𝓟 (Set.Iio 0))
    refine tendsto_inf.2 ⟨hToZero, ?_⟩
    refine tendsto_principal.2 ?_
    have hs : Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1)) ∈ l := by
      change Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1)) ∈
        nhdsWithin (1 / S.C_L) (Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1)))
      rw [nhdsWithin]
      rw [mem_inf_iff]
      exact ⟨Set.univ, univ_mem, Set.Ioo (1 / S.C_L) (1 / (S.C_L - S.C_1)),
        mem_principal_self _, by simp⟩
    filter_upwards [hs] with x hx
    rw [Set.mem_Iio]
    have hxmul : 1 < S.C_L * x := by
      have hmul : S.C_L * (1 / S.C_L) < S.C_L * x := mul_lt_mul_of_pos_left hx.1 S.hCL
      simpa [hCL0] using hmul
    have hneg : 1 - S.C_L * x < 0 := by
      nlinarith
    simpa [BET.n_layer_adsorption_rate] using hneg
  have hInv : Tendsto (fun x => (1 - X S x)⁻¹) l atBot := hNeg.inv_tendsto_nhdsLT_zero
  simpa [l, brunauer_26_factor S] using hCore.pos_mul_atBot zero_lt_one hInv

lemma tendsto_at_bot_at_inv_CL'
(hCL : S.C_L ≤ S.C_1)
(hP : 0 < P)
:
Filter.Tendsto (brunauer_26 S) (nhdsWithin (1 / S.C_L) (Set.Ioi (1 / S.C_L))) Filter.atBot
:= by
  let l := nhdsWithin (1 / S.C_L) (Set.Ioi (1 / S.C_L))
  have hCL0 : S.C_L ≠ 0 := _root_.ne_of_gt S.hCL
  have hId : Tendsto (fun x : ℝ => x) l (nhds (1 / S.C_L)) := by
    simpa [l] using (tendsto_nhdsWithin_of_tendsto_nhds (f := fun x : ℝ => x) tendsto_id)
  have hCore : Tendsto (fun x => C S x * X S x / (1 - X S x + C S x * X S x)) l (nhds 1) :=
    tendsto_core_at_inv_CL S hId
  have hX : Tendsto (fun x => X S x) l (nhds 1) := tendsto_X_at_inv_CL S hId
  have hToZero : Tendsto (fun x => 1 - X S x) l (nhds 0) := by
    have hsub : Tendsto (fun x => (1 : ℝ) - X S x) l (nhds (1 - 1)) := by
      exact Tendsto.sub (show Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) from tendsto_const_nhds) hX
    simpa using hsub
  have hNeg : Tendsto (fun x => 1 - X S x) l (nhdsWithin (0 : ℝ) (Set.Iio 0)) := by
    change Tendsto (fun x => 1 - X S x) l (nhds 0 ⊓ 𝓟 (Set.Iio 0))
    refine tendsto_inf.2 ⟨hToZero, ?_⟩
    refine tendsto_principal.2 ?_
    have hs : Set.Ioi (1 / S.C_L) ∈ l := by
      change Set.Ioi (1 / S.C_L) ∈ nhdsWithin (1 / S.C_L) (Set.Ioi (1 / S.C_L))
      rw [nhdsWithin]
      rw [mem_inf_iff]
      exact ⟨Set.univ, univ_mem, Set.Ioi (1 / S.C_L), mem_principal_self _, by simp⟩
    filter_upwards [hs] with x hx
    rw [Set.mem_Iio]
    have hxmul : 1 < S.C_L * x := by
      have hmul : S.C_L * (1 / S.C_L) < S.C_L * x := mul_lt_mul_of_pos_left hx S.hCL
      simpa [hCL0] using hmul
    have hneg : 1 - S.C_L * x < 0 := by
      nlinarith
    simpa [BET.n_layer_adsorption_rate] using hneg
  have hInv : Tendsto (fun x => (1 - X S x)⁻¹) l atBot := hNeg.inv_tendsto_nhdsLT_zero
  simpa [l, brunauer_26_factor S] using hCore.pos_mul_atBot zero_lt_one hInv

theorem brunauer_28_from_seq
(h27 : S.P₀ = 1 / S.C_L)
(hx1 : X S P < 1)
(hx2 : 0 < X S P)
(hP : 0 < P)
:
V S P V₀ / A S P = V₀ * brunauer_28 S P
:= by
  have hCL0 : S.C_L ≠ 0 := _root_.ne_of_gt S.hCL
  rw [brunauer_26_from_seq S P V₀ hx1 hx2]
  have hEq : brunauer_26 S P = brunauer_28 S P := by
    rw [brunauer_26, brunauer_28, h27]
    have hX : P / (1 / S.C_L) = X S P := by
      simp [BET.n_layer_adsorption_rate, div_eq_mul_inv, mul_comm]
    have hnum : C S P * X S P = S.C_L * (C S P * P) := by
      rw [← hX]
      field_simp [hCL0]
    have hden1 : 1 - X S P = S.C_L * (1 / S.C_L - P) := by
      rw [← hX]
      field_simp [hCL0]
    have hden2 : S.C_L * (1 / S.C_L - P) + S.C_L * (C S P * P) =
        1 + (C S P - 1) * (P / (1 / S.C_L)) := by
      field_simp [hCL0]
      ring
    rw [hnum, hden1, hden2]
    field_simp [hCL0]
  rw [hEq]

end BET
