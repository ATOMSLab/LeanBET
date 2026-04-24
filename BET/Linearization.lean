import Mathlib
import BET.BET_infinte
import BET.Instance
import BET.Function


namespace BET

/-- Code-level correctness: if `linearizeBET` returns `some (p,y)`,
then `p = pt.p` and `y = pt.p / (pt.n * (1 - pt.p))`, with the expected guards. -/
theorem linearizeBET_some_eq
  (pt : Point ℝ)
  (hp : pt.p < (1 : ℝ))
  (hden : BET.isZero (pt.n * ((1 : ℝ) - pt.p)) = false) :
  linearizeBET (α := ℝ) pt
    = some (pt.p, pt.p / (pt.n * ((1 : ℝ) - pt.p))) := by
  simp [linearizeBET]
  aesop


/-- Characterization lemma for `linearizeBET`. -/
theorem linearizeBET_eq_some_iff
  (pt : Point ℝ) (p y : ℝ) :
  linearizeBET (α := ℝ) pt = some (p, y) ↔
    pt.p < (1 : ℝ)
    ∧ p = pt.p
    ∧ BET.isZero (pt.n * ((1 : ℝ) - pt.p)) = false
    ∧ y = pt.p / (pt.n * ((1 : ℝ) - pt.p)) := by
  classical
  have hone : (BETLike.one : ℝ) = (1 : ℝ) := rfl
  constructor
  · intro h
    by_cases hp1 : pt.p < (1 : ℝ)
    · have hp' : pt.p < BETLike.one := by
        simpa [hone] using hp1
      let denom : ℝ := pt.n * (BETLike.one - pt.p)
      by_cases hden0 : BET.isZero denom = true
      · have : linearizeBET (α := ℝ) pt = none := by
          simp [linearizeBET, hp']
          aesop
        cases this ▸ h
      · have hdenF : BET.isZero denom = false := by
          cases hzt : BET.isZero denom with
          | false => rfl
          | true  => cases hden0 hzt
        have hs :
            linearizeBET (α := ℝ) pt = some (pt.p, pt.p / denom) := by
          simp [linearizeBET, hp', denom]
          aesop
        have hpair : (pt.p, pt.p / denom) = (p, y) := by
          have : some (pt.p, pt.p / denom) = some (p, y) := by
            simpa [hs] using h
          exact Option.some.inj this
        have hpp : pt.p = p := by
          simpa using congrArg Prod.fst hpair
        have hyy : pt.p / denom = y := by
          simpa using congrArg Prod.snd hpair
        refine ⟨hp1, ?_, ?_, ?_⟩
        · exact hpp.symm
        · have : BET.isZero (pt.n * ((1 : ℝ) - pt.p)) = false := by
            simpa [denom, hone] using hdenF
          exact this
        · exact (by simpa [denom, hone] using hyy.symm)
    · have hnot : ¬ pt.p < BETLike.one := by
        simpa [hone] using hp1
      have : linearizeBET (α := ℝ) pt = none := by
        simp [linearizeBET, hnot]
      cases this ▸ h
  · rintro ⟨hp1, hpEq, hden, hyEq⟩
    subst p
    subst y
    have hp' : pt.p < BETLike.one := by
      simpa [hone] using hp1
    have hden' : BET.isZero (pt.n * (BETLike.one - pt.p)) = false := by
      simpa [hone] using hden
    simp [linearizeBET, hone]
    aesop


/-Algebraic linearization: substituting the BET nonlinear model for `n`
makes the linearized quantity a line in `p`-/

noncomputable def betNonlinear (c nm p : ℝ) : ℝ :=
  (c * nm * p) / ((1 - p) * (1 + (c - 1) * p))

noncomputable def betLinearY (n p : ℝ) : ℝ :=
  p / (n * (1 - p))


/-- `linearizeBET` returns the `betLinearY` ordinate when it succeeds. -/
theorem linearizeBET_some_eq_betLinearY
  (pt : Point ℝ)
  (hp : pt.p < (1 : ℝ))
  (hden : BET.isZero (pt.n * ((1 : ℝ) - pt.p)) = false) :
  linearizeBET (α := ℝ) pt
    = some (pt.p, betLinearY pt.n pt.p) := by
  simpa [betLinearY] using linearizeBET_some_eq pt hp hden

theorem bet_linearization_algebra
  (c nm p : ℝ)
  (hc : c ≠ 0) (hnm : nm ≠ 0)
  (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
  betLinearY (betNonlinear c nm p) p
    = (1 / (c * nm)) + ((c - 1) / (c * nm)) * p := by
  have hCp : c * nm ≠ 0 := mul_ne_zero hc hnm
  have h1mp : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  unfold betLinearY betNonlinear
  field_simp [hCp, h1mp, hp0]

/-- Away from `P = 0`, the adsorption constant simplifies to the system ratio `C_1 / C_L`. -/
theorem adsorption_constant_eq_ratio
  (S : BET.system) {P : ℝ} (hP : P ≠ 0) :
  BET.adsorption_constant S P = S.C_1 / S.C_L := by
  change (S.C_1 * P) / (S.C_L * P) = S.C_1 / S.C_L
  exact mul_div_mul_right S.C_1 S.C_L hP

/-- `brunauer_28` is the BET nonlinear model at normalized pressure `P / P₀`, with `nm = 1`. -/
theorem brunauer_28_eq_betNonlinear_normalized
  (S : BET.system) (P : ℝ) :
  brunauer_28 S P = betNonlinear (BET.adsorption_constant S P) 1 (P / S.P₀) := by
  change BET.adsorption_constant S P * P
      / ((S.P₀ - P) * (1 + (BET.adsorption_constant S P - 1) * (P / S.P₀))) =
    betNonlinear (BET.adsorption_constant S P) 1 (P / S.P₀)
  rw [betNonlinear]
  field_simp [_root_.ne_of_gt S.hP₀]

/-- The BET nonlinear model with monolayer amount `nm`
specializes to `nm * brunauer_28` under normalized pressure. -/
theorem betNonlinear_eq_nm_mul_brunauer_28
  (S : BET.system) (nm P : ℝ) :
  betNonlinear (BET.adsorption_constant S P) nm (P / S.P₀) = nm * brunauer_28 S P := by
  rw [brunauer_28_eq_betNonlinear_normalized]
  unfold betNonlinear
  ring

/-- A convenient formulation of the bridge from `brunauer_28` to `betNonlinear`
using explicit equalities for the nonlinear parameters. -/
theorem betNonlinear_eq_nm_mul_brunauer_28_of_eq
  {S : BET.system} {P c nm p : ℝ}
  (hc : c = BET.adsorption_constant S P)
  (hp : p = P / S.P₀) :
  betNonlinear c nm p = nm * brunauer_28 S P := by
  subst c p
  exact betNonlinear_eq_nm_mul_brunauer_28 S nm P

/-- When `P ≠ 0`, the nonlinear BET parameter `c` can be read directly from the system data. -/
theorem brunauer_28_eq_betNonlinear_ratio
  (S : BET.system) {P : ℝ} (hP : P ≠ 0) :
  brunauer_28 S P = betNonlinear (S.C_1 / S.C_L) 1 (P / S.P₀) := by
  rw [brunauer_28_eq_betNonlinear_normalized, adsorption_constant_eq_ratio S hP]

/-- Scaled `brunauer_28` agrees with the standard BET nonlinear model
written using the system ratio `C_1 / C_L`. -/
theorem betNonlinear_ratio_eq_nm_mul_brunauer_28
  (S : BET.system) (nm : ℝ) {P : ℝ} (hP : P ≠ 0) :
  betNonlinear (S.C_1 / S.C_L) nm (P / S.P₀) = nm * brunauer_28 S P := by
  rw [← adsorption_constant_eq_ratio S hP, betNonlinear_eq_nm_mul_brunauer_28]

/-- Linearizing the BET model expressed via `brunauer_28` yields the same affine expression
as the standard nonlinear BET formula. -/
theorem betLinearY_nm_mul_brunauer_28
  (S : BET.system) (nm P : ℝ)
  (hnm : nm ≠ 0)
  (hP : P ≠ 0)
  (hPP₀ : P ≠ S.P₀) :
  betLinearY (nm * brunauer_28 S P) (P / S.P₀)
    = (1 / (BET.adsorption_constant S P * nm))
      + ((BET.adsorption_constant S P - 1) / (BET.adsorption_constant S P * nm)) * (P / S.P₀) := by
  have hC : BET.adsorption_constant S P ≠ 0 := by
    rw [adsorption_constant_eq_ratio S hP]
    exact div_ne_zero (_root_.ne_of_gt S.hC1) (_root_.ne_of_gt S.hCL)
  have hp0 : P / S.P₀ ≠ 0 := by
    exact div_ne_zero hP (_root_.ne_of_gt S.hP₀)
  have hp1 : P / S.P₀ ≠ 1 := by
    intro hp1
    have hEq : P = S.P₀ := by
      simpa [one_mul] using (div_eq_iff (_root_.ne_of_gt S.hP₀)).mp hp1
    exact hPP₀ hEq
  rw [← betNonlinear_eq_nm_mul_brunauer_28]
  exact bet_linearization_algebra (BET.adsorption_constant S P) nm (P / S.P₀) hC hnm hp0 hp1

/-- The same linearization statement with the adsorption constant written explicitly
as the system ratio `C_1 / C_L`. -/
theorem betLinearY_nm_mul_brunauer_28_ratio
  (S : BET.system) (nm P : ℝ)
  (hnm : nm ≠ 0)
  (hP : P ≠ 0)
  (hPP₀ : P ≠ S.P₀) :
  betLinearY (nm * brunauer_28 S P) (P / S.P₀)
    = (1 / ((S.C_1 / S.C_L) * nm))
      + (((S.C_1 / S.C_L) - 1) / ((S.C_1 / S.C_L) * nm)) * (P / S.P₀) := by
  rw [betLinearY_nm_mul_brunauer_28 S nm P hnm hP hPP₀, adsorption_constant_eq_ratio S hP]

/-- If we package the BET nonlinear model into a `Point`, `linearizeBET` returns the expected
linearized ordinate. The explicit nonzero-denominator guard is exactly the runtime condition
checked by `linearizeBET`. -/
theorem linearizeBET_nm_mul_brunauer_28_some
  (S : BET.system) (nm P : ℝ)
  (hp : P / S.P₀ < (1 : ℝ))
  (hden : BET.isZero ((nm * brunauer_28 S P) * ((1 : ℝ) - P / S.P₀)) = false) :
  linearizeBET (α := ℝ) { p := P / S.P₀, n := nm * brunauer_28 S P }
    = some (P / S.P₀, betLinearY (nm * brunauer_28 S P) (P / S.P₀)) := by
  simpa [betLinearY] using
    linearizeBET_some_eq
      ({ p := P / S.P₀, n := nm * brunauer_28 S P } : Point ℝ) hp hden

/-- Combining the bridge to `brunauer_28` with `linearizeBET` yields the affine BET line. -/
theorem linearizeBET_nm_mul_brunauer_28_line
  (S : BET.system) (nm P : ℝ)
  (hnm : nm ≠ 0)
  (hP : P ≠ 0)
  (hPP₀ : P ≠ S.P₀)
  (hp : P / S.P₀ < (1 : ℝ))
  (hden : BET.isZero ((nm * brunauer_28 S P) * ((1 : ℝ) - P / S.P₀)) = false) :
  linearizeBET (α := ℝ) { p := P / S.P₀, n := nm * brunauer_28 S P }
    = some (P / S.P₀,
      (1 / (BET.adsorption_constant S P * nm))
        + ((BET.adsorption_constant S P - 1)
            / (BET.adsorption_constant S P * nm))
            * (P / S.P₀)) := by
  rw [linearizeBET_nm_mul_brunauer_28_some S nm P hp hden,
    betLinearY_nm_mul_brunauer_28 S nm P hnm hP hPP₀]


end BET
