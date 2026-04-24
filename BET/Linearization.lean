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


/- Algebraic linearization: the normalized Brunauer 28 form becomes affine
under the BET transform. -/

theorem linearization_of_brunauer_fraction
  (c nm p : ℝ)
  (hc : c ≠ 0) (hnm : nm ≠ 0)
  (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
  p / ((((c * nm * p) / ((1 - p) * (1 + (c - 1) * p)))) * (1 - p))
    = (1 / (c * nm)) + ((c - 1) / (c * nm)) * p := by
  have hCp : c * nm ≠ 0 := mul_ne_zero hc hnm
  have h1mp : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  calc
    p / ((((c * nm * p) / ((1 - p) * (1 + (c - 1) * p)))) * (1 - p))
      = p / ((c * nm * p) / (1 + (c - 1) * p)) := by
          field_simp [h1mp]
    _ = (1 + (c - 1) * p) / (c * nm) := by
          field_simp [hCp, hp0]
    _ = (1 / (c * nm)) + ((c - 1) / (c * nm)) * p := by
          field_simp [hCp]

/-- Away from `P = 0`, the adsorption constant simplifies to the system ratio `C_1 / C_L`. -/
theorem adsorption_constant_eq_ratio
  (S : BET.system) {P : ℝ} (hP : P ≠ 0) :
  BET.adsorption_constant S P = S.C_1 / S.C_L := by
  change (S.C_1 * P) / (S.C_L * P) = S.C_1 / S.C_L
  exact mul_div_mul_right S.C_1 S.C_L hP

/-- Scaling `brunauer_28` by the monolayer amount `nm`
puts it into the normalized-pressure form used in BET linearization. -/
theorem nm_mul_brunauer_28_eq_normalized_fraction
  (S : BET.system) (nm P : ℝ) :
  nm * brunauer_28 S P =
    ((BET.adsorption_constant S P) * nm * (P / S.P₀)) /
      ((1 - P / S.P₀) * (1 + (BET.adsorption_constant S P - 1) * (P / S.P₀))) := by
  have hP₀ : S.P₀ ≠ 0 := _root_.ne_of_gt S.hP₀
  change nm
      * (BET.adsorption_constant S P * P
          / ((S.P₀ - P) * (1 + (BET.adsorption_constant S P - 1) * (P / S.P₀)))) =
    ((BET.adsorption_constant S P) * nm * (P / S.P₀)) /
      ((1 - P / S.P₀) * (1 + (BET.adsorption_constant S P - 1) * (P / S.P₀)))
  field_simp [hP₀]

/-- Linearizing the Brunauer 28 model yields the affine BET expression
with the adsorption constant written as `adsorption_constant S P`. -/
theorem brunauer_28_linearization_adsorption_constant
  (S : BET.system) (nm P : ℝ)
  (hnm : nm ≠ 0)
  (hP : P ≠ 0)
  (hPP₀ : P ≠ S.P₀) :
  (P / S.P₀) / ((nm * brunauer_28 S P) * (1 - P / S.P₀))
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
  rw [nm_mul_brunauer_28_eq_normalized_fraction]
  exact linearization_of_brunauer_fraction
    (BET.adsorption_constant S P) nm (P / S.P₀) hC hnm hp0 hp1

/-- The same linearization statement with the adsorption constant written explicitly
as the system ratio `C_1 / C_L`. -/
theorem brunauer_28_linearization_ratio
  (S : BET.system) (nm P : ℝ)
  (hnm : nm ≠ 0)
  (hP : P ≠ 0)
  (hPP₀ : P ≠ S.P₀) :
  (P / S.P₀) / ((nm * brunauer_28 S P) * (1 - P / S.P₀))
    = (1 / ((S.C_1 / S.C_L) * nm))
      + (((S.C_1 / S.C_L) - 1) / ((S.C_1 / S.C_L) * nm)) * (P / S.P₀) := by
  rw [brunauer_28_linearization_adsorption_constant S nm P hnm hP hPP₀,
    adsorption_constant_eq_ratio S hP]

/-- Manuscript-friendly form: the Brunauer 28 isotherm becomes affine after BET linearization. -/
theorem brunauer_28_linearization
  (S : BET.system) (nm P : ℝ)
  (hnm : 0 < nm)
  (hP : 0 < P)
  (hPP₀ : P < S.P₀) :
  (P / S.P₀) / ((nm * brunauer_28 S P) * (1 - P / S.P₀))
    = (1 / ((S.C_1 / S.C_L) * nm))
      + (((S.C_1 / S.C_L) - 1) / ((S.C_1 / S.C_L) * nm)) * (P / S.P₀) := by
  exact brunauer_28_linearization_ratio S nm P hnm.ne' hP.ne' (ne_of_lt hPP₀)

/-- If we package the Brunauer 28 model into a `Point`, `linearizeBET` returns the expected
linearized ordinate. The explicit nonzero-denominator guard is exactly the runtime condition
checked by `linearizeBET`. -/
theorem linearizeBET_nm_mul_brunauer_28_some
  (S : BET.system) (nm P : ℝ)
  (hp : P / S.P₀ < (1 : ℝ))
  (hden : BET.isZero ((nm * brunauer_28 S P) * ((1 : ℝ) - P / S.P₀)) = false) :
  linearizeBET (α := ℝ) { p := P / S.P₀, n := nm * brunauer_28 S P }
    = some (P / S.P₀, (P / S.P₀) / ((nm * brunauer_28 S P) * (1 - P / S.P₀))) := by
  simpa using
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
    brunauer_28_linearization_adsorption_constant S nm P hnm hP hPP₀]


end BET
