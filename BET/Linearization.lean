import Mathlib
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

noncomputable def betNonlinear (C nm p : ℝ) : ℝ :=
  (C * nm * p) / ((1 - p) * (1 + (C - 1) * p))

noncomputable def betLinearY (n p : ℝ) : ℝ :=
  p / (n * (1 - p))

theorem bet_linearization_algebra
  (C nm p : ℝ)
  (hC : C ≠ 0) (hnm : nm ≠ 0)
  (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
  betLinearY (betNonlinear C nm p) p
    = (1 / (C * nm)) + ((C - 1) / (C * nm)) * p := by
  have hCp : C * nm ≠ 0 := mul_ne_zero hC hnm
  have h1mp : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  unfold betLinearY betNonlinear
  field_simp [hCp, h1mp, hp0]






end BET
