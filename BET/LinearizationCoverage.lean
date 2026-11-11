import BET.Function

/-!
# The regression uses every point of the window

On UiO-66 the misread point `p = 9.0` was silently dropped by
`linearizeBET` (which ignores points with `p ≥ 1`), so the fit used 48 points
while the window — and `nPoints` — said 49.

The theorem `fit_uses_every_point` rules this out: if every point of the
isotherm can be linearised, then for every window the regression is computed
from all `nPoints` points.  `Execution.lean` checks `allLinearizable` before
running, so the theorem's assumption holds for every run that gets past it.
-/

namespace BET

/-- Every point can be put through the BET linearisation
(`p < 1` and `n·(1 − p) ≠ 0`). -/
def allLinearizable {α} [BETLike α] (iso : Isotherm α) : Bool :=
  iso.all (fun pt => (linearizeBET pt).isSome)

theorem linearizeWindow_length {α} [BETLike α] (w : List (Point α))
    (h : ∀ pt ∈ w, (linearizeBET pt).isSome = true) :
    (linearizeWindow w).length = w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : (linearizeBET a).isSome = true := h a (List.mem_cons_self ..)
    have hw : ∀ pt ∈ w, (linearizeBET pt).isSome = true :=
      fun pt hpt => h pt (List.mem_cons_of_mem a hpt)
    have ih' := ih hw
    unfold linearizeWindow at ih' ⊢
    cases hl : linearizeBET a with
    | none => rw [hl] at ha; cases ha
    | some b =>
      rw [List.filterMap_cons, hl]
      simp only [List.length_cons]
      rw [ih']

/-- Every point of a window comes from the isotherm. -/
theorem allWindows_points_mem {α} (iso : Isotherm α) (s e : Nat) (w : List (Point α))
    (hw : (s, e, w) ∈ allWindows iso) : ∀ x ∈ w, x ∈ iso := by
  unfold allWindows at hw
  intro x hx
  by_cases hn : iso.length < 2
  · simp only [hn, if_true] at hw
    exact absurd hw (List.not_mem_nil)
  · simp only [hn, if_false] at hw
    rw [List.mem_flatMap] at hw
    obtain ⟨st, _, hw⟩ := hw
    rw [List.mem_map] at hw
    obtain ⟨sp, _, heq⟩ := hw
    have hw' : List.take (sp - st + 1) (List.drop st iso) = w := (Prod.mk.inj (Prod.mk.inj heq).2).2
    rw [← hw'] at hx
    exact List.mem_of_mem_drop (List.mem_of_mem_take hx)

/-- `nPoints` is the number of points in the window. -/
theorem fitWindow_nPoints {α} [BETLike α] (w : List (Point α)) (r : Nat × Nat) (fit : BETFit α)
    (h : fitWindow w r = some fit) : fit.nPoints = w.length := by
  unfold fitWindow at h
  simp only at h
  cases hr : linearRegression (linearizeWindow w) with
  | none => rw [hr] at h; dsimp only [bind, Option.bind] at h; cases h
  | some v =>
    obtain ⟨slope, intercept, r2⟩ := v
    rw [hr] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

/-- **The regression uses every point of the window.**  If every point of the
isotherm can be linearised, then for every window that is fitted the
regression data has exactly `nPoints` points — no point is silently dropped. -/
theorem fit_uses_every_point {α} [BETLike α] (iso : Isotherm α)
    (h : allLinearizable iso = true)
    (s e : Nat) (w : List (Point α)) (hw : (s, e, w) ∈ allWindows iso)
    (fit : BETFit α) (hfit : fitWindow w (s, e) = some fit) :
    (linearizeWindow w).length = fit.nPoints := by
  rw [fitWindow_nPoints w (s, e) fit hfit]
  apply linearizeWindow_length
  intro pt hpt
  unfold allLinearizable at h
  rw [List.all_eq_true] at h
  exact h pt (allWindows_points_mem iso s e w hw pt hpt)

end BET
