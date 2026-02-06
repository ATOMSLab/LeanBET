import Mathlib
import BET.Instance
import BET.Function

open BET
namespace BET

set_option linter.style.commandStart false
set_option linter.style.missingEnd false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.emptyLine false


/-- Mathematical (Prop) notion: list is nondecreasing. -/
def MonotoneNondecreasing {α} [BETLike α] : List α → Prop
| [] => True
| [_] => True
| x :: y :: xs => x ≤ y ∧ MonotoneNondecreasing (y :: xs)


/-- Soundness of the exact executable monotonicity check. -/
theorem monotone_sound {α} [BETLike α] :
    ∀ xs : List α, isMonotoneNondecreasingExact xs = true → MonotoneNondecreasing xs
  | [], _ => by simp [MonotoneNondecreasing]
  | [x], _ => by simp [MonotoneNondecreasing]
  | x :: y :: xs, h => by
      -- unfold the Bool checker
      simp [isMonotoneNondecreasingExact] at h
      -- the simp above splits on the `if x ≤ y`
      -- we now have the branch where `x ≤ y` holds and the recursive check is true
      have hxy : x ≤ y := by
        -- `simp` produced `h` in the branch where `x ≤ y` is true
        -- so we can extract it by doing a by_cases split ourselves:
        by_cases h' : x ≤ y
        · exact h'
        · -- if not (x ≤ y), the function would be false, contradicting `h`
          simp [h'] at h
      -- now prove the Prop spec
      refine And.intro hxy ?_
      -- recurse
      have : isMonotoneNondecreasingExact (y :: xs) = true := by
        -- same by_cases trick to extract the recursive equality
        by_cases h' : x ≤ y
        · simpa [isMonotoneNondecreasingExact, h'] using h
        · exfalso
          simp [h'] at h
      exact monotone_sound (y :: xs) this


theorem passesBETSI_core_monotone_sound
  {α : Type} [BETLike α]
  (invert : Isotherm α → α → Option α)
  (iso : Isotherm α) (fit : BETFit α) (window : List (Point α)) (cfg : BETSIFilter α)
  (r : BETSIResult α)
  (h : passesBETSI_core invert iso fit window cfg = some r) :
  MonotoneNondecreasing (window.map (fun pt => pt.n * ((BETLike.one (α := α)) - pt.p))) ∧
  MonotoneNondecreasing ((linearizeWindow window).map Prod.snd) := by
  classical

  -- Name the exact sequences the core checks.
  set n1m : List α := window.map (fun pt => pt.n * ((BETLike.one (α := α)) - pt.p)) with hn1m
  set linY : List α := (linearizeWindow window).map Prod.snd with hlinY

  -- ------------------------------------------------------------
  -- 1) Extract: isMonotoneNondecreasingExact n1m = true
  -- ------------------------------------------------------------
  have hn1mBool : isMonotoneNondecreasingExact n1m = true := by
    cases hmono : isMonotoneNondecreasingExact n1m with
    | false =>
        -- If the check is false, the core returns none immediately.
        have : passesBETSI_core invert iso fit window cfg = none := by
          simp [passesBETSI_core]
          aesop

        -- Contradiction with h : ... = some r
        have : (none : Option (BETSIResult α)) = some r := by
          simp
          aesop
        cases this
    | true => simp

  -- ------------------------------------------------------------
  -- 2) Extract: linY ≠ []  (because the core rejects empty linY)
  -- ------------------------------------------------------------
  have hlinY_ne : linY ≠ [] := by
    intro hnil
    have : passesBETSI_core invert iso fit window cfg = none := by
      simp [passesBETSI_core]
      aesop
    have : (none : Option (BETSIResult α)) = some r := by
      simp
      aesop
    cases this

  -- ------------------------------------------------------------
  -- 3) Extract: isMonotoneNondecreasingExact linY = true
  -- ------------------------------------------------------------
  have hlinYBool : isMonotoneNondecreasingExact linY = true := by
    cases hmono : isMonotoneNondecreasingExact linY with
    | false =>
        -- If this check is false (and linY is nonempty), the core returns none.
        have : passesBETSI_core invert iso fit window cfg = none := by
          simp [passesBETSI_core]
          aesop
        have : (none : Option (BETSIResult α)) = some r := by
          simp
          aesop
        cases this
    | true => simp

  -- ------------------------------------------------------------
  -- 4) Bridge Bool checks to Prop specs using monotone_sound
  -- ------------------------------------------------------------
  refine And.intro ?_ ?_
  · exact monotone_sound n1m hn1mBool
  · exact monotone_sound linY hlinYBool


@[simp] lemma monotone_nil {α : Type} [BETLike α] :
  MonotoneNondecreasing ([] : List α) := by
  simp [MonotoneNondecreasing]

@[simp] lemma monotone_singleton {α : Type} [BETLike α] (x : α) :
  MonotoneNondecreasing [x] := by
  simp [MonotoneNondecreasing]

/-- Helper: if `x::y::xs` is monotone, then the head step `x ≤ y` holds. -/
lemma monotone_head_le_next {α : Type} [BETLike α] {x y : α} {xs : List α} :
  MonotoneNondecreasing (x :: y :: xs) → x ≤ y := by
  intro h
  simpa [MonotoneNondecreasing] using h.1

/-- Helper: if `x::y::xs` is monotone, then the tail `y::xs` is monotone. -/
lemma monotone_tail {α : Type} [BETLike α] {x y : α} {xs : List α} :
  MonotoneNondecreasing (x :: y :: xs) → MonotoneNondecreasing (y :: xs) := by
  intro h
  simpa [MonotoneNondecreasing] using h.2

/-- Completeness: if the Prop-spec monotonicity holds, the Bool checker returns true. -/
theorem monotone_complete {α : Type} [BETLike α] (xs : List α) :
  MonotoneNondecreasing (α := α) xs → isMonotoneNondecreasingExact (α := α) xs = true := by
  intro hmono
  induction xs with
  | nil => simp [isMonotoneNondecreasingExact]
  | cons x xs ih =>
      cases xs with
      | nil => simp [isMonotoneNondecreasingExact]
      | cons y ys =>
          have hxy : x ≤ y := monotone_head_le_next (x := x) (y := y) (xs := ys) hmono
          have htail : MonotoneNondecreasing (α := α) (y :: ys) :=
            monotone_tail (x := x) (y := y) (xs := ys) hmono
          have ih' : isMonotoneNondecreasingExact (α := α) (y :: ys) = true := ih htail
          -- Bool recursion uses `if x ≤ y then ... else ...`
          simp [isMonotoneNondecreasingExact, hxy, ih']


theorem monotone_iff {α : Type} [BETLike α] (xs : List α) :
  isMonotoneNondecreasingExact (α := α) xs = true ↔ MonotoneNondecreasing (α := α) xs := by
  constructor
  · intro h; exact monotone_sound (α := α) xs h
  · intro h; exact monotone_complete (α := α) xs h



/-- Minimal physical admissibility for a BET fit (as Prop). -/
def PhysAdmissible {α} [BETLike α] (fit : BETFit α) : Prop :=
  BETLike.zero (α := α) < fit.c ∧ BETLike.zero (α := α) < fit.nm

/-- Physical admissibility, matching the core gates. -/
def PhysAdmissibleLE {α : Type} [BETLike α] (fit : BETFit α) : Prop :=
  ¬ (fit.c ≤ BETLike.zero (α := α)) ∧ ¬ (fit.nm ≤ BETLike.zero (α := α))

/-- Physical admissibility in “math form”: what we say in the manuscript. -/
def PhysAdmissibleLT {α : Type} [BETLike α] (fit : BETFit α) : Prop :=
  BETLike.zero (α := α) < fit.c ∧ BETLike.zero (α := α) < fit.nm


theorem phys_complete {α : Type} [BETLike α] (fit : BETFit α) :
  PhysAdmissibleLE (α := α) fit →
  (¬ (fit.c ≤ BETLike.zero (α := α)) ∧ ¬ (fit.nm ≤ BETLike.zero (α := α))) := by
  intro h
  exact h

theorem passesBETSI_core_physical_sound
  {α : Type} [BETLike α]
  (invert : Isotherm α → α → Option α)
  (iso : Isotherm α) (fit : BETFit α) (window : List (Point α)) (cfg : BETSIFilter α)
  (r : BETSIResult α)
  (h : passesBETSI_core invert iso fit window cfg = some r) :
  PhysAdmissibleLE (α := α) fit := by
  classical
  refine And.intro ?hc ?hnm

  · intro hcBad
    have : passesBETSI_core invert iso fit window cfg = none := by
      simp [passesBETSI_core, hcBad]
    -- contradiction
    exact absurd this (by simp [h])

  · intro hnmBad
    have : passesBETSI_core invert iso fit window cfg = none := by
      simp [passesBETSI_core, hnmBad]
    -- contradiction
    exact absurd this (by simp [h])


theorem passesBETSI_core_checks_sound
  {α : Type} [BETLike α]
  (invert : Isotherm α → α → Option α)
  (iso : Isotherm α) (fit : BETFit α) (window : List (Point α)) (cfg : BETSIFilter α)
  (r : BETSIResult α)
  (h : passesBETSI_core invert iso fit window cfg = some r) :
  MonotoneNondecreasing (window.map (fun pt => pt.n * ((BETLike.one (α := α)) - pt.p))) ∧
  MonotoneNondecreasing ((linearizeWindow window).map Prod.snd) ∧
  PhysAdmissibleLE (α := α) fit := by
  have hmono := passesBETSI_core_monotone_sound (invert := invert) (iso := iso)
    (fit := fit) (window := window) (cfg := cfg) (r := r) h
  have hphys := passesBETSI_core_physical_sound (invert := invert) (iso := iso)
    (fit := fit) (window := window) (cfg := cfg) (r := r) h
  exact ⟨hmono.1, hmono.2, hphys⟩



/-- If the core returns `some r`, then the result record carries the input `fit` and `window`. -/
theorem passesBETSI_core_result_fields
  {α : Type} [BETLike α]
  (invert : Isotherm α → α → Option α)
  (iso : Isotherm α) (fit : BETFit α) (window : List (Point α)) (cfg : BETSIFilter α)
  (r : BETSIResult α)
  (h : passesBETSI_core invert iso fit window cfg = some r) :
  r.fit = fit ∧ r.window = window := by
  classical
  simp [passesBETSI_core] at h
  constructor
  · aesop
  · aesop


theorem passesBETSI_core_checks_sound_result
  {α : Type} [BETLike α]
  (invert : Isotherm α → α → Option α)
  (iso : Isotherm α) (fit : BETFit α) (window : List (Point α)) (cfg : BETSIFilter α)
  (r : BETSIResult α)
  (h : passesBETSI_core invert iso fit window cfg = some r) :
  MonotoneNondecreasing (r.window.map (fun pt => pt.n * ((BETLike.one (α := α)) - pt.p))) ∧
  MonotoneNondecreasing ((linearizeWindow r.window).map Prod.snd) ∧
  PhysAdmissibleLE (α := α) r.fit := by
  classical

  -- 1) Get the checks soundness statement about the *inputs* (fit/window)
  have h' :
      MonotoneNondecreasing (window.map (fun pt => pt.n * ((BETLike.one (α := α)) - pt.p))) ∧
      MonotoneNondecreasing ((linearizeWindow window).map Prod.snd) ∧
      PhysAdmissibleLE (α := α) fit :=
    passesBETSI_core_checks_sound
      (invert := invert) (iso := iso) (fit := fit) (window := window) (cfg := cfg) (r := r) h

  -- 2) Bridge input facts to r-field facts using your bookkeeping lemma
  have hfields : r.fit = fit ∧ r.window = window :=
    passesBETSI_core_result_fields
      (invert := invert) (iso := iso) (fit := fit) (window := window) (cfg := cfg) (r := r) h

  -- 3) Rewrite the goal using those equalities
  --    (Note: use hfields.2.symm to rewrite r.window -> window)
  simpa [hfields.1, hfields.2] using h'





end BET
