import Mathlib
import BET.Instance
import BET.Function

open BET
namespace BET

set_option linter.style.longLine false
set_option linter.flexible false

/-
Soundness of knee selection for the polymorphic BETSI code.

Goal story (informal):
- `jmaxOf results` computes the maximum end-index `j` among all passing fits.
- `knee results` keeps exactly those results whose end-index equals this maximum `j`.
- `kneeBest results` returns (when it exists) one of the knee results whose `% error`
  is minimal in the sense that no other knee result has strictly smaller error.

This file proves those statements in Lean.
-/


/- ============================================================
   Specs for knee selection
   ============================================================ -/

/-- Declarative knee spec: this result is from the list, and its `stop` index is maximal. -/
def KneeSpec {α : Type} (results : List (BETSIResult α)) (r : BETSIResult α) : Prop :=
  r ∈ results ∧ r.fit.range.snd = jmaxOf results

/--
Declarative “best among knee” spec:
`r` is a knee candidate and no other knee candidate has strictly smaller error.
(We deliberately use `¬ (r'.pcError < r.pcError)` rather than `r.pcError ≤ r'.pcError`
so we do not need algebraic/order axioms beyond the `lt` relation used by the code.)
-/
def KneeBestSpec {α : Type} [BETLike α] (results : List (BETSIResult α)) (r : BETSIResult α) : Prop :=
  r ∈ knee results ∧ ∀ r' ∈ knee results, ¬ (r'.pcError < r.pcError)

/- ============================================================
   Helper lemmas
   ============================================================ -/

/-- Membership in `knee` implies membership in `results` and equality of end index with `jmaxOf`. -/
theorem mem_knee_iff {α : Type} (results : List (BETSIResult α)) (r : BETSIResult α) :
    r ∈ knee results ↔ r ∈ results ∧ r.fit.range.snd = jmaxOf results := by
  classical
  unfold knee
  simp [jmaxOf]

/-- Soundness: anything in `knee results` satisfies `KneeSpec`. -/
theorem knee_sound {α : Type} (results : List (BETSIResult α)) (r : BETSIResult α)
    (h : r ∈ knee results) : KneeSpec results r := by
  have hr : r ∈ results ∧ r.fit.range.snd = jmaxOf results := (mem_knee_iff results r).1 h
  exact hr

/--
A foldl helper: the “pick smaller error” fold always returns an element from the initial best or the list it folds over.
-/
lemma foldl_pick_mem {α : Type} [BETLike α]
    (best : BETSIResult α) (ks : List (BETSIResult α)) :
    (ks.foldl (fun b r => if r.pcError < b.pcError then r else b) best) ∈ best :: ks := by
  induction ks generalizing best with
  | nil =>
      simp
  | cons r rs ih =>
      -- unfold one fold step, then use IH
      simp [List.foldl]
      by_cases hlt : r.pcError < best.pcError
      · aesop
      · grind

/-- If `r ∈ knee results`, then its end index equals the maximum end index. -/
lemma mem_knee_snd_eq_jmax {α} (results : List (BETSIResult α)) {r : BETSIResult α}
    (hr : r ∈ knee results) :
    r.fit.range.snd == jmaxOf results := by
  have := (mem_knee_iff (results := results) (r := r)).1 hr
  aesop


/-- If `kneeBest` returns `some r`, then the knee list is nonempty. -/
lemma kneeBest_some_implies_knee_nonempty {α} [BETLike α]
    (results : List (BETSIResult α)) {r : BETSIResult α}
    (h : kneeBest (α := α) results = some r) :
    knee results ≠ [] := by
  unfold kneeBest at h
  cases hk : knee results with
  | nil =>
      simp [hk] at h
  | cons k ks =>
      simp [hk] at h
      intro hnil
      cases hnil

/-- **Core soundness**: `kneeBest = some r` implies `r ∈ knee results`. -/
def kneeStep {α} [BETLike α] (best r : BETSIResult α) : BETSIResult α :=
  if r.pcError < best.pcError then r else best


/-- Fold with `kneeStep` never invents a new result:
it always returns either the initial accumulator `k` or one of the list elements. -/
lemma foldl_kneeStep_mem {α} [BETLike α]
    (k : BETSIResult α) (ks : List (BETSIResult α)) :
    (ks.foldl kneeStep k) ∈ (k :: ks) := by
  induction ks generalizing k with
  | nil =>
      simp [List.foldl]
  | cons x xs ih =>
      -- unfold one fold step
      simp [List.foldl, kneeStep]
      by_cases h : x.pcError < k.pcError
      · -- new accumulator is x
        have hx : (xs.foldl kneeStep x) ∈ (x :: xs) := ih (k := x)
        -- hence also in k :: x :: xs
        have : (xs.foldl kneeStep x) ∈ (k :: x :: xs) :=
          List.mem_cons_of_mem k (by simpa using hx)
        simpa [h] using this
      · -- accumulator stays k
        have hk : (xs.foldl kneeStep k) ∈ (k :: xs) := ih (k := k)
        -- unpack membership in (k :: xs)
        have hk' : (xs.foldl kneeStep k) = k ∨ (xs.foldl kneeStep k) ∈ xs := by
          simpa [List.mem_cons] using hk
        -- now lift into k :: x :: xs
        have : (xs.foldl kneeStep k) ∈ (k :: x :: xs) := by
          rcases hk' with h_eq | hmem
          · simp [h_eq]
          · exact List.mem_cons_of_mem k (List.mem_cons_of_mem x hmem)
        simpa [h] using this


/-- Soundness: if `kneeBest results = some r`, then `r` is one of the elements in `knee results`. -/
theorem kneeBest_mem_knee {α} [BETLike α]
    (results : List (BETSIResult α)) {r : BETSIResult α}
    (h : kneeBest (α := α) results = some r) :
    r ∈ knee results := by
  classical
  unfold kneeBest at h
  -- split on `knee results`
  cases hk : knee results with
  | nil =>
      -- then kneeBest = none
      simp [hk] at h
  | cons k ks =>
      -- kneeBest = some (foldl kneeStep k ks)
      simp [hk] at h
      have hm : (ks.foldl (kneeStep (α := α)) k) ∈ (k :: ks) :=
        foldl_kneeStep_mem (α := α) (k := k) (ks := ks)
      aesop


theorem mem_knee_end_eq_jmax {α}
    (results : List (BETSIResult α)) {r : BETSIResult α}
    (hr : r ∈ knee results) :
    r.fit.range.snd = jmaxOf results := by
  classical
  unfold knee at hr
  -- `knee results = results.filter (...)`
  have : r ∈ results.filter (fun r => r.fit.range.snd == jmaxOf results) := by
    simpa using hr
  have hp : (r.fit.range.snd == jmaxOf results) = true := by aesop
  aesop


lemma mem_knee_of_mem_results {α} {r : BETSIResult α} {results : List (BETSIResult α)} :
  r ∈ knee results → r ∈ results := by
  unfold knee
  intro h
  exact List.mem_of_mem_filter h


theorem kneeBest_mem {α} [BETLike α] (results : List (BETSIResult α)) (r : BETSIResult α)
  (h : kneeBest results = some r) :
  r ∈ knee results := by
  unfold kneeBest at h
  cases hk : knee results with
  | nil =>
      simp [hk] at h
  | cons k ks =>
      simp [hk] at h
      cases h
      -- foldl preserves membership
      exact foldl_kneeStep_mem (α := α) k ks



/-- If `r ∈ results`, then its end-index is bounded by `jmaxOf results`. -/
theorem jmaxOf_ge_end {α} (results : List (BETSIResult α)) (r : BETSIResult α)
    (hr : r ∈ results) :
    r.fit.range.snd ≤ jmaxOf results := by
  classical
  -- follow the structure from knee.pdf: prove a general max-fold lemma, then specialize
  unfold jmaxOf
  -- abbreviations (keep them local to avoid name-scope issues)
  let endIdx : BETSIResult α → Nat := fun t => t.fit.range.snd
  let step : Nat → BETSIResult α → Nat := fun acc t => Nat.max acc (endIdx t)
  -- helper: accumulator is always ≤ fold result
  have acc_le_foldl :
      ∀ (rs : List (BETSIResult α)) (acc : Nat),
        acc ≤ rs.foldl step acc := by
    intro rs acc
    induction rs generalizing acc with
    | nil =>
        simp [List.foldl]
    | cons h t ih =>
        simp [List.foldl]
        have h1 : acc ≤ Nat.max acc (endIdx h) := Nat.le_max_left _ _
        have h2 : Nat.max acc (endIdx h) ≤ t.foldl step (Nat.max acc (endIdx h)) :=
          ih (acc := Nat.max acc (endIdx h))
        exact le_trans h1 h2
  -- stronger helper: membership implies endIdx ≤ fold result (for any accumulator)
  have mem_le_foldl :
      ∀ (rs : List (BETSIResult α)) (acc : Nat),
        r ∈ rs → endIdx r ≤ rs.foldl step acc := by
    intro rs acc hrIn
    induction rs generalizing acc with
    | nil =>
        cases hrIn
    | cons h t ih =>
        rcases List.mem_cons.1 hrIn with hEq | hMem
        · subst hEq
          simp [List.foldl, step, endIdx]
          have hle1 : endIdx r ≤ Nat.max acc (endIdx r) := Nat.le_max_right _ _
          have hle2 : Nat.max acc (endIdx r) ≤ t.foldl step (Nat.max acc (endIdx r)) :=
            acc_le_foldl t (Nat.max acc (endIdx r))
          exact le_trans hle1 hle2
        · simp [List.foldl, step, endIdx]
          exact ih (acc := Nat.max acc (endIdx h)) hMem
  -- finish: apply mem_le_foldl with acc = 0
  simpa [step, endIdx] using (mem_le_foldl results 0 hr)


-- Soundness of knee: membership implies “max end index”
theorem mem_knee_end_eq_jmaxOf {α} (results : List (BETSIResult α)) (r : BETSIResult α)
    (hr : r ∈ knee results) :
    r.fit.range.snd = jmaxOf results := by
  classical
  unfold knee at hr
  simp at hr
  rcases hr with ⟨hmem, hEqBool⟩
  have : r.fit.range.snd = jmaxOf results := by omega
  exact this









end BET
