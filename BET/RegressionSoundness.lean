/-
RegressionSoundness.lean

Step 1 + 2:
(1) Write Prop-level specifications for the intermediate quantities used by
    `linearRegression`.
(2) Prove “gate extraction” lemmas: if `linearRegression data = some (m,b,r2)`,
    then the length guard passed, the variance guard passed, and `(m,b,r2)` are
    exactly the closed-form values computed by the code.

This is the polymorphic (BETLike-based) soundness layer.
-/

import Mathlib
import BET.Instance
import BET.Function

namespace BET

open IO

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.missingEnd false
set_option linter.style.emptyLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.flexible false

/- ============================================================
   Step 1: Declarative “spec” definitions (polymorphic)
   ============================================================ -/

section Specs

/-- Preferred sum for ℝ proofs: uses Mathlib's `List.sum`. -/
noncomputable def listSumR (xs : List ℝ) : ℝ :=
  xs.foldl (· + ·) 0

def xsSpec (data : List (ℝ × ℝ)) : List ℝ :=
  data.map Prod.fst

def ysSpec (data : List (ℝ × ℝ)) : List ℝ :=
  data.map Prod.snd

noncomputable def nSpecR (data : List (ℝ × ℝ)) : ℝ :=
  (data.length : ℝ)

noncomputable def xBarSpecR (data : List (ℝ × ℝ)) : ℝ :=
  listSumR (xsSpec data) / nSpecR data

noncomputable def yBarSpecR (data : List (ℝ × ℝ)) : ℝ :=
  listSumR (ysSpec data) / nSpecR data

noncomputable def covSpecR (data : List (ℝ × ℝ)) : ℝ :=
  let xBar := xBarSpecR data
  let yBar := yBarSpecR data
  listSumR <| data.map (fun (x, y) => (x - xBar) * (y - yBar))

noncomputable def vrSpecR (data : List (ℝ × ℝ)) : ℝ :=
  let xBar := xBarSpecR data
  listSumR <| data.map (fun (x, _) => (x - xBar) ^ (2 : Nat))

/-- Spec: slope m = cov/vr (when vr ≠ 0). -/
noncomputable def slopeSpec (data : List (ℝ × ℝ)) : ℝ :=
  covSpecR data / vrSpecR data

/-- Spec: intercept b = ȳ - m x̄. -/
noncomputable def interceptSpec(data : List (ℝ × ℝ)) : ℝ :=
  let m := slopeSpec data
  yBarSpecR data - m * xBarSpecR data

/-- Spec: predicted y values for given (m,b). -/
def yHatSpec (data : List (ℝ × ℝ)) (m b : ℝ) : List ℝ :=
  (xsSpec data).map (fun x => m * x + b)

/-- Spec: SS_tot = Σ (y-ȳ)^2. -/
noncomputable def ssTotSpec (data : List (ℝ × ℝ)) : ℝ :=
  let yBar := yBarSpecR data
  listSum <| (ysSpec data).map (fun y => (y - yBar) ^ (2 : Nat))

/-- Spec: SS_res = Σ (y - ŷ)^2 for given (m,b). -/
noncomputable def ssResSpec (data : List (ℝ × ℝ)) (m b : ℝ) : ℝ :=
  let ys := ysSpec data
  let yHat := yHatSpec data m b
  listSum <| (List.zip ys yHat).map (fun (y, yh) => (y - yh) ^ (2 : Nat))

/--
Spec: r² with the same convention as the code:
if SS_tot = 0 then r² = 1, else r² = 1 - SS_res/SS_tot.
-/
noncomputable def r2Spec (data : List (ℝ × ℝ)) (m b : ℝ) : ℝ :=
  let ssTot := ssTotSpec data
  let ssRes := ssResSpec data m b
  if isZero ssTot then 1 else 1 - (ssRes / ssTot)


end Specs

/- ============================================================
   Step 2: Gate-extraction soundness lemmas
   ============================================================ -/


variable {α : Type} [BETLike α]


@[simp] lemma nSpec_real (data : List (ℝ × ℝ)) :
  nSpecR data = (data.length : ℝ) := rfl


/-- If regression returns `some`, then it passed the length guard (length ≥ 2). -/
theorem linearRegression_some_length
    (data : List (α × α)) {m b r2 : α}
    (h : linearRegression (α := α) data = some (m, b, r2)) :
    2 ≤ data.length := by
  classical
  by_contra hlt
  have hlen : data.length < 2 := Nat.lt_of_not_ge hlt
  -- if length < 2, the function returns none
  simp [linearRegression, hlen] at h


/-- If regression returns `some`, then it passed the `vr` nonzero guard (`isZero vr = false`). -/
theorem linearRegression_some_vr_notZero
    (data : List (ℝ × ℝ)) {m b r2 : ℝ}
    (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
    BET.isZero (vrSpecR data) = false := by
  classical
  have hlen_ge : 2 ≤ data.length := linearRegression_some_length (α := ℝ) data h
  have hlen : ¬ data.length < 2 := Nat.not_lt.mpr hlen_ge
  set vr : ℝ := vrSpecR data with hvr
  cases hz : BET.isZero vr with
  | true =>
      have : linearRegression (α := ℝ) data = none := by
        simp [linearRegression, hlen]
        aesop
      simpa [h]

  | false =>
      simpa [hvr] using hz


/-
`linearRegression` is executable (Option-returning) code.
`slopeSpec`, `interceptSpec`, `r2Spec` are the declarative/spec definitions.

This lemma is the “field-extraction bridge”:
if the code returns `some (m,b,r2)`, then those fields *equal* the spec formulas.
-/
theorem linearRegression_some_fields
  {α : Type} [BETLike α]
  (data : List (ℝ  × ℝ ))
  (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  BET.isZero (α := ℝ) (vrSpecR  data) = false ∧
  m = slopeSpec data ∧
  b = interceptSpec data ∧
  r2 = r2Spec data (slopeSpec data) (interceptSpec data) := by
  classical
  have hlen : ¬ data.length < 2 := by
    intro hlt
    simpa [linearRegression, hlt] using h
  have hspec :
      BET.isZero (α := ℝ) (vrSpecR data) = false ∧
      slopeSpec data = m ∧
      interceptSpec data = b ∧
      r2Spec data (slopeSpec data) (interceptSpec data) = r2 := by
    simpa [ linearRegression, hlen, nSpecR, xsSpec, ysSpec, xBarSpecR, yBarSpecR, covSpecR, vrSpecR, slopeSpec, interceptSpec
      , yHatSpec, ssTotSpec, ssResSpec, r2Spec] using h
  refine And.intro hspec.1 ?_
  refine And.intro ?_ ?_
  · exact hspec.2.1.symm
  refine And.intro ?_ ?_
  · exact hspec.2.2.1.symm
  · exact hspec.2.2.2.symm




--## Linear regression minimizer

/-!
Step 1 + 2 for RegressionSoundness.lean

Step 1: define the least-squares objective (SSE).
Step 2: prove the “normal-equation style” identities that characterize
        the returned slope/intercept at the spec level.
-/

/- ============================================================
   Step 1: SSE objective (spec)
   ============================================================ -/

/--
SSE(m,b) = Σ (yᵢ - (m xᵢ + b))².

In our development, this is exactly `ssResSpec`, since `ssResSpec`
is defined as a sum of squared residuals using `yHatSpec`.
-/

noncomputable def sseSpec (data : List (ℝ  × ℝ)) (m b : ℝ) : ℝ :=
  ssResSpec  data m b

@[simp] lemma sseSpec_def  (data : List (ℝ × ℝ)) (m b : ℝ) :
    sseSpec data m b = ssResSpec data m b := by rfl

@[simp] theorem interceptSpec_eq_yBar_sub_slope_mul_xBar
    (data : List (ℝ × ℝ)) :
    interceptSpec data
      = yBarSpecR data - slopeSpec data * xBarSpecR data := by simp [interceptSpec]



--## Linear regression minimizer lemmas
/-- Sum of squared errors: SSE(m,b) = Σ (y - (m x + b))^2.
We reuse your spec `ssResSpec` exactly. -/

noncomputable def sse (data : List (ℝ × ℝ)) (m b : ℝ) : ℝ := ssResSpec  data m b

/-- Best intercept for a fixed slope `m`: b(m) = ȳ - m x̄. -/
noncomputable def bOf (data : List (ℝ × ℝ)) (m : ℝ) : ℝ := yBarSpecR data - m * xBarSpecR data

/-- Residuals eᵢ(m,b) = yᵢ - (m xᵢ + b). -/
noncomputable def residuals (data : List (ℝ × ℝ)) (m b : ℝ) : List ℝ :=
  let ys := ysSpec data
  let yHat := yHatSpec data m b
  (List.zip ys yHat).map (fun (y, yh) => y - yh)


-- helper: shifting the foldl accumulator by a constant on the left
lemma foldl_add_const_left (x a : ℝ) (xs : List ℝ) :
    List.foldl (fun s t => s + t) (x + a) xs
      = x + List.foldl (fun s t => s + t) a xs := by
  induction xs generalizing a with
  | nil => simp [List.foldl]
  | cons y ys ih => simpa [List.foldl, add_assoc] using ih (a := a + y)


@[simp] lemma listSumR_nil : listSumR ([] : List ℝ) = 0 := by
  rfl

@[simp] lemma listSumR_cons (x : ℝ) (xs : List ℝ) :
  listSumR (x :: xs) = x + listSumR xs := by
  simp [listSumR, List.foldl]
  simpa [add_comm, add_left_comm, add_assoc] using
    (foldl_add_const_left x 0 xs)


-- SSE is sum of squared residuals
lemma sse_eq_sum_sq_residuals (data : List (ℝ × ℝ)) (m b : ℝ) :
  sse data m b
    =
  listSumR ((residuals data m b).map (fun e => e ^ (2 : Nat))) := by
  simp [sse, residuals, ssResSpec, listSumR]
  aesop


/-- Convenience: square on ℝ. -/
@[simp] lemma sq (x : ℝ) : x^2 = x*x := by
  ring


/-- Residuals shift when changing intercept: e(m,b) = e(m,b0) - (b - b0). -/
lemma residuals_shift_intercept (data : List (ℝ × ℝ)) (m b b0 : ℝ) :
    residuals data m b
      =
    (residuals data m b0).map (fun e => e - (b - b0)) := by
  induction data with
  | nil => simp [residuals, ysSpec, xsSpec, yHatSpec]
  | cons a as ih =>
      cases a with
      | mk x y =>
          simp [residuals, ysSpec, xsSpec, yHatSpec] at ih ⊢
          constructor
          · ring
          · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ih


/-- Add-constant lemma: sum (x + c) = sum x + n*c. -/
lemma listSumR_map_add_const (xs : List ℝ) (c : ℝ) :
    listSumR (xs.map (fun x => x + c))
      = listSumR xs + (xs.length : ℝ) * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih]
      ring


/-- Sub-constant lemma: sum (x - c) = sum x - n*c. -/
lemma listSumR_map_sub_const (xs : List ℝ) (c : ℝ) :
    listSumR (xs.map (fun x => x - c))
      = listSumR xs - (xs.length : ℝ) * c := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using
    (listSumR_map_add_const xs (-c))



@[simp] lemma xsSpec_length (data : List (ℝ  × ℝ)) :
    (xsSpec data).length = data.length := by
  simp [xsSpec]

lemma xsSpec_ne_nil_of_length_ne_zero (data : List (ℝ × ℝ)) (hn : data.length ≠ 0) :
    xsSpec data ≠ [] := by
  intro hxs
  have : data.length = 0 := by
    have hxlen : (xsSpec  data).length = 0 := by simpa [hxs]
    simpa [xsSpec_length data] using hxlen
  exact hn this

lemma sum_centered_xs_eq_zero
  (data : List (ℝ × ℝ)) :
  listSumR ((xsSpec data).map (fun x => x - xBarSpecR data)) = 0 := by
  classical
  by_cases hlen : data.length = 0
  · -- degenerate: data = [], hence xsSpec = [], sum = 0
    have hdata : data = [] := by
      simpa using hlen
    simp [hdata, xsSpec, xBarSpecR, nSpecR, listSumR_nil]

  · -- non-degenerate
    have hn : (data.length : ℝ) ≠ 0 := by
      intro hcast
      have : data.length = 0 := by
        exact_mod_cast hcast
      exact hlen this

    -- use your helper: sum (x - c) = sum x - (len xs) * c
    have hsub :
      listSumR ((xsSpec data).map (fun x => x - xBarSpecR data))
        =
      listSumR (xsSpec data) - ((xsSpec data).length : ℝ) * xBarSpecR data := by
      simpa using
        (listSumR_map_sub_const (xs := xsSpec data) (c := xBarSpecR data))

    -- length of xsSpec equals length of data
    have hxlen : (xsSpec data).length = data.length := by
      simp [xsSpec]

    calc
      listSumR ((xsSpec data).map (fun x => x - xBarSpecR data))
          = listSumR (xsSpec data) - ((xsSpec data).length : ℝ) * xBarSpecR data := hsub
      _   = listSumR (xsSpec data) - (data.length : ℝ) * xBarSpecR data := by simpa [hxlen]
      _   = listSumR (xsSpec data) - (data.length : ℝ) * (listSumR (xsSpec data) / (data.length : ℝ)) := by simp [xBarSpecR, nSpecR]
      _   = 0 := by field_simp [hn]; ring

lemma residual_bOf_eq_centered
  (data : List (ℝ × ℝ)) (m : ℝ) (x y : ℝ) :
  y - (m * x + bOf data m) = (y - yBarSpecR data) - m * (x - xBarSpecR data) := by
  simp [bOf]
  ring


lemma residuals_eq_map
  (data : List (ℝ × ℝ)) (m b : ℝ) :
  residuals data m b = data.map (fun (x, y) => y - (m * x + b)) := by
  classical
  induction data with
  | nil =>
      simp [residuals, xsSpec, ysSpec, yHatSpec]
  | cons xy xs ih =>
      cases xy with
      | mk x y =>
          simp only [List.map_cons]
          exact (by simpa [residuals, xsSpec, ysSpec, yHatSpec] using ih)

/-
lemma residual_bOf_eq_centered_pointwise
  (data : List (ℝ × ℝ)) (m : ℝ) :
  ∀ (a b : ℝ), (a, b) ∈ data →
    b - (m * a + bOf data m) = b - yBarSpecR data - m * (a - xBarSpecR data) := by
  intro a b hab
  simp [bOf]
  ring
-/


lemma residuals_bOf_eq_centered
  (data : List (ℝ × ℝ)) (m : ℝ) :
  residuals data m (bOf data m) = data.map (fun (x, y) => (y - yBarSpecR data) - m * (x - xBarSpecR data)) := by
  classical
  simp [residuals_eq_map]
  intro a b hab
  simp [bOf]
  ring

lemma sum_centered_ys_eq_zero (data : List (ℝ × ℝ)) :
  listSumR ((ysSpec data).map (fun y => y - yBarSpecR data)) = 0 := by
  classical
  by_cases hlen : data.length = 0
  · have hdata : data = [] := by simpa using hlen
    simp [hdata, ysSpec, yBarSpecR, nSpecR, listSumR]
  · have hn : (data.length : ℝ) ≠ 0 := by
      intro hcast
      have : data.length = 0 := by
        exact_mod_cast hcast
      exact hlen this
    have hsub :
      listSumR ((ysSpec data).map (fun y => y - yBarSpecR data))
        =
      listSumR (ysSpec data) - ((ysSpec data).length : ℝ) * yBarSpecR data := by
      simpa using
        (listSumR_map_sub_const (xs := ysSpec data) (c := yBarSpecR data))
    have hylen : (ysSpec data).length = data.length := by
      simp [ysSpec]
    calc
      listSumR ((ysSpec data).map (fun y => y - yBarSpecR data))
          = listSumR (ysSpec data) - ((ysSpec data).length : ℝ) * yBarSpecR data := hsub
      _   = listSumR (ysSpec data) - (data.length : ℝ) * yBarSpecR data := by
              simpa [hylen]
      _   = listSumR (ysSpec data) - (data.length : ℝ) *
              (listSumR (ysSpec data) / (data.length : ℝ)) := by
              simp [yBarSpecR, nSpecR]
      _   = 0 := by
              field_simp [hn]
              ring

lemma listSum_eq_listSumR (xs : List ℝ) :
    listSum (α := ℝ) xs = listSumR xs := by
  unfold listSum listSumR
  change xs.foldl (· + ·) (BETLike.zero (α := ℝ)) = xs.foldl (· + ·) 0
  rfl

lemma ssTotSpec_eq_listSumR
  (data : List (ℝ × ℝ)) :
  ssTotSpec data
    =
    let yBar := yBarSpecR data
    listSumR (data.map (fun (x, y) => (y - yBar) ^ (2 : Nat))) := by
  classical
  unfold ssTotSpec
  simp [ysSpec, listSum_eq_listSumR, listSumR]
  rfl


lemma listSumR_map_add {β : Type} (xs : List β) (f g : β → ℝ) :
    listSumR (xs.map (fun t => f t + g t))
      =
    listSumR (xs.map f) + listSumR (xs.map g) := by
  induction xs with
  | nil =>
      simp [listSumR]
  | cons a xs ih =>
      simp [List.map, listSumR_cons, ih]
      ring


lemma listSumR_map_mul_const {β : Type} (xs : List β) (c : ℝ) (f : β → ℝ) :
    listSumR (xs.map (fun t => c * f t))
      =
    c * listSumR (xs.map f) := by
  induction xs with
  | nil =>
      simp [listSumR]
  | cons a xs ih =>
      -- rewrite listSumR on cons and use IH
      simp [List.map, listSumR_cons, ih]
      ring

lemma listSumR_map_neg {β : Type} (xs : List β) (f : β → ℝ) :
    listSumR (xs.map (fun t => - f t))
      =
    - listSumR (xs.map f) := by
  induction xs with
  | nil =>
      simp [listSumR]
  | cons a xs ih =>
      -- reduce map/cons and use listSumR_cons
      simp [List.map, listSumR_cons, ih]
      ring


lemma listSumR_map_sub {β : Type} (xs : List β) (f g : β → ℝ) :
    listSumR (xs.map (fun t => f t - g t))
      =
    listSumR (xs.map f) - listSumR (xs.map g) := by
  simp [sub_eq_add_neg, listSumR_map_add, listSumR_map_neg]


lemma sq_eq_mul (t : ℝ) : t ^ (2 : Nat) = t * t := by
  simp [pow_two]


lemma ssResSpec_eq_sum_sq_residuals (data : List (ℝ × ℝ)) (m b : ℝ) :
  ssResSpec data m b
    =
  listSumR ((residuals data m b).map (fun e => e * e)) := by
  classical
  unfold ssResSpec
  simp [listSum_eq_listSumR]
  unfold residuals
  simp
  aesop


lemma sse_bOf_quadratic
  (data : List (ℝ × ℝ)) (m : ℝ) :
  sse data m (bOf data m)
    =
    ssTotSpec data - 2 * m * covSpecR data + (m ^ (2 : Nat)) * vrSpecR data := by
  classical
  unfold sse
  rw [ssResSpec_eq_sum_sq_residuals]

  -- rewrite residuals at bOf into centered form (your lemma)
  have hcenter :
      residuals data m (bOf data m)
        =
      data.map (fun xy =>
        xy.2 - yBarSpecR data - m * (xy.1 - xBarSpecR data)) := by
    simpa using (residuals_bOf_eq_centered (data := data) (m := m))
  have hcenterSq :
      (residuals data m (bOf data m)).map (fun e => e * e)
        =
      (data.map (fun xy =>
        xy.2 - yBarSpecR data - m * (xy.1 - xBarSpecR data))).map (fun e => e * e) := by
    simpa using congrArg (fun L => L.map (fun e => e * e)) hcenter

  rw [hcenterSq]
  clear hcenterSq hcenter

  -- Abbreviate bars and centered parts
  set xBar := xBarSpecR data
  set yBar := yBarSpecR data
  let A : (ℝ × ℝ) → ℝ := fun xy => xy.2 - yBar
  let B : (ℝ × ℝ) → ℝ := fun xy => xy.1 - xBar

  have hrewrite :
      (data.map (fun xy => xy.2 - yBarSpecR data - m * (xy.1 - xBarSpecR data))).map (fun e => e * e)
        =
      data.map (fun xy => (A xy - m * B xy) * (A xy - m * B xy)) := by
    simp [List.map_map]
    intro xy hxy
    simp [List.map_map, A, B, xBar, yBar]


  -- Expand the square: (A - mB)^2 = A^2 - 2mAB + m^2 B^2
  have hexpand :
      data.map (fun xy => (A xy - m * B xy) * (A xy - m * B xy))
        =
      data.map (fun xy =>
        (A xy * A xy) - (2 * m) * (A xy * B xy) + (m ^ (2 : Nat)) * (B xy * B xy)) := by
    apply List.map_congr_left
    intro xy hxy
    ring
    -- 1) First normalize hrewrite so it matches yBar/xBar (not yBarSpecR/xBarSpecR)
  have hrewrite' :
      List.map (fun e => e * e)
          (List.map (fun xy => xy.2 - yBar - m * (xy.1 - xBar)) data)
        =
      List.map (fun xy => (A xy - m * B xy) * (A xy - m * B xy)) data := by
    simpa [xBar, yBar] using hrewrite

  -- 2) Rewrite inside listSumR using congrArg
  have hsum1 := congrArg listSumR hrewrite'
  rw [hsum1]
  clear hsum1 hrewrite' hrewrite

  -- 3) Now lift hexpand through listSumR too
  have hsum2 := congrArg listSumR hexpand
  rw [hsum2]
  clear hsum2 hexpand

  have hsplit1 :
      listSumR (data.map (fun xy =>
        (A xy * A xy) - (2 * m) * (A xy * B xy) + (m ^ (2 : Nat)) * (B xy * B xy)))
        =
      listSumR (data.map (fun xy => (A xy * A xy) - (2 * m) * (A xy * B xy)))
        +
      listSumR (data.map (fun xy => (m ^ (2 : Nat)) * (B xy * B xy))) := by
    simpa [add_assoc] using
      (listSumR_map_add (xs := data)
        (f := fun xy => (A xy * A xy) - (2 * m) * (A xy * B xy))
        (g := fun xy => (m ^ (2 : Nat)) * (B xy * B xy)))
  rw [hsplit1]
  clear hsplit1

  have hsplit2 :
      listSumR (data.map (fun xy => (A xy * A xy) - (2 * m) * (A xy * B xy)))
        =
      listSumR (data.map (fun xy => A xy * A xy))
        -
      listSumR (data.map (fun xy => (2 * m) * (A xy * B xy))) := by
    simpa using
      (listSumR_map_sub (xs := data)
        (f := fun xy => A xy * A xy)
        (g := fun xy => (2 * m) * (A xy * B xy)))
  rw [hsplit2]
  clear hsplit2

  -- pull constants out
  have hconst1 :
      listSumR (data.map (fun xy => (2 * m) * (A xy * B xy)))
        =
      (2 * m) * listSumR (data.map (fun xy => A xy * B xy)) := by
    simpa [mul_assoc] using
      (listSumR_map_mul_const (xs := data) (c := (2 * m)) (f := fun xy => A xy * B xy))

  have hconst2 :
      listSumR (data.map (fun xy => (m ^ (2 : Nat)) * (B xy * B xy)))
        =
      (m ^ (2 : Nat)) * listSumR (data.map (fun xy => B xy * B xy)) := by
    simpa [mul_assoc] using
      (listSumR_map_mul_const (xs := data) (c := (m ^ (2 : Nat))) (f := fun xy => B xy * B xy))

  rw [hconst1, hconst2]
  clear hconst1 hconst2

  have hTot :
      listSumR (data.map (fun xy => A xy * A xy)) = ssTotSpec data := by
    -- use the ssTotSpec_eq_listSumR lemma
    simpa [A, yBar, xBar] using (ssTotSpec_eq_listSumR (data := data)).symm
  rw [hTot]
  clear hTot

  -- 2) A*B sum = covSpecR (up to commutativity)
  have hCov :
      listSumR (data.map (fun xy => A xy * B xy)) = covSpecR data := by
    unfold covSpecR
    simp [A, B, xBar, yBar, mul_comm, mul_left_comm, mul_assoc]
  rw [hCov]
  clear hCov

  -- 3) B*B sum = vrSpecR (since (x-xBar)^2 = (x-xBar)*(x-xBar))
  have hVr :
      listSumR (data.map (fun xy => B xy * B xy)) = vrSpecR data := by
    unfold vrSpecR
    simp [B, xBar]
  rw [hVr]



lemma quadratic_min_at_slope
  (data : List (ℝ × ℝ)) (m : ℝ)
  (hvr : 0 < vrSpecR data) :
  ssTotSpec data - 2 * m * covSpecR data + m ^ (2 : Nat) * vrSpecR data
    ≥
  ssTotSpec data - 2 * (slopeSpec data) * covSpecR data
    + (slopeSpec data) ^ (2 : Nat) * vrSpecR data := by
  classical

  -- abbreviations
  set vr : ℝ := vrSpecR data
  set cov : ℝ := covSpecR data
  have hvr' : 0 < vr := by
    simpa [vr] using hvr

  -- introduce s = cov/vr so ring never sees division later
  set s : ℝ := cov / vr

  -- slopeSpec = cov/vr = s
  have hslope : slopeSpec data = s := by
    simp [s, slopeSpec, covSpecR, vrSpecR, cov, vr]

  -- crucial bridge: cov = s * vr
  have hcov : cov = s * vr := by
    -- s = cov/vr  =>  s*vr = cov  (need vr ≠ 0)
    have hne : vr ≠ 0 := ne_of_gt hvr'
    dsimp [s]
    field_simp [hne]

  -- compute the difference as a square times vr
  have hdiff :
      (ssTotSpec data - 2 * m * cov + m ^ (2 : Nat) * vr)
        - (ssTotSpec data - 2 * s * cov + s ^ (2 : Nat) * vr)
      =
      vr * (m - s) ^ (2 : Nat) := by
    -- expand squares
    simp [pow_two]
    -- eliminate cov in favor of s*vr so ring can close
    simp [hcov]
    ring

  have hvr_nonneg : 0 ≤ vr := le_of_lt hvr'
  have hsq_nonneg : 0 ≤ (m - s) ^ (2 : Nat) := by
    -- square is nonnegative
    simpa [pow_two] using sq_nonneg (m - s)

  have hdiff_nonneg :
      0 ≤
      (ssTotSpec data - 2 * m * cov + m ^ (2 : Nat) * vr)
        - (ssTotSpec data - 2 * s * cov + s ^ (2 : Nat) * vr) := by
    show 0 ≤
      (ssTotSpec data - 2 * m * cov + m ^ (2 : Nat) * vr)
        - (ssTotSpec data - 2 * s * cov + s ^ (2 : Nat) * vr)
    -- now rewrite using hdiff
    rw [hdiff]
    have hsq : 0 ≤ (m - s) ^ (2 : Nat) := by
      simpa [pow_two] using sq_nonneg (m - s)
    exact mul_nonneg hvr_nonneg hsq

  have hmain :
      ssTotSpec data - 2 * m * cov + m ^ (2 : Nat) * vr
        ≥
      ssTotSpec data - 2 * s * cov + s ^ (2 : Nat) * vr := by
    linarith

  simpa [cov, vr, hslope] using hmain


lemma sse_bOf_minimized_at_slope
  (data : List (ℝ × ℝ)) (m : ℝ)
  (hvr : 0 < vrSpecR data) :
  ssResSpec data (slopeSpec data) (bOf data (slopeSpec data))
    ≤
  ssResSpec data m (bOf data m) := by

  have hq_m :
      ssResSpec data m (bOf data m)
        =
      ssTotSpec data - 2 * m * covSpecR data + m ^ (2 : Nat) * vrSpecR data := by
    simpa [sse] using (sse_bOf_quadratic (data := data) (m := m))

  have hq_s :
      ssResSpec data (slopeSpec data) (bOf data (slopeSpec data))
        =
      ssTotSpec data - 2 * (slopeSpec data) * covSpecR data
        + (slopeSpec data) ^ (2 : Nat) * vrSpecR data := by
    simpa [sse] using (sse_bOf_quadratic (data := data) (m := slopeSpec data))

  have hquad :
      ssTotSpec data - 2 * m * covSpecR data + m ^ (2 : Nat) * vrSpecR data
        ≥
      ssTotSpec data - 2 * (slopeSpec data) * covSpecR data
        + (slopeSpec data) ^ (2 : Nat) * vrSpecR data :=
    quadratic_min_at_slope (data := data) (m := m) hvr

  linarith [hq_m, hq_s, hquad]


lemma listSumR_map_const {β : Type} (c : ℝ) (xs : List β) :
    listSumR (xs.map (fun _ => c)) = (xs.length : ℝ) * c := by
  induction xs with
  | nil =>
      simp [listSumR]
  | cons a xs ih =>
      simp [listSumR_cons, ih, List.map, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc, add_comm, add_left_comm]
      aesop



lemma ssResSpec_eq_listSumR_residuals_sq
  (data : List (ℝ × ℝ)) (m b : ℝ) :
  ssResSpec data m b
    =
  listSumR ((residuals data m b).map (fun e => e * e)) := by
  unfold ssResSpec residuals ysSpec yHatSpec xsSpec
  simp [listSumR, pow_two, List.map_map, List.zip_map_right, List.zip_map_left, Function.comp]
  aesop




lemma listSumR_yHatSpec (data : List (ℝ × ℝ)) (m b : ℝ) :
    listSumR (yHatSpec data m b)
      =
    m * listSumR (xsSpec data) + (data.length : ℝ) * b := by

  simp [yHatSpec, xsSpec]

  have hadd :
      listSumR (List.map (fun x => m * x + b) (List.map Prod.fst data))
        =
      listSumR (List.map (fun x => m * x) (List.map Prod.fst data))
        +
      listSumR (List.map (fun _ => b) (List.map Prod.fst data)) := by
    simpa [listSumR] using
      (listSumR_map_add (xs := List.map Prod.fst data)
        (f := fun x => m * x) (g := fun _ => b))

  have hm :
      listSumR (List.map (fun x => m * x) (List.map Prod.fst data))
        =
      m * listSumR (List.map Prod.fst data) := by
    simpa using
      (listSumR_map_mul_const (xs := List.map Prod.fst data) (c := m) (f := fun x => x))

  have hb :
      listSumR (List.map (fun _ => b) (List.map Prod.fst data))
        =
      ((List.map Prod.fst data).length : ℝ) * b := by
    simpa using
      (listSumR_map_const (xs := List.map Prod.fst data) (c := b))

  have hlen : (List.map Prod.fst data).length = data.length := by
    simp

  have hcomp_add :
    List.map ((fun x ↦ m * x + b) ∘ Prod.fst) data
      =
    List.map (fun x ↦ m * x + b) (List.map Prod.fst data) := by
     simpa [List.map_map]

  have hcomp_m :
    List.map ((fun x ↦ m * x) ∘ Prod.fst) data
      =
    List.map (fun x ↦ m * x) (List.map Prod.fst data) := by
     simpa [List.map_map]

  have hcomp_b :
    List.map ((fun x ↦ b) ∘ Prod.fst) data
      =
    List.map (fun x ↦ b) (List.map Prod.fst data) := by
    simpa [List.map_map]

  calc
    listSumR (List.map ((fun x ↦ m * x + b) ∘ Prod.fst) data) = listSumR (List.map (fun x ↦ m * x + b) (List.map Prod.fst data)) := by simpa using hcomp_add
  _ = listSumR (List.map (fun x ↦ m * x) (List.map Prod.fst data)) + listSumR (List.map (fun x ↦ b) (List.map Prod.fst data)) := by exact hadd
  _ = m * listSumR (List.map Prod.fst data) + ↑data.length * b := by rw [hm, hb, hlen]
  _ = m * listSumR (List.map Prod.fst data) + ↑data.length * b := by rfl





/-- Sum of residuals is zero when using the optimal intercept `bOf data m`. -/
lemma listSumR_residuals_bOf_eq_zero
    (data : List (ℝ × ℝ)) (m : ℝ)
    (hlen : data.length ≠ 0) :
    listSumR (residuals data m (bOf data m)) = 0 := by
  classical
  have hn : (data.length : ℝ) ≠ 0 := by exact_mod_cast hlen

  have hres : residuals data m (bOf data m) = data.map (fun xy => xy.2 - (m * xy.1 + bOf data m)) := by
    simpa [residuals_eq_map]

  let f : (ℝ × ℝ) → ℝ := fun xy => xy.2
  let g : (ℝ × ℝ) → ℝ := fun xy => (m * xy.1 + bOf data m)

  have hsplit :
      listSumR (List.map (fun xy : ℝ × ℝ => xy.2 + (-bOf data m + -(m * xy.1))) data)
        =
      listSumR (List.map f data) + - listSumR (List.map g data) := by
    have hfun :
        (fun xy : ℝ × ℝ => xy.2 + (-bOf data m + -(m * xy.1)))
          = (fun xy : ℝ × ℝ => f xy + - g xy) := by
      funext xy
      simp [f, g]
    simpa [hfun] using
      (by
        calc
          listSumR (List.map (fun xy => f xy + - g xy) data)
              =
            listSumR (List.map f data) + listSumR (List.map (fun xy => - g xy) data) := by
              simpa using (listSumR_map_add (xs := data) (f := f) (g := fun xy => - g xy))
          _ =
            listSumR (List.map f data) + - listSumR (List.map g data) := by
              simpa using congrArg (fun t => listSumR (List.map f data) + t)
                (listSumR_map_neg (xs := data) (f := g)))

  have hf : data.map f = ysSpec data := by simp [ysSpec, f]
  have hg : data.map g = (yHatSpec data m (bOf data m)) := by simp [yHatSpec, xsSpec, g, List.map_map]

  have hmap :
      List.map (fun xy => xy.2 - (m * xy.1 + bOf data m)) data
        = List.map (fun xy => xy.2 + (-bOf data m + -(m * xy.1))) data := by
    apply List.map_congr_left
    intro xy hxy
    ring

  have hmap :
    List.map (fun xy ↦ xy.2 - (m * xy.1 + bOf data m)) data
      = List.map (fun xy ↦ xy.2 + (-bOf data m + -(m * xy.1))) data := by
     apply List.map_congr_left
     intro xy hxy
     ring


  have hsum :
      listSumR (residuals data m (bOf data m))
        = listSumR (ysSpec data) - listSumR (yHatSpec data m (bOf data m)) := by
    calc
      listSumR (residuals data m (bOf data m)) = listSumR (List.map (fun xy ↦ xy.2 - (m * xy.1 + bOf data m)) data) := by simpa [hres]
      _ = listSumR (List.map (fun xy ↦ xy.2 + (-bOf data m + -(m * xy.1))) data) := by simpa [hmap]
      _ = listSumR (List.map f data) + - listSumR (List.map g data) := by simpa using hsplit
      _ = listSumR (List.map f data) - listSumR (List.map g data) := by simp [sub_eq_add_neg]
      _ = listSumR (ysSpec data) - listSumR (yHatSpec data m (bOf data m)) := by simp [hf, hg]

  have hyHat :
      listSumR (yHatSpec data m (bOf data m))
        = m * listSumR (xsSpec data) + (data.length : ℝ) * (bOf data m) := by
    simpa using (listSumR_yHatSpec (data := data) (m := m) (b := bOf data m))

  have hbOf :
      (data.length : ℝ) * (bOf data m) = listSumR (ysSpec data) - m * listSumR (xsSpec data) := by
    simp [bOf, yBarSpecR, xBarSpecR, hn]
    field_simp [hn]

  calc
    listSumR (residuals data m (bOf data m)) = listSumR (ysSpec data) - listSumR (yHatSpec data m (bOf data m)) := hsum
    _ = listSumR (ysSpec data) - (m * listSumR (xsSpec data) + (data.length : ℝ) * (bOf data m)) := by simp [hyHat]
    _ = listSumR (ysSpec data) - (m * listSumR (xsSpec data) + (listSumR (ysSpec data) - m * listSumR (xsSpec data))) := by simp [hbOf]
    _ = 0 := by ring


lemma sse_minimized_at_slope_bOf
  (data : List (ℝ × ℝ)) (m : ℝ)
  (hvr : 0 < vrSpecR data) :
  ssResSpec data (slopeSpec data) (bOf data (slopeSpec data))
    ≤
  ssResSpec data m (bOf data m) := by
  have hquad := quadratic_min_at_slope data m hvr

  have : ssTotSpec data
            - 2 * slopeSpec data * covSpecR data
            + slopeSpec data ^ 2 * vrSpecR data
          ≤
          ssTotSpec data
            - 2 * m * covSpecR data
            + m ^ 2 * vrSpecR data := by
    exact hquad

  calc
    ssResSpec data (slopeSpec data) (bOf data (slopeSpec data)) =
      ssTotSpec data - 2 * slopeSpec data * covSpecR data + slopeSpec data ^ 2 * vrSpecR data := by
      simpa using (sse_bOf_quadratic (data := data) (m := slopeSpec data))
    _ ≤ ssTotSpec data - 2 * m * covSpecR data + m ^ 2 * vrSpecR data := this
    _ = ssResSpec data m (bOf data m) := by
      symm
      simpa using (sse_bOf_quadratic (data := data) (m := m))



lemma ssResSpec_shift_intercept
  (data : List (ℝ × ℝ)) (m b : ℝ) (hlen : data.length ≠ 0) :
  ssResSpec data m b
    =
  ssResSpec data m (bOf data m)
    + (data.length : ℝ) * (b - bOf data m) ^ (2 : Nat) := by
  classical

  let r : List ℝ := residuals data m (bOf data m)
  let d : ℝ := b - bOf data m
  have hn : (data.length : ℝ) ≠ 0 := by
    exact_mod_cast hlen

  have hshift : residuals data m b = (residuals data m (bOf data m)).map (fun e => e - (b - bOf data m)) := by
    simpa [d, r] using residuals_shift_intercept (data := data) (m := m) (b := b) (b0 := bOf data m)

  have hsum0 : listSumR r = 0 := by simpa [r] using listSumR_residuals_bOf_eq_zero (data := data) (m := m) hlen

  have hrlen : r.length = data.length := by simp [r, residuals, ysSpec, yHatSpec, xsSpec]

  have hb :
      ssResSpec data m b = listSumR ((residuals data m b).map (fun e => e * e)) := by
    simpa using ssResSpec_eq_listSumR_residuals_sq (data := data) (m := m) (b := b)

  have hbOf :
      ssResSpec data m (bOf data m)
        =
      listSumR (r.map (fun e => e * e)) := by
    simpa [r] using ssResSpec_eq_listSumR_residuals_sq (data := data) (m := m) (b := bOf data m)

  rw [hb, hbOf]
  have hshift' : residuals data m b = r.map (fun e => e - d) := by
    simpa [r, d] using hshift
  rw [hshift']
  have hsq :
      (fun e : ℝ => (e - d) * (e - d))
        =
      (fun e : ℝ => e * e + ((-2 * d) * e + d * d)) := by
    funext e
    ring
  simp [List.map_map, hsq]
  have hsplit1 :
      listSumR (r.map (fun e => e * e + ((-2 * d) * e + d * d))) = listSumR (r.map (fun e => e * e)) +
      listSumR (r.map (fun e => ((-2 * d) * e + d * d))) := by
    simpa using (listSumR_map_add (xs := r) (f := fun e => e * e) (g := fun e => ((-2 * d) * e + d * d)))

  have hsplit2 :
      listSumR (r.map (fun e => ((-2 * d) * e + d * d))) = listSumR (r.map (fun e => (-2 * d) * e)) +
      listSumR (r.map (fun _ => d * d)) := by
    simpa using (listSumR_map_add (xs := r) (f := fun e => (-2 * d) * e) (g := fun _ => d * d))

  have hmul :
      listSumR (r.map (fun e => (-2 * d) * e)) = (-2 * d) * listSumR r := by
    simpa using (listSumR_map_mul_const (xs := r) (c := (-2 * d)) (f := fun e => e))

  have hconst :
      listSumR (r.map (fun _ => d * d)) = (r.length : ℝ) * (d * d) := by
    simpa using (listSumR_map_const (xs := r) (c := d * d))

  have hcomp :
      List.map ((fun e ↦ e * e) ∘ fun e ↦ e - d) r = List.map (fun e ↦ (e - d) * (e - d)) r := by
    ext e; rfl

  calc
    listSumR (List.map ((fun e ↦ e * e) ∘ fun e ↦ e - d) r) = listSumR (List.map (fun e ↦ (e - d) * (e - d)) r) := by simpa [hcomp]
    _ = listSumR (List.map (fun e ↦ e * e + (-2 * d * e + d * d)) r) := by simpa [hsq]
    _ = listSumR (List.map (fun e ↦ e * e) r) + listSumR (List.map (fun e ↦ -2 * d * e + d * d) r) := by exact hsplit1
    _ = listSumR (List.map (fun e ↦ e * e) r) + (listSumR (List.map (fun e ↦ -2 * d * e) r) + listSumR (List.map (fun _ ↦ d * d) r)) := by
      simpa [add_assoc] using congrArg (fun t => listSumR (List.map (fun e ↦ e * e) r) + t) hsplit2
    _ = listSumR (List.map (fun e ↦ e * e) r) + ((-2 * d) * listSumR r) + ((r.length : ℝ) * (d * d)) := by
      rw [hmul, hconst]; ring_nf
    _ = listSumR (List.map (fun e ↦ e * e) r) + ((r.length : ℝ) * (d * d)) := by simp [hsum0, add_assoc, mul_assoc]
    _ = listSumR (List.map (fun e ↦ e * e) r) + ((data.length : ℝ) * (d * d)) := by simpa [hrlen]
    _ = listSumR (List.map (fun e ↦ e * e) r) + (data.length : ℝ) * ((b - bOf data m) * (b - bOf data m)) := by simp [d, mul_assoc]


lemma ssResSpec_minimized_at_bOf
  (data : List (ℝ × ℝ)) (m b : ℝ)
  (hlen : data.length ≠ 0) :
  ssResSpec data m (bOf data m) ≤ ssResSpec data m b := by
  have hshift := ssResSpec_shift_intercept (data := data) (m := m) (b := b) hlen
  rw [hshift]
  have hnonneg :
      0 ≤ (data.length : ℝ) * ((b - bOf data m) * (b - bOf data m)) := by
    have hlen_nonneg : 0 ≤ (data.length : ℝ) := by
      exact Nat.cast_nonneg data.length
    have hsq_nonneg : 0 ≤ (b - bOf data m) * (b - bOf data m) := by
      nlinarith
    exact mul_nonneg hlen_nonneg hsq_nonneg
  aesop


lemma ssResSpec_minimized_at_slope_and_bOf
  (data : List (ℝ × ℝ)) (m b : ℝ)
  (hlen : data.length ≠ 0)
  (hvr : 0 < vrSpecR data) :
  ssResSpec data (slopeSpec data) (bOf data (slopeSpec data))
    ≤
  ssResSpec data m b := by
  have hbmin : ssResSpec data m (bOf data m) ≤ ssResSpec data m b := by
    exact ssResSpec_minimized_at_bOf (data := data) (m := m) (b := b) hlen

  have hmslope :
      ssResSpec data (slopeSpec data) (bOf data (slopeSpec data))
        ≤
      ssResSpec data m (bOf data m) := by
    exact sse_minimized_at_slope_bOf (data := data) (m := m) hvr

  exact le_trans hmslope hbmin


lemma interceptSpec_eq_bOf_slopeSpec
  (data : List (ℝ × ℝ)) :
  interceptSpec data = bOf data (slopeSpec data) := by simp [interceptSpec, bOf]


--## The main theorem: least squares residual is minimized at slope and intercept
lemma ssResSpec_minimized_at_slope_and_intercept
  (data : List (ℝ × ℝ)) (m b : ℝ)
  (hlen : data.length ≠ 0)
  (hvr : 0 < vrSpecR data) :
  ssResSpec data (slopeSpec data) (interceptSpec data)
    ≤
  ssResSpec data m b := by
  have h := ssResSpec_minimized_at_slope_and_bOf (data := data) (m := m) (b := b) hlen hvr
  simpa [interceptSpec_eq_bOf_slopeSpec] using h


lemma sse_minimized_at_slope_and_intercept
  (data : List (ℝ × ℝ)) (m b : ℝ)
  (hlen : data.length ≠ 0)
  (hvr : 0 < vrSpecR data) :
  sse data (slopeSpec data) (interceptSpec data)
    ≤
  sse data m b := by
  simpa [sse] using
    (ssResSpec_minimized_at_slope_and_intercept
      (data := data) (m := m) (b := b) hlen hvr)



/-- Helper: `BETLike.ofNat` for ℝ is coercion. -/
@[simp] lemma ofNat_eq_cast (n : Nat) : (BETLike.ofNat (α := ℝ) n) = (n : ℝ) := by rfl



theorem linearRegression_returns_slope_intercept
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  m = slopeSpec data ∧ b = interceptSpec data := by
  classical

  -- length guard
  by_cases hlen : data.length < 2
  · have : linearRegression (α := ℝ) data = none := by
      simp [linearRegression, hlen]
    cases this ▸ h

  · have hlen' : ¬ data.length < 2 := hlen

    -- name the exec locals
    set n   : ℝ := BETLike.ofNat data.length with hn
    set xs  : List ℝ := data.map Prod.fst with hxs
    set ys  : List ℝ := data.map Prod.snd with hys
    set xBar : ℝ := listSum xs / n with hxBar
    set yBar : ℝ := listSum ys / n with hyBar
    set cov : ℝ := listSum (data.map (fun (x, y) => (x - xBar) * (y - yBar))) with hcov
    set vr  : ℝ := listSum (data.map (fun (x, _) => (x - xBar) ^ (2 : Nat))) with hvr

    -- variance guard
    by_cases hvr0 : BET.isZero vr
    · have : HasIsZero.isZero (listSum (List.map (fun x => (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                  (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ))) data)) = true := by simpa [hvr, hxBar, hxs, hn] using hvr0

      -- Now show the regression result is none, contradict h
      have : linearRegression (α := ℝ) data = none := by
        simp [linearRegression, hlen', hn, hxs, hys, hxBar, hyBar, hcov, hvr, hvr0]
        aesop
      cases this ▸ h

    · have hExec : HasIsZero.isZero (listSum (List.map (fun x => (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                      (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ))) data)) = false ∧
          listSum (List.map (fun x => (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                      (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ))) data) / listSum (List.map (fun x =>
                    (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) * (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                  data) = m ∧ listSum (List.map Prod.snd data) / (data.length : ℝ) - listSum (List.map
                        (fun x =>
                          (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                            (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                        data) /
                    listSum
                      (List.map
                        (fun x =>
                          (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                        data) *
                  (listSum (List.map Prod.fst data) / (data.length : ℝ))
            =
            b
          ∧
          (if
                HasIsZero.isZero
                    (listSum
                      (List.map
                        ((fun y =>
                            (y - listSum (List.map Prod.snd data) / (data.length : ℝ)) *
                              (y - listSum (List.map Prod.snd data) / (data.length : ℝ))) ∘
                          Prod.snd)
                        data)) =
                  true then
              BETLike.one
            else
              BETLike.one -
                listSum
                    (List.map (fun x => (x.1 - x.2) * (x.1 - x.2))
                      ((List.map Prod.snd data).zip
                        (List.map
                          ((fun x =>
                              listSum
                                      (List.map
                                        (fun x =>
                                          (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                                            (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                                        data) /
                                    listSum
                                      (List.map
                                        (fun x =>
                                          (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                                        data) *
                                  x +
                                (listSum (List.map Prod.snd data) / (data.length : ℝ) -
                                  listSum
                                        (List.map
                                          (fun x =>
                                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                                              (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                                          data) /
                                      listSum
                                        (List.map
                                          (fun x =>
                                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                                              (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                                          data) *
                                    (listSum (List.map Prod.fst data) / (data.length : ℝ))) ) ∘
                            Prod.fst)
                          data))) /
                  listSum
                    (List.map
                      ((fun y =>
                          (y - listSum (List.map Prod.snd data) / (data.length : ℝ)) *
                            (y - listSum (List.map Prod.snd data) / (data.length : ℝ))) ∘
                        Prod.snd)
                      data)) =
            r2 := by
        -- This is exactly your "re-simp from scratch" step:
        -- it produces the conjunction that includes `isZero(vr)=false`.
        simpa [linearRegression, hlen', hn, hxs, hys, hxBar, hyBar, hcov, hvr, hvr0] using h

      -- Extract slope/intercept equalities from the conjunction.
      have hm_exec :
          listSum
                (List.map
                  (fun x =>
                    (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                      (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                  data) /
              listSum
                (List.map
                  (fun x =>
                    (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                      (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                  data)
            =
            m :=
        hExec.2.1

      have hb_exec :
          listSum (List.map Prod.snd data) / (data.length : ℝ) -
                listSum
                      (List.map
                        (fun x =>
                          (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                            (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                        data) /
                    listSum
                      (List.map
                        (fun x =>
                          (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                        data) *
                  (listSum (List.map Prod.fst data) / (data.length : ℝ))
            =
            b :=
        hExec.2.2.1

      -- Now bridge to spec. (This is the part you already planned.)
      have hm : m = slopeSpec data := by
        -- Turn hm_exec around and rewrite to your spec formula.
        have : m =
            listSum
                  (List.map
                    (fun x =>
                      (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                        (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                    data) /
                listSum
                  (List.map
                    (fun x =>
                      (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                        (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                    data) := by
          simpa using hm_exec.symm
        -- If your `listSum` on ℝ is definitional to `listSumR`, this simp closes.
        -- Otherwise, insert your lemma rewriting `listSum` -> `listSumR` here.
        simpa [slopeSpec, covSpecR, vrSpecR, xBarSpecR, yBarSpecR,
               xsSpec, ysSpec, nSpecR, listSumR] using this

      have hb : b = interceptSpec data := by
        have : b =
            listSum (List.map Prod.snd data) / (data.length : ℝ) -
                  listSum
                        (List.map
                          (fun x =>
                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                              (x.2 - listSum (List.map Prod.snd data) / (data.length : ℝ)))
                          data) /
                      listSum
                        (List.map
                          (fun x =>
                            (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)) *
                              (x.1 - listSum (List.map Prod.fst data) / (data.length : ℝ)))
                          data) *
                    (listSum (List.map Prod.fst data) / (data.length : ℝ)) := by
          simpa using hb_exec.symm
        -- Use hm and unfold interceptSpec
        simpa [interceptSpec, slopeSpec, covSpecR, vrSpecR, xBarSpecR, yBarSpecR,
               xsSpec, ysSpec, nSpecR, listSumR, hm] using this

      exact ⟨hm, hb⟩


--## The main theorem: if the executable returns (m,b,r2), then m,b match the spec.
theorem linearRegression_returns_spec
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  linearRegression (α := ℝ) data
    =
    some (slopeSpec data, interceptSpec data, r2) := by
  have hmb : m = slopeSpec data ∧ b = interceptSpec data :=
    linearRegression_returns_slope_intercept (data := data) (m := m) (b := b) (r2 := r2) h
  rcases hmb with ⟨hm, hb⟩
  simpa [hm, hb] using h


theorem linearRegression_returns_slope
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  m = slopeSpec data := by
  exact (linearRegression_returns_slope_intercept (data := data) (m := m) (b := b) (r2 := r2) h).1

theorem linearRegression_returns_intercept
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  b = interceptSpec data := by
  exact (linearRegression_returns_slope_intercept (data := data) (m := m) (b := b) (r2 := r2) h).2

theorem linearRegression_certifies_minimizer
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  ssResSpec data (slopeSpec data) (interceptSpec data)
    ≤ ssResSpec data m b := by
  have hmb :
      m = slopeSpec data ∧ b = interceptSpec data :=
    linearRegression_returns_slope_intercept (data := data) (m := m) (b := b) (r2 := r2) h
  rcases hmb with ⟨hm, hb⟩
  simpa [hm, hb]




--## BET Parameter Soundness theorem

-- Spec-side extraction from regression coefficients
noncomputable def nmFromLine (intercept slope : ℝ) : ℝ := (intercept + slope)⁻¹

noncomputable def cFromLine (intercept slope : ℝ) : ℝ := 1 + slope / intercept

-- Optional: monolayer pressure from C (if you use it)
noncomputable def p_nmFromC (c : ℝ) : ℝ := 1 / (Real.sqrt c + 1)



theorem betExtraction_sound
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  nmFromLine b m = nmFromLine (interceptSpec data) (slopeSpec data)
  ∧
  cFromLine b m = cFromLine (interceptSpec data) (slopeSpec data) := by
  -- bridge executable m,b to spec slope/intercept
  have hmb :
      m = slopeSpec data ∧ b = interceptSpec data :=
    linearRegression_returns_slope_intercept (data := data) (m := m) (b := b) (r2 := r2) h
  rcases hmb with ⟨hm, hb⟩
  constructor
  · -- Nm soundness
    simpa [hb, hm]
  · -- C soundness
    simpa [hb, hm]






end BET
