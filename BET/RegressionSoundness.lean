import Mathlib
import BET.Instance
import BET.Function

namespace BET
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
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
noncomputable def interceptSpec (data : List (ℝ × ℝ)) : ℝ :=
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
  have hlen : ¬ data.length < 2 := by
    exact Nat.not_lt.mpr (linearRegression_some_length (α := ℝ) data h)
  set vr : ℝ := vrSpecR data with hvr
  cases hz : BET.isZero vr with
  | true =>
      have hz' :
          BET.isZero
            (listSum
              (data.map
                (fun x => (x.1 - listSum (data.map Prod.fst) / BETLike.ofNat data.length) ^ (2 : Nat)))) = true := by
        simpa [hvr, vrSpecR, xBarSpecR, nSpecR, xsSpec] using hz
      have hz'' :
          HasIsZero.isZero
            (listSum
              (data.map
                (fun x => (x.1 - listSum (data.map Prod.fst) / BETLike.ofNat data.length) ^ (2 : Nat)))) = true := by
        simpa [BET.isZero] using hz'
      have : linearRegression (α := ℝ) data = none := by
        unfold linearRegression
        rw [if_neg hlen]
        dsimp
        simp [hz'']
      rw [this] at h
      cases h
  | false =>
      simpa [hvr] using hz


/-
`linearRegression` is executable (Option-returning) code.
`slopeSpec`, `interceptSpec`, `r2Spec` are the declarative/spec definitions.

This lemma is the “field-extraction bridge”:
if the code returns `some (m,b,r2)`, then those fields *equal* the spec formulas.
-/
theorem linearRegression_some_fields
  (data : List (ℝ × ℝ))
  (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  BET.isZero (α := ℝ) (vrSpecR data) = false ∧
  m = slopeSpec data ∧
  b = interceptSpec data ∧
  r2 = r2Spec data (slopeSpec data) (interceptSpec data) := by
  classical
  have hlen : ¬ data.length < 2 := by
    intro hlt
    simp [linearRegression, hlt] at h
  have hspec :
      BET.isZero (α := ℝ) (vrSpecR data) = false ∧
      slopeSpec data = m ∧
      interceptSpec data = b ∧
      r2Spec data (slopeSpec data) (interceptSpec data) = r2 := by
    simpa [
      linearRegression, hlen, nSpecR, xsSpec, ysSpec, xBarSpecR, yBarSpecR,
      covSpecR, vrSpecR, slopeSpec, interceptSpec, yHatSpec, ssTotSpec,
      ssResSpec, r2Spec
    ] using h
  exact ⟨hspec.1, hspec.2.1.symm, hspec.2.2.1.symm, hspec.2.2.2.symm⟩




--## Linear regression minimizer

/- ============================================================
   Step 1: SSE objective (spec)
   ============================================================ -/

@[simp] theorem interceptSpec_eq_yBar_sub_slope_mul_xBar
    (data : List (ℝ × ℝ)) :
    interceptSpec data
      = yBarSpecR data - slopeSpec data * xBarSpecR data := by simp [interceptSpec]



--## Linear regression minimizer lemmas
/-- Sum of squared errors: SSE(m,b) = Σ (y - (m x + b))^2.
We reuse your spec `ssResSpec` exactly. -/

noncomputable def sse (data : List (ℝ × ℝ)) (m b : ℝ) : ℝ :=
  ssResSpec data m b

/-- Best intercept for a fixed slope `m`: b(m) = ȳ - m x̄. -/
noncomputable def bOf (data : List (ℝ × ℝ)) (m : ℝ) : ℝ :=
  yBarSpecR data - m * xBarSpecR data

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



@[simp] lemma xsSpec_length (data : List (ℝ × ℝ)) :
  (xsSpec data).length = data.length := by
  simp [xsSpec]

lemma xsSpec_ne_nil_of_length_ne_zero (data : List (ℝ × ℝ)) (hn : data.length ≠ 0) :
    xsSpec data ≠ [] := by
  intro hxs
  have : data.length = 0 := by
    have hxlen : (xsSpec data).length = 0 := by
      simp [hxs]
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
      _ = listSumR (xsSpec data) - (data.length : ℝ) * xBarSpecR data := by
        simp [hxlen]
      _ = listSumR (xsSpec data) - (data.length : ℝ) *
          (listSumR (xsSpec data) / (data.length : ℝ)) := by
        simp [xBarSpecR, nSpecR]
      _ = 0 := by
        field_simp [hn]
        ring

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


lemma residuals_bOf_eq_centered
  (data : List (ℝ × ℝ)) (m : ℝ) :
  residuals data m (bOf data m) =
    data.map (fun (x, y) => (y - yBarSpecR data) - m * (x - xBarSpecR data)) := by
  classical
  rw [residuals_eq_map]
  apply List.map_congr_left
  intro xy hxy
  rcases xy with ⟨x, y⟩
  exact residual_bOf_eq_centered (data := data) (m := m) (x := x) (y := y)

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
      _ = listSumR (ysSpec data) - (data.length : ℝ) * yBarSpecR data := by
        simp [hylen]
      _ = listSumR (ysSpec data) - (data.length : ℝ) *
          (listSumR (ysSpec data) / (data.length : ℝ)) := by
        simp [yBarSpecR, nSpecR]
      _ = 0 := by
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
    listSumR (data.map (fun (_, y) => (y - yBar) ^ (2 : Nat))) := by
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

lemma ssResSpec_eq_sum_sq_residuals (data : List (ℝ × ℝ)) (m b : ℝ) :
  ssResSpec data m b
    =
  listSumR ((residuals data m b).map (fun e => e * e)) := by
  classical
  unfold ssResSpec residuals ysSpec yHatSpec xsSpec
  rw [listSum_eq_listSumR]
  simp_rw [pow_two, List.map_map]
  refine congrArg listSumR ?_
  apply List.map_congr_left
  intro x hx
  rcases x with ⟨y, yh⟩
  simp [Function.comp]


lemma sse_bOf_quadratic
  (data : List (ℝ × ℝ)) (m : ℝ) :
  sse data m (bOf data m)
    =
    ssTotSpec data - 2 * m * covSpecR data + (m ^ (2 : Nat)) * vrSpecR data := by
  classical
  unfold sse
  rw [ssResSpec_eq_sum_sq_residuals]
  set xBar := xBarSpecR data
  set yBar := yBarSpecR data
  let A : (ℝ × ℝ) → ℝ := fun xy => xy.2 - yBar
  let B : (ℝ × ℝ) → ℝ := fun xy => xy.1 - xBar
  have hcenterSq :
      listSumR ((residuals data m (bOf data m)).map (fun e => e * e))
        =
      listSumR (data.map (fun xy => (A xy - m * B xy) * (A xy - m * B xy))) := by
    rw [residuals_bOf_eq_centered (data := data) (m := m)]
    simp only [List.map_map]
    apply congrArg listSumR
    apply List.map_congr_left
    intro xy hxy
    rcases xy with ⟨x, y⟩
    simp [A, B, xBar, yBar]
  rw [hcenterSq]
  have hexpand :
      data.map (fun xy => (A xy - m * B xy) * (A xy - m * B xy))
        =
      data.map (fun xy =>
        (A xy * A xy) - (2 * m) * (A xy * B xy) + (m ^ (2 : Nat)) * (B xy * B xy)) := by
    apply List.map_congr_left
    intro xy hxy
    ring
  have hsum2 := congrArg listSumR hexpand
  rw [hsum2]
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
    simpa [A, yBar, xBar, pow_two] using (ssTotSpec_eq_listSumR (data := data)).symm
  rw [hTot]
  clear hTot
  -- 2) A*B sum = covSpecR (up to commutativity)
  have hCov :
      listSumR (data.map (fun xy => A xy * B xy)) = covSpecR data := by
    unfold covSpecR
    simp [A, B, xBar, yBar, mul_comm]
  rw [hCov]
  clear hCov
  -- 3) B*B sum = vrSpecR (since (x-xBar)^2 = (x-xBar)*(x-xBar))
  have hVr :
      listSumR (data.map (fun xy => B xy * B xy)) = vrSpecR data := by
    unfold vrSpecR
    simp [B, xBar, pow_two]
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
    -- s = cov/vr => s*vr = cov (need vr ≠ 0)
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
  | cons _ xs ih =>
      rw [List.map, listSumR_cons, ih]
      simp [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      ring

lemma listSumR_yHatSpec (data : List (ℝ × ℝ)) (m b : ℝ) :
    listSumR (yHatSpec data m b)
      =
    m * listSumR (xsSpec data) + (data.length : ℝ) * b := by
  unfold yHatSpec xsSpec
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
  calc
    listSumR (List.map (fun x ↦ m * x + b) (List.map Prod.fst data)) =
        listSumR (List.map (fun x ↦ m * x) (List.map Prod.fst data)) +
          listSumR (List.map (fun x ↦ b) (List.map Prod.fst data)) := by
      exact hadd
    _ = m * listSumR (List.map Prod.fst data) + ↑data.length * b := by
      rw [hm, hb, hlen]
    _ = m * listSumR (List.map Prod.fst data) + ↑data.length * b := by
      rfl


/-- Sum of residuals is zero when using the optimal intercept `bOf data m`. -/
lemma listSumR_residuals_bOf_eq_zero
    (data : List (ℝ × ℝ)) (m : ℝ)
    (_hlen : data.length ≠ 0) :
    listSumR (residuals data m (bOf data m)) = 0 := by
  rw [residuals_bOf_eq_centered (data := data) (m := m)]
  rw [listSumR_map_sub]
  have hys : listSumR (data.map (fun xy => xy.2 - yBarSpecR data)) = 0 := by
    simpa [ysSpec] using sum_centered_ys_eq_zero data
  have hxs :
      listSumR (data.map (fun xy => m * (xy.1 - xBarSpecR data)))
        =
      m * listSumR (data.map (fun xy => xy.1 - xBarSpecR data)) := by
    simpa using
      (listSumR_map_mul_const (xs := data) (c := m)
        (f := fun xy => xy.1 - xBarSpecR data))
  have hxs0 : listSumR (data.map (fun xy => xy.1 - xBarSpecR data)) = 0 := by
    simpa [xsSpec] using sum_centered_xs_eq_zero data
  rw [hys, hxs, hxs0]
  ring


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
  have hshift :
      residuals data m b =
        (residuals data m (bOf data m)).map (fun e => e - (b - bOf data m)) := by
    simpa [d, r] using
      residuals_shift_intercept (data := data) (m := m) (b := b) (b0 := bOf data m)
  have hsum0 : listSumR r = 0 := by
    simpa [r] using listSumR_residuals_bOf_eq_zero (data := data) (m := m) hlen
  have hrlen : r.length = data.length := by simp [r, residuals, ysSpec, yHatSpec, xsSpec]
  have hb :
      ssResSpec data m b = listSumR ((residuals data m b).map (fun e => e * e)) := by
    simpa using ssResSpec_eq_sum_sq_residuals (data := data) (m := m) (b := b)
  have hbOf :
      ssResSpec data m (bOf data m)
        =
      listSumR (r.map (fun e => e * e)) := by
    simpa [r] using ssResSpec_eq_sum_sq_residuals (data := data) (m := m) (b := bOf data m)
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
  have hsplit1 :
      listSumR (r.map (fun e => e * e + ((-2 * d) * e + d * d))) =
        listSumR (r.map (fun e => e * e)) +
          listSumR (r.map (fun e => (-2 * d) * e + d * d)) := by
    simpa using
      (listSumR_map_add (xs := r) (f := fun e => e * e)
        (g := fun e => (-2 * d) * e + d * d))
  have hsplit2 :
      listSumR (r.map (fun e => (-2 * d) * e + d * d)) =
        listSumR (r.map (fun e => (-2 * d) * e)) +
          listSumR (r.map (fun _ => d * d)) := by
    simpa using
      (listSumR_map_add (xs := r) (f := fun e => (-2 * d) * e) (g := fun _ => d * d))
  have hmul :
      listSumR (r.map (fun e => (-2 * d) * e)) = (-2 * d) * listSumR r := by
    simpa using (listSumR_map_mul_const (xs := r) (c := (-2 * d)) (f := fun e => e))
  have hconst :
      listSumR (r.map (fun _ => d * d)) = (r.length : ℝ) * (d * d) := by
    simpa using (listSumR_map_const (xs := r) (c := d * d))
  have hcomp :
      List.map ((fun e ↦ e * e) ∘ fun e ↦ e - d) r =
        List.map (fun e ↦ (e - d) * (e - d)) r := by
    ext e
    rfl
  calc
    listSumR (List.map (fun e => e * e) (List.map (fun e => e - d) r))
        = listSumR (List.map ((fun e ↦ e * e) ∘ fun e ↦ e - d) r) := by
          simp [List.map_map]
    _ = listSumR (List.map (fun e ↦ (e - d) * (e - d)) r) := by
          simp [hcomp]
    _ = listSumR (List.map (fun e ↦ e * e + (-2 * d * e + d * d)) r) := by simp [hsq]
    _ = listSumR (List.map (fun e ↦ e * e) r) +
          listSumR (List.map (fun e ↦ -2 * d * e + d * d) r) := by
      exact hsplit1
    _ = listSumR (List.map (fun e ↦ e * e) r) +
          (listSumR (List.map (fun e ↦ -2 * d * e) r) +
            listSumR (List.map (fun _ ↦ d * d) r)) := by
      simpa [add_assoc] using
        congrArg (fun t => listSumR (List.map (fun e ↦ e * e) r) + t) hsplit2
    _ = listSumR (List.map (fun e ↦ e * e) r) +
          ((-2 * d) * listSumR r) + ((r.length : ℝ) * (d * d)) := by
      rw [hmul, hconst]
      ring_nf
    _ = listSumR (List.map (fun e ↦ e * e) r) + ((r.length : ℝ) * (d * d)) := by
      simp [hsum0]
    _ = listSumR (List.map (fun e ↦ e * e) r) + ((data.length : ℝ) * (d * d)) := by
      simp [hrlen]
    _ = listSumR (List.map (fun e ↦ e * e) r) +
          (data.length : ℝ) * ((b - bOf data m) ^ (2 : Nat)) := by
      simp [d, pow_two]


lemma ssResSpec_minimized_at_bOf
  (data : List (ℝ × ℝ)) (m b : ℝ)
  (hlen : data.length ≠ 0) :
  ssResSpec data m (bOf data m) ≤ ssResSpec data m b := by
  rw [ssResSpec_shift_intercept (data := data) (m := m) (b := b) hlen]
  have hnonneg :
      0 ≤ (data.length : ℝ) * (b - bOf data m) ^ (2 : Nat) := by
    exact mul_nonneg (Nat.cast_nonneg data.length) (by nlinarith [sq_nonneg (b - bOf data m)])
  linarith


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
theorem linearRegression_returns_slope_intercept
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  m = slopeSpec data ∧ b = interceptSpec data := by
  rcases linearRegression_some_fields
      (data := data) (m := m) (b := b) (r2 := r2) h with
    ⟨_, hm, hb, _⟩
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
  rcases linearRegression_returns_slope_intercept (data := data) (m := m) (b := b) (r2 := r2) h with
    ⟨hm, hb⟩
  simp [hm, hb]


lemma listSumR_map_nonneg {β : Type} (xs : List β) (f : β → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ listSumR (xs.map f) := by
  induction xs with
  | nil =>
      simp [listSumR]
  | cons x xs ih =>
      simp [listSumR_cons, hf x, ih, add_nonneg]

lemma vrSpecR_nonneg (data : List (ℝ × ℝ)) :
    0 ≤ vrSpecR data := by
  unfold vrSpecR
  refine listSumR_map_nonneg
    (xs := data)
    (f := fun xy => (xy.1 - xBarSpecR data) ^ (2 : Nat)) ?_
  intro xy
  simpa [pow_two] using sq_nonneg (xy.1 - xBarSpecR data)

@[simp] lemma isZero_zero_real :
    BET.isZero (α := ℝ) (0 : ℝ) = true := by
  simp [BET.isZero, HasIsZero.isZero]

lemma linearRegression_some_vr_pos
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  0 < vrSpecR data := by
  have hnonneg : 0 ≤ vrSpecR data := vrSpecR_nonneg data
  have hvr_bool : BET.isZero (vrSpecR data) = false :=
    linearRegression_some_vr_notZero (data := data) h
  have hvr_ne : vrSpecR data ≠ 0 := by
    intro hzero
    have hiz : BET.isZero (vrSpecR data) = true := by
      simpa [hzero] using (isZero_zero_real)
    rw [hiz] at hvr_bool
    cases hvr_bool
  have h0ne : (0 : ℝ) ≠ vrSpecR data := by
    intro hzero
    exact hvr_ne hzero.symm
  exact lt_of_le_of_ne hnonneg h0ne

theorem linearRegression_returns_least_minimizer
  (data : List (ℝ × ℝ)) (m b r2 : ℝ)
  (h : linearRegression (α := ℝ) data = some (m, b, r2)) :
  ∀ m' b' : ℝ,
    ssResSpec data m b ≤ ssResSpec data m' b' := by
  rcases linearRegression_some_fields
      (data := data) (m := m) (b := b) (r2 := r2) h with
    ⟨_, hm, hb, _⟩
  have hlen2 : 2 ≤ data.length :=
    linearRegression_some_length (α := ℝ) (data := data) h
  have hlen : data.length ≠ 0 := by
    have hpos : 0 < data.length := lt_of_lt_of_le (by decide : 0 < 2) hlen2
    exact Nat.ne_of_gt hpos
  have hvr : 0 < vrSpecR data :=
    linearRegression_some_vr_pos (data := data) (m := m) (b := b) (r2 := r2) h
  intro m' b'
  simpa [hm, hb] using
    (ssResSpec_minimized_at_slope_and_intercept
      (data := data) (m := m') (b := b') hlen hvr)

/-- If `fitWindow` succeeds, its embedded regression result is exactly the regression
computed on the executable linearized data. -/
theorem fitWindow_some_regression
  (window : List (Point ℝ)) (range : Nat × Nat) (fit : BETFit ℝ)
  (h : fitWindow (α := ℝ) window range = some fit) :
  linearRegression (α := ℝ) (linearizeWindow window) =
    some (fit.slope, fit.intercept, fit.rSquared) := by
  classical
  unfold fitWindow at h
  cases hreg : linearRegression (α := ℝ) (linearizeWindow window) with
  | none =>
      simp [hreg] at h
  | some triple =>
      rcases triple with ⟨slope, intercept, r2⟩
      cases hzeroNm : BET.isZero (slope + intercept) with
      | true =>
          simp [hreg] at h
          have hNmFalse : HasIsZero.isZero (slope + intercept) = false := h.1
          have hNmTrue : HasIsZero.isZero (slope + intercept) = true := by
            simpa [BET.isZero] using hzeroNm
          rw [hNmTrue] at hNmFalse
          cases hNmFalse
      | false =>
          cases hzeroInt : BET.isZero intercept with
          | true =>
              simp [hreg] at h
              have hIntFalse : HasIsZero.isZero intercept = false := h.2.1
              have hIntTrue : HasIsZero.isZero intercept = true := by
                simpa [BET.isZero] using hzeroInt
              rw [hIntTrue] at hIntFalse
              cases hIntFalse
          | false =>
              simp [hreg] at h
              rcases h with ⟨_, _, hfit⟩
              cases hfit
              rfl

/-- The least-squares minimizer theorem now connects directly to the executable
window-fitting pipeline: whenever `fitWindow` succeeds, its returned line minimizes
the residual sum of squares on the linearized window data. -/
theorem fitWindow_returns_least_minimizer
  (window : List (Point ℝ)) (range : Nat × Nat) (fit : BETFit ℝ)
  (h : fitWindow (α := ℝ) window range = some fit) :
  ∀ m b : ℝ,
    ssResSpec (linearizeWindow window) fit.slope fit.intercept ≤
      ssResSpec (linearizeWindow window) m b := by
  have hreg := fitWindow_some_regression (window := window) (range := range) (fit := fit) h
  exact linearRegression_returns_least_minimizer
    (data := linearizeWindow window)
    (m := fit.slope) (b := fit.intercept) (r2 := fit.rSquared) hreg


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
    simp [hb, hm]
  · -- C soundness
    simp [hb, hm]

end BET
