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


/-- Specification for a window triple produced from `iso`.

It says: the window is exactly `drop start` then `take (stop-start+1)`,
and indices are in range, and the window has at least 2 points. -/
def WindowSpec {α} (iso : Isotherm α)
    (start stop : Nat) (window : List (Point α)) : Prop :=
  start < iso.length ∧
  stop < iso.length ∧
  start < stop ∧
  window = ((iso.drop start) |> List.take (stop - start + 1))


/-- A helper: length of the `drop/take` window is exactly `stop-start+1`
provided `stop < length iso` and `start ≤ stop`. -/
lemma length_drop_take_eq {α} (iso : Isotherm α) (start stop : Nat)
    (hstart : start < iso.length)
    (hstop  : stop < iso.length)
    (hle    : start ≤ stop) :
    (iso.drop start |>.take (stop - start + 1)).length = (stop - start + 1) := by
  have hlenDrop : stop - start + 1 ≤ (iso.drop start).length := by
    -- `(iso.drop start).length = iso.length - start`
    simp [List.length_drop]
    have : stop - start + 1 ≤ iso.length - start := by
      have h1 : stop + 1 ≤ iso.length := Nat.succ_le_of_lt hstop
      omega
    simpa [List.length_drop] using this
  exact List.length_take_of_le hlenDrop

/-- Any triple appearing in `allWindows iso` has `start < stop`. -/
lemma mem_allWindows_start_lt_stop {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    start < stop := by
  classical
  unfold allWindows at hmem
  by_cases hn : iso.length < 2
  · -- then allWindows = []
    simp [hn] at hmem
  · -- main case
    have hn' : ¬ iso.length < 2 := hn
    simp [hn'] at hmem
    rcases hmem with ⟨start', hstartMem, htriple⟩
    rcases htriple with ⟨stop', hstopMem, rfl⟩
    omega


/-- Soundness: every triple produced by `allWindows` satisfies `WindowSpec`. -/
theorem allWindows_sound {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    WindowSpec iso start stop window := by
  classical
  by_cases hlen : iso.length < 2
  · simp [allWindows, hlen] at hmem
  · have hspec :
        2 ≤ iso.length ∧
        start < iso.length ∧
        ∃ x < iso.length - (start + 1),
          x + (start + 1) = stop ∧
          List.take (x + (start + 1) - start + 1) (List.drop start iso) = window := by
      have h2 : 2 ≤ iso.length := Nat.not_lt.mp hlen
      exact ⟨h2, by simpa [allWindows, hlen] using hmem⟩
    rcases hspec with ⟨h2, hstartLt, x, hxLt, hstopEq, htakeDropEq⟩
    -- 1) start < iso.length
    have hstart : start < iso.length := hstartLt

    -- 2) stop < iso.length
    have hstop : stop < iso.length := by
      -- rewrite stop as x + (start+1)
      have hle : start + 1 ≤ iso.length := Nat.succ_le_of_lt hstart
      -- from hxLt : x < iso.length - (start+1)
      have h' : x + (start + 1) < (iso.length - (start + 1)) + (start + 1) :=
        Nat.add_lt_add_right hxLt (start + 1)
      -- RHS simplifies to iso.length
      have : x + (start + 1) < iso.length := by
        simpa [Nat.sub_add_cancel hle] using h'
      simpa [hstopEq] using this

    -- 3) start < stop
    have hstartStop : start < stop := by
      -- start < start+1 ≤ x+(start+1) = stop
      have hs : start < start + 1 := Nat.lt_succ_self start
      have hle : start + 1 ≤ x + (start + 1) := Nat.le_add_left (start + 1) x
      have : start < x + (start + 1) := lt_of_lt_of_le hs hle
      simpa [hstopEq] using this

    -- 4) window equation: window = drop/take ...
    have hwin :
        window = (iso.drop start |>.take (stop - start + 1)) := by
      have : List.take (stop - start + 1) (List.drop start iso) = window := by

        simpa [hstopEq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htakeDropEq

      simpa [List.take, List.drop] using this.symm
    refine ⟨hstart, hstop, hstartStop, ?_⟩
    simp [hwin]


--###------------------------------------------------#############
--###    Additional lemmas about allWindows               ###--
lemma allWindows_eq_nil_of_length_lt_two {α} (iso : Isotherm α)
    (hlen : iso.length < 2) :
    allWindows iso = [] := by
  simp [allWindows, hlen]


theorem mem_allWindows_start_lt_length {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    start < iso.length := by
  have hspec := allWindows_sound (iso := iso) (start := start) (stop := stop) (window := window) hmem
  exact hspec.1

theorem mem_allWindows_stop_lt_length {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    stop < iso.length := by
  have hspec := allWindows_sound (iso := iso) (start := start) (stop := stop) (window := window) hmem
  exact hspec.2.1

theorem mem_allWindows_window_eq {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    window = (iso.drop start |>.take (stop - start + 1)) := by
  have hspec := allWindows_sound (iso := iso) (start := start) (stop := stop) (window := window) hmem
  exact hspec.2.2.2

/-- Helper: length of `drop/take` window is exactly `stop-start+1`
assuming `stop < iso.length` and `start ≤ stop`. -/
lemma length_drop_take_eqq {α} (iso : Isotherm α) (start stop : Nat)
    (hstop : stop < iso.length)
    (hle  : start ≤ stop) :
    (iso.drop start |>.take (stop - start + 1)).length = (stop - start + 1) := by
  have htake : stop - start + 1 ≤ (iso.drop start).length := by
    -- (iso.drop start).length = iso.length - start
    simp [List.length_drop]
    have h1 : stop + 1 ≤ iso.length := Nat.succ_le_of_lt hstop
    -- convert to: stop - start + 1 ≤ iso.length - start
    omega
  exact List.length_take_of_le htake


theorem mem_allWindows_length {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    window.length = stop - start + 1 := by
  have hwin := mem_allWindows_window_eq (iso := iso) (start := start) (stop := stop) (window := window) hmem
  have hstop := mem_allWindows_stop_lt_length (iso := iso) (start := start) (stop := stop) (window := window) hmem
  have hlt := mem_allWindows_start_lt_stop (iso := iso) (start := start) (stop := stop) (window := window) hmem
  have hle : start ≤ stop := Nat.le_of_lt hlt
  -- rewrite by the window equation, then compute length of drop/take
  simpa [hwin] using length_drop_take_eqq (iso := iso) (start := start) (stop := stop) hstop hle


theorem mem_allWindows_length_ge2 {α} (iso : Isotherm α)
    {start stop : Nat} {window : List (Point α)}
    (hmem : (start, stop, window) ∈ allWindows iso) :
    2 ≤ window.length := by
  have hlen := mem_allWindows_length (iso := iso) (start := start) (stop := stop) (window := window) hmem
  have hlt  := mem_allWindows_start_lt_stop (iso := iso) (start := start) (stop := stop) (window := window) hmem
  -- show 2 ≤ stop - start + 1
  have : 2 ≤ stop - start + 1 := by
    omega
  simpa [hlen] using this

/--
Completeness of window enumeration:
if `start < stop < iso.length`, then the corresponding window
`iso.drop start |>.take (stop - start + 1)` appears in `allWindows iso`.
-/

theorem allWindows_complete {α} (iso : Isotherm α)
    (start stop : Nat)
    (hstartStop : start < stop)
    (hstop : stop < iso.length) :
    (start, stop, iso.drop start |>.take (stop - start + 1)) ∈ allWindows iso := by
  classical
  unfold allWindows
  have hnot : ¬ iso.length < 2 := by omega
  simp [hnot]
  refine And.intro ?_ ?_
  · exact lt_trans hstartStop hstop
  · let x : Nat := stop - (start + 1)

    have hle : start + 1 ≤ stop := Nat.succ_le_of_lt hstartStop
    have hxRange : x < iso.length - (start + 1) := by omega
    have hxEq : x + (start + 1) = stop := by simpa [x] using (Nat.sub_add_cancel hle)
    refine ⟨x, hxRange, hxEq, ?_⟩
    simp [x, hxEq]

/--
Uniqueness: for fixed indices `(start, stop)`, `allWindows` cannot produce two different windows.
This is a clean “no-duplication for fixed indices” property that follows from soundness.
-/
theorem allWindows_unique_window {α} (iso : Isotherm α)
    {start stop : Nat} {w₁ w₂ : List (Point α)}
    (h₁ : (start, stop, w₁) ∈ allWindows iso)
    (h₂ : (start, stop, w₂) ∈ allWindows iso) :
    w₁ = w₂ := by
  have hw₁ : w₁ = (iso.drop start |>.take (stop - start + 1)) :=
    mem_allWindows_window_eq (iso := iso) (hmem := h₁)
  have hw₂ : w₂ = (iso.drop start |>.take (stop - start + 1)) :=
    mem_allWindows_window_eq (iso := iso) (hmem := h₂)
  -- both are equal to the same slice
  simpa [hw₁] using hw₂.symm


end BET
