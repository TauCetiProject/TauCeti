/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The `Lᵖ` seminorm of a deviation from a level

The deviation `f - m` of a real function from a level `m` is the difference of its parts
`(f - m)⁺` above and `(m - f)⁺` below the level. For `q ≥ 1` the triangle inequality bounds its
`L^q` seminorm by the sum of theirs. Level-set arguments estimate the two parts separately, for
instance around a median `m`, where each of them vanishes on a set of at least half the measure.

## Main declarations

* `TauCeti.eLpNorm_sub_const_le_add`: `‖f - m‖_q ≤ ‖(f - m)⁺‖_q + ‖(m - f)⁺‖_q` for `q ≥ 1`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

/-- The deviation of `f` from a level `m` is the difference of `(f - m)⁺` and `(m - f)⁺`, so its
`L^q` seminorm is at most the sum of theirs for `q ≥ 1`. -/
theorem eLpNorm_sub_const_le_add {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (m : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun x => f x - m) q ν ≤
      eLpNorm (fun x => max (f x - m) 0) q ν + eLpNorm (fun x => max (m - f x) 0) q ν := by
  have heq : (fun x => f x - m) =
      (fun x => max (f x - m) 0) - fun x => max (m - f x) 0 := by
    funext x
    simp only [Pi.sub_apply]
    rcases le_total (f x) m with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), sub_zero]
  rw [heq]
  exact eLpNorm_sub_le hq

end TauCeti
