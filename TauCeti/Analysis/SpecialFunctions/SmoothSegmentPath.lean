/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The smooth path along a segment

For points `x` and `y` of a real normed space, `TauCeti.smoothSegmentPath x y` is the path
`s ↦ x + ψ(s) (y - x)`, where `ψ` is `Real.smoothTransition`. It is smooth, stays on the segment
from `x` to `y`, equals `x` for `s ≤ 0` and equals `y` for `s ≥ 1`. So it connects two points by
a smooth path which is constant near both ends, as needed for paths parametrized by all of `ℝ`
with prescribed limits at `±∞`.

## Main declarations

* `TauCeti.smoothSegmentPath`: the path `s ↦ x + ψ(s) (y - x)`.
* `TauCeti.contDiff_smoothSegmentPath`: it is smooth.
* `TauCeti.smoothSegmentPath_mem_segment`: it stays on the segment from `x` to `y`.
* `TauCeti.smoothSegmentPath_self`: constant path when the endpoints coincide.
* `TauCeti.smoothSegmentPath_of_nonpos` and `TauCeti.smoothSegmentPath_of_one_le`: it equals `x`
  for `s ≤ 0` and `y` for `s ≥ 1`.
* `TauCeti.eventuallyEq_smoothSegmentPath_atBot` and
  `TauCeti.eventuallyEq_smoothSegmentPath_atTop`: it is eventually constant at `±∞`.
* `AffineMap.map_smoothSegmentPath`: affine maps transport `TauCeti.smoothSegmentPath`.
-/

public section

noncomputable section

open Filter Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E)

/-- The smooth path `s ↦ x + ψ(s) (y - x)` from `x` to `y` along the segment, where `ψ` is
`Real.smoothTransition`. It equals `x` for `s ≤ 0` and `y` for `s ≥ 1`. -/
def smoothSegmentPath (s : ℝ) : E :=
  x + Real.smoothTransition s • (y - x)

/-- The defining formula of the smooth path along a segment. -/
theorem smoothSegmentPath_def (s : ℝ) :
    smoothSegmentPath x y s = x + Real.smoothTransition s • (y - x) :=
  (rfl)

/-- The smooth path from a point to itself is constant. -/
@[simp]
theorem smoothSegmentPath_self (s : ℝ) : smoothSegmentPath x x s = x := by
  simp [smoothSegmentPath_def]

/-- The smooth path along a segment is smooth. -/
theorem contDiff_smoothSegmentPath {n : ℕ∞} : ContDiff ℝ n (smoothSegmentPath x y) :=
  contDiff_const.add (Real.smoothTransition.contDiff.smul contDiff_const)

/-- The smooth path along a segment stays on the segment. -/
theorem smoothSegmentPath_mem_segment (s : ℝ) : smoothSegmentPath x y s ∈ segment ℝ x y := by
  rw [segment_eq_image']
  exact ⟨_, ⟨Real.smoothTransition.nonneg s, Real.smoothTransition.le_one s⟩, rfl⟩

/-- The smooth path along a segment equals its starting point for `s ≤ 0`. -/
theorem smoothSegmentPath_of_nonpos {s : ℝ} (hs : s ≤ 0) : smoothSegmentPath x y s = x := by
  simp [smoothSegmentPath_def, Real.smoothTransition.zero_of_nonpos hs]

/-- The smooth path along a segment equals its end point for `s ≥ 1`. -/
theorem smoothSegmentPath_of_one_le {s : ℝ} (hs : 1 ≤ s) : smoothSegmentPath x y s = y := by
  simp [smoothSegmentPath_def, Real.smoothTransition.one_of_one_le hs]

/-- The smooth path along a segment is eventually its starting point at `-∞`. -/
theorem eventuallyEq_smoothSegmentPath_atBot : smoothSegmentPath x y =ᶠ[atBot] fun _ ↦ x :=
  eventually_le_atBot 0 |>.mono fun _ hs ↦ smoothSegmentPath_of_nonpos x y hs

/-- The smooth path along a segment is eventually its end point at `+∞`. -/
theorem eventuallyEq_smoothSegmentPath_atTop : smoothSegmentPath x y =ᶠ[atTop] fun _ ↦ y :=
  eventually_ge_atTop 1 |>.mono fun _ hs ↦ smoothSegmentPath_of_one_le x y hs

end TauCeti

/-- An affine map transports `TauCeti.smoothSegmentPath` to the smooth segment path between the
images of its endpoints. -/
theorem AffineMap.map_smoothSegmentPath {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ᵃ[ℝ] F) (x y : E) (s : ℝ) :
    f (TauCeti.smoothSegmentPath x y s) = TauCeti.smoothSegmentPath (f x) (f y) s := by
  simpa only [TauCeti.smoothSegmentPath_def, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    add_comm _ x, add_comm _ (f x)] using f.apply_lineMap x y (Real.smoothTransition s)
