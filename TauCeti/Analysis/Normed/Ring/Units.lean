/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# Continuity of the ring inverse

In a normed ring with summable geometric series, `Ring.inverse` is continuous at every unit
(`NormedRing.inverse_continuousAt`), but it jumps to `0` at the boundary of the open set of units.
When the nonunits also form an open set, as in a complete discretely valued ring such as `ℤ_p`,
there is no such boundary and `Ring.inverse` is continuous everywhere.
-/

public section

namespace NormedRing

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- If the nonunits of a normed ring with summable geometric series form an open set, then
`Ring.inverse` is continuous: it is continuous at every unit, and locally zero at every nonunit. -/
theorem continuous_inverse_of_isOpen_nonunits (h : IsOpen (nonunits R)) :
    Continuous (Ring.inverse : R → R) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact inverse_continuousAt u
  · have hx' : Ring.inverse =ᶠ[nhds x] fun _ ↦ (0 : R) :=
      Filter.mem_of_superset (h.mem_nhds hx) fun y hy ↦ Ring.inverse_non_unit y hy
    exact continuousAt_const.congr hx'.symm

end NormedRing
