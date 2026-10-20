/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# Units and the Jacobson radical of normed rings

In a normed ring with summable geometric series, `Ring.inverse` is continuous at every unit
(`NormedRing.inverse_continuousAt`), but it jumps to `0` at the boundary of the open set of units.
When the nonunits also form an open set, as in a complete discretely valued ring such as `ℤ_p`,
there is no such boundary and `Ring.inverse` is continuous everywhere.

The Jacobson radical is closed, as an intersection of maximal left ideals, using
Mathlib's `Ring.jacobson_eq_sInf_isMaximal` and `Ideal.IsMaximal.isClosed`.
See Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
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

namespace TauCeti.Ring

/-- The Jacobson radical of a normed ring with summable geometric series is closed. -/
theorem isClosed_jacobson (A : Type*) [NormedRing A] [HasSummableGeomSeries A] :
    IsClosed (Ring.jacobson A : Set A) := by
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.coe_sInf]
  exact isClosed_biInter fun I hI => by
    have : Ideal.IsMaximal I := hI
    exact Ideal.IsMaximal.isClosed

end TauCeti.Ring
