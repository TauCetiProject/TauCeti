/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The additive Haar measure of the standard basis

The additive Haar measure attached to a basis gives measure one to the parallelepiped the basis
spans. For the standard basis of `ι → ℝ` that parallelepiped is the unit cube, so the measure is
product Lebesgue measure.

## Main results

* `Module.Basis.addHaar_basisFun` — the additive Haar measure of `Pi.basisFun ℝ ι` is `volume`.
-/

public section

open MeasureTheory

namespace Module.Basis

/-- The additive Haar measure attached to the standard basis of `ι → ℝ` is product Lebesgue
measure, because the basis parallelepiped is the unit cube. -/
theorem addHaar_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).addHaar = (volume : Measure (ι → ℝ)) := by
  rw [addHaar_def, parallelepiped_basisFun, addHaarMeasure_eq_volume_pi]

end Module.Basis

end
