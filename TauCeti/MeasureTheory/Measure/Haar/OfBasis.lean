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
product Lebesgue measure. A general change of basis rescales its normalized Haar measure
by the inverse absolute determinant.

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

section ChangeBasis

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι]

/-- A change of basis rescales its normalized Haar measure by the inverse absolute determinant. -/
theorem addHaar_eq_smul_of_basis (b b' : Basis ι ℝ E) :
    b'.addHaar = ENNReal.ofReal |(b.det b')⁻¹| • b.addHaar := by
  let e : E ≃ₗ[ℝ] E := b.equiv b' (Equiv.refl ι)
  have hmap : b.map e = b' := by
    ext i
    simp [e]
  have hdet : e.toLinearMap.det = b.det b' := by
    simpa only [e] using det_basis b' b
  calc
    b'.addHaar = Measure.map e.toContinuousLinearEquiv b.addHaar := by
      rw [b.map_addHaar, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, hmap]
    _ = _ := by
      simpa only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.coe_coe, hdet] using
        Measure.map_linearMap_addHaar_eq_smul_addHaar b.addHaar e.isUnit_det'.ne_zero

end ChangeBasis

end Module.Basis

end
