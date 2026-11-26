/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.RotationUniquelyErgodic
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Worked examples: rotations of the circle

* An irrational rotation of `UnitAddCircle` is uniquely ergodic, and `volume` is its only
  invariant probability.
* The rotation by `1/3` is not uniquely ergodic: the uniform probability on the orbit
  `{0, 1/3, 2/3}` is invariant, as is `volume`.
-/

public section

open MeasureTheory TauCeti

namespace TauCeti.RotationUniquelyErgodicExamples

/-- An irrational rotation of the circle is uniquely ergodic. -/
theorem uniquelyErgodic_irrational {a : ℝ} (ha : Irrational a) :
    UniquelyErgodic ((a : UnitAddCircle) + · : UnitAddCircle → UnitAddCircle) :=
  uniquelyErgodic_add_left_of_denseRange_zsmul <|
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using ha)

/-- For an irrational rotation, every invariant probability is `volume`. -/
example {a : ℝ} (ha : Irrational a) (ν : ProbabilityMeasure UnitAddCircle)
    (hν : ν ∈ invariantProbabilities ((a : UnitAddCircle) + · : UnitAddCircle → UnitAddCircle)) :
    (ν : Measure UnitAddCircle) = volume :=
  congrArg ProbabilityMeasure.toMeasure ((uniquelyErgodic_irrational ha).eq_of_mem hν
    (ν := ⟨volume, inferInstance⟩) (mem_invariantProbabilities.mpr
      (measurePreserving_add_left (volume : Measure UnitAddCircle) (a : UnitAddCircle))))

/-- The point `1/3` of the circle. -/
noncomputable def third : UnitAddCircle := ((1 / 3 : ℝ) : UnitAddCircle)

/-- The uniform probability on the orbit `{0, 1/3, 2/3}` of the rotation by `1/3`. -/
noncomputable def orbitThird : Measure UnitAddCircle :=
  (3 : ENNReal)⁻¹ • (Measure.dirac 0 + Measure.dirac third + Measure.dirac (third + third))

instance instIsProbabilityMeasureOrbitThird : IsProbabilityMeasure orbitThird :=
  ⟨by
    simp only [orbitThird, smul_apply, add_apply, measure_univ, smul_eq_mul]
    norm_num [ENNReal.inv_mul_cancel]⟩

/-- The rotation by `1/3` preserves the orbit probability. -/
theorem measurePreserving_orbitThird :
    MeasurePreserving (third + · : UnitAddCircle → UnitAddCircle) orbitThird orbitThird := by
  have hm : Measurable (third + · : UnitAddCircle → UnitAddCircle) :=
    (continuous_const_add _).measurable
  refine ⟨hm, ?_⟩
  have h3 : third + (third + third) = 0 := by
    simp only [third, ← AddCircle.coe_add]
    norm_num
  simp only [orbitThird, Measure.map_smul _ hm.aemeasurable, Measure.map_add _ _ hm,
    Measure.map_dirac' hm, add_zero, h3]
  ac_rfl

/-- The rotation by `1/3` is not uniquely ergodic. -/
example : ¬ UniquelyErgodic (third + · : UnitAddCircle → UnitAddCircle) := by
  intro h
  have := congrArg (fun ν : ProbabilityMeasure UnitAddCircle ↦ (ν : Measure UnitAddCircle) {0})
    (h.eq_of_mem (μ := ⟨orbitThird, inferInstance⟩)
      (mem_invariantProbabilities.mpr measurePreserving_orbitThird)
      (ν := ⟨volume, inferInstance⟩) (mem_invariantProbabilities.mpr
        (measurePreserving_add_left (volume : Measure UnitAddCircle) third)))
  simp [orbitThird] at this

end TauCeti.RotationUniquelyErgodicExamples
