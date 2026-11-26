/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.UniquelyErgodic
public import TauCeti.Dynamics.Ergodic.InvariantProbabilities.Extreme
public import Mathlib.Dynamics.Ergodic.AddCircle
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Worked examples: unique ergodicity

* The doubling map of `UnitAddCircle` preserves both `δ_0` and `volume`, so it is not uniquely
  ergodic, and by `TauCeti.uniquelyErgodic_iff_tendstoUniformly_birkhoffAverage` some continuous
  function has Birkhoff averages that do not converge uniformly to a constant. Both measures are
  ergodic, so its invariant probabilities have at least two extreme points.
* The identity of a one-point space is uniquely ergodic, so its Birkhoff averages converge
  uniformly to the integral against the Dirac mass.
-/

public section

open MeasureTheory Filter TauCeti
open scoped ENNReal

namespace TauCeti.UniquelyErgodicExamples

/-- The doubling map of the circle. -/
noncomputable def doubling (x : UnitAddCircle) : UnitAddCircle := 2 • x

theorem continuous_doubling : Continuous doubling :=
  continuous_id.nsmul 2

/-- The Dirac mass at the fixed point `0` is ergodic for the doubling map. -/
theorem ergodic_doubling_dirac : Ergodic doubling (Measure.dirac 0) :=
  ergodic_dirac_of_isFixedPt continuous_doubling.measurable (by simp [Function.IsFixedPt, doubling])

/-- `volume` is ergodic for the doubling map; `doubling` is by definition `fun x ↦ 2 • x`, the map
of Mathlib's `AddCircle.ergodic_nsmul`. -/
theorem ergodic_doubling_volume : Ergodic doubling volume :=
  AddCircle.ergodic_nsmul (T := 1) one_lt_two

/-- The probability measures `δ_0` and `volume` on `UnitAddCircle` are distinct. -/
theorem dirac_zero_ne_volume :
    (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure UnitAddCircle) ≠
      ⟨volume, inferInstance⟩ := by
  intro h
  have := congrArg (fun μ : ProbabilityMeasure UnitAddCircle ↦ (μ : Measure UnitAddCircle) {0}) h
  simp at this

/-- The doubling map is not uniquely ergodic: `δ_0` and `volume` are both invariant. -/
theorem not_uniquelyErgodic_doubling : ¬ UniquelyErgodic doubling := fun h ↦
  dirac_zero_ne_volume (h.eq_of_mem
    (mem_invariantProbabilities.mpr ergodic_doubling_dirac.toMeasurePreserving)
    (mem_invariantProbabilities.mpr ergodic_doubling_volume.toMeasurePreserving))

/-- Consequently some continuous function has Birkhoff averages under the doubling map that do
not converge uniformly to a constant. -/
example : ∃ f : C(UnitAddCircle, ℝ), ∀ c : ℝ,
    ¬ TendstoUniformly (fun n ↦ birkhoffAverage ℝ doubling f n) (fun _ ↦ c) atTop := by
  by_contra! h
  exact not_uniquelyErgodic_doubling
    ((uniquelyErgodic_iff_tendstoUniformly_birkhoffAverage continuous_doubling).mpr h)

/-- **Check.** `δ_0` and `volume` are two distinct extreme points of the invariant probabilities of
the doubling map: both are ergodic. -/
example : ∃ μ ν : ProbabilityMeasure UnitAddCircle, μ ≠ ν ∧
    (μ : Measure UnitAddCircle) ∈ Set.extremePoints ℝ≥0∞
      (((↑) : ProbabilityMeasure UnitAddCircle → Measure UnitAddCircle) ''
        invariantProbabilities doubling) ∧
    (ν : Measure UnitAddCircle) ∈ Set.extremePoints ℝ≥0∞
      (((↑) : ProbabilityMeasure UnitAddCircle → Measure UnitAddCircle) ''
        invariantProbabilities doubling) :=
  ⟨_, _, dirac_zero_ne_volume,
    ergodic_iff_mem_extremePoints_invariantProbabilities.1 ergodic_doubling_dirac,
    ergodic_iff_mem_extremePoints_invariantProbabilities.1 ergodic_doubling_volume⟩

/-- The identity of a one-point space is uniquely ergodic. -/
theorem uniquelyErgodic_id_unit : UniquelyErgodic (id : Unit → Unit) := by
  refine UniquelyErgodic.of_mem (ν := ⟨Measure.dirac (), inferInstance⟩)
    (mem_invariantProbabilities.mpr (MeasurePreserving.id _)) fun μ _ ↦ ?_
  refine ProbabilityMeasure.toMeasure_injective (Measure.ext_iff_singleton.mpr fun u ↦ ?_)
  have : ({u} : Set Unit) = Set.univ := Set.eq_univ_of_forall fun _ ↦ rfl
  simp [this]

/-- Hence its Birkhoff averages converge uniformly to the value at the point. -/
example (f : C(Unit, ℝ)) :
    TendstoUniformly (fun n ↦ birkhoffAverage ℝ id f n) (fun _ ↦ f ()) atTop := by
  have h := uniquelyErgodic_id_unit.tendstoUniformly_birkhoffAverage continuous_id
    (μ := ⟨Measure.dirac (), inferInstance⟩)
    (mem_invariantProbabilities.mpr (MeasurePreserving.id _)) f
  simpa using h

end TauCeti.UniquelyErgodicExamples
