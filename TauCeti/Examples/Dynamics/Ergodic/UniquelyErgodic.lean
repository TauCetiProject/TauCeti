/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.UniquelyErgodic
public import Mathlib.Dynamics.Ergodic.AddCircle
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Worked examples: unique ergodicity

* The doubling map of `UnitAddCircle` preserves both `δ_0` and `volume`, so it is not uniquely
  ergodic, and by `TauCeti.uniquelyErgodic_iff_tendstoUniformly_birkhoffAverage` some continuous
  function has Birkhoff averages that do not converge uniformly to a constant.
* The identity of a one-point space is uniquely ergodic, so its Birkhoff averages converge
  uniformly to the integral against the Dirac mass.
-/

public section

open MeasureTheory Filter TauCeti

namespace TauCeti.UniquelyErgodicExamples

/-- The doubling map of the circle. -/
noncomputable def doubling (x : UnitAddCircle) : UnitAddCircle := 2 • x

theorem continuous_doubling : Continuous doubling :=
  continuous_id.nsmul 2

/-- The doubling map is not uniquely ergodic: `δ_0` and `volume` are both invariant. -/
theorem not_uniquelyErgodic_doubling : ¬ UniquelyErgodic doubling := by
  intro h
  have hm : Measurable doubling := continuous_doubling.measurable
  have h₀ : (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure UnitAddCircle) ∈
      invariantProbabilities doubling := by
    refine mem_invariantProbabilities.mpr ⟨hm, ?_⟩
    rw [ProbabilityMeasure.coe_mk, Measure.map_dirac' hm]
    simp [doubling]
  have hvol : (⟨volume, inferInstance⟩ : ProbabilityMeasure UnitAddCircle) ∈
      invariantProbabilities doubling :=
    mem_invariantProbabilities.mpr (AddCircle.ergodic_nsmul (T := 1) one_lt_two).toMeasurePreserving
  have := congrArg (fun μ : ProbabilityMeasure UnitAddCircle ↦ (μ : Measure UnitAddCircle) {0})
    (h.eq_of_mem h₀ hvol)
  simp at this

/-- Consequently some continuous function has Birkhoff averages under the doubling map that do
not converge uniformly to a constant. -/
example : ∃ f : C(UnitAddCircle, ℝ), ∀ c : ℝ,
    ¬ TendstoUniformly (fun n ↦ birkhoffAverage ℝ doubling f n) (fun _ ↦ c) atTop := by
  by_contra! h
  exact not_uniquelyErgodic_doubling
    ((uniquelyErgodic_iff_tendstoUniformly_birkhoffAverage continuous_doubling).mpr h)

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
