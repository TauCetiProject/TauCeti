/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The Giry measurable space from joint evaluations

The measurable space on measures is induced by the map of all measurable-set evaluations.
Consequently, any measure-valued map generates the same σ-algebra as its joint evaluations,
without a measurability assumption. These identities let laws and independence of random
measures be checked through their evaluation processes.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The measurable space on measures is induced by the joint evaluation map on all
measurable sets. -/
theorem measurableSpace_eq_comap_eval :
    (Measure.instMeasurableSpace : MeasurableSpace (Measure X)) =
      MeasurableSpace.comap
        (fun (μ : Measure X) (A : {A : Set X // MeasurableSet A}) ↦ μ A.val)
        MeasurableSpace.pi := by
  let e : Measure X → ({A : Set X // MeasurableSet A} → ℝ≥0∞) := fun μ A ↦ μ A.val
  apply le_antisymm
  · have hid : Measurable[MeasurableSpace.comap e inferInstance]
        (id : Measure X → Measure X) :=
      measurable_of_measurable_coe _ fun A hA ↦
        (measurable_pi_apply (⟨A, hA⟩ : {A : Set X // MeasurableSet A})).comp
          (comap_measurable e)
    simpa only [MeasurableSpace.comap_id] using hid.comap_le
  · exact (Measurable.of_eval fun A ↦ measurable_coe A.property).comap_le

/-- A measure-valued map generates the same measurable space as its joint evaluations
on all measurable sets. No measurability assumption on the map is needed. -/
theorem measurableSpace_comap_eq_comap_eval {Ω : Type*} (N : Ω → Measure X) :
    MeasurableSpace.comap N inferInstance =
      MeasurableSpace.comap
        (fun ω (A : {A : Set X // MeasurableSet A}) ↦ N ω A.val)
        MeasurableSpace.pi := by
  rw [measurableSpace_eq_comap_eval, MeasurableSpace.comap_comp, Function.comp_def]

end MeasureTheory.Measure
