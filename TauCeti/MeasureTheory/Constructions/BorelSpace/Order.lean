/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability and measure extensionality on ordered Borel spaces

A lower semicontinuous function into a second-countable linear order is Borel measurable
(`LowerSemicontinuous.measurable`). The same holds when lower semicontinuity fails at countably
many points: each superlevel set `{f > y}` is the union of its interior, which contains every
superlevel point where `f` is lower semicontinuous, and of a countable set.

Such functions arise, for instance, as the perimeter of the superlevel sets `{u > t}` of a
function `u` as a function of the level `t`, which is lower semicontinuous at every level whose
level set is null, hence off a countable set.

## Main results

* `TauCeti.measurable_of_countable_not_lowerSemicontinuousAt`: a function that is lower
  semicontinuous at all but countably many points is measurable.
* `MeasureTheory.Measure.ext_of_Iic'`: measures finite on initial intervals are determined by
  their masses on those intervals, without a finite-total-mass assumption.
-/

public section

open Set Topology
open scoped ENNReal

namespace TauCeti

variable {α δ : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [LinearOrder α] [OrderTopology α] [SecondCountableTopology α]
  [TopologicalSpace δ] [MeasurableSpace δ] [OpensMeasurableSpace δ] [MeasurableSingletonClass δ]

/-- A function that is lower semicontinuous at all but countably many points is measurable. -/
theorem measurable_of_countable_not_lowerSemicontinuousAt {f : δ → α}
    (hf : {x | ¬LowerSemicontinuousAt f x}.Countable) : Measurable f := by
  refine measurable_of_Ioi fun y => ?_
  -- A superlevel point where `f` is lower semicontinuous is an interior point.
  have hsub : f ⁻¹' Ioi y ⊆
      interior (f ⁻¹' Ioi y) ∪ (f ⁻¹' Ioi y ∩ {x | ¬LowerSemicontinuousAt f x}) := fun x hx => by
    by_cases hlsc : LowerSemicontinuousAt f x
    · exact Or.inl (mem_interior_iff_mem_nhds.2 (hlsc y hx))
    · exact Or.inr ⟨hx, hlsc⟩
  rw [subset_antisymm hsub (union_subset interior_subset inter_subset_left)]
  exact isOpen_interior.measurableSet.union (hf.mono inter_subset_right).measurableSet

end TauCeti

namespace MeasureTheory.Measure

/-- Two measures finite on initial intervals are equal if they agree on all initial intervals.
Unlike `Measure.ext_of_Iic`, this does not require finite total mass. -/
theorem ext_of_Iic' {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α]
    (μ ν : Measure α) (hμ : ∀ a, μ (Iic a) ≠ ∞)
    (h : ∀ a, μ (Iic a) = ν (Iic a)) : μ = ν := by
  obtain ⟨s, hs, hd, -, htop⟩ := exists_countable_dense_bot_top α
  apply ext_of_generateFrom_of_cover_subset
    (S := range (Iic : α → Set α)) (T := Iic '' s)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic (α := α))) isPiSystem_Iic
  · rintro _ ⟨a, -, rfl⟩
    exact mem_range_self _
  · exact hs.image _
  · apply sUnion_eq_univ_iff.2
    intro x
    obtain ⟨a, ha, hxa⟩ := hd.exists_ge' htop x
    exact ⟨Iic a, mem_image_of_mem _ ha, hxa⟩
  · rintro _ ⟨a, -, rfl⟩
    exact hμ a
  · rintro _ ⟨a, rfl⟩
    exact h a

end MeasureTheory.Measure
