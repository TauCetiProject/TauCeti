/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of functions that are lower semicontinuous off a countable set

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
-/

public section

open Set Topology

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
