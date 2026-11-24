/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

import Mathlib.Order.Cofinal

/-!
# Measurability and measure extensionality on ordered Borel spaces

Let `α` be a second-countable linear order with its order topology and Borel σ-algebra. A lower
semicontinuous function `f : δ → α` on a topological space `δ` whose open sets are measurable is
measurable (`LowerSemicontinuous.measurable`). If moreover the singletons of `δ` are measurable,
the same holds when lower semicontinuity fails at countably many points: the restriction of `f`
to the complement of these points is lower semicontinuous, hence measurable, and with measurable
singletons a function measurable off a countable set is measurable
(`measurable_of_measurable_on_compl_countable`).

Such functions arise, for instance, as the perimeter of the superlevel sets `{u > t}` of a
function `u` as a function of the level `t`, which is lower semicontinuous at every level whose
level set is null, hence off a countable set.

## Main results

* `TauCeti.measurable_of_countable_not_lowerSemicontinuousAt`: a function, on a space whose open
  sets and singletons are measurable, that is lower semicontinuous at all but countably many
  points is measurable.
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

/-- Let `δ` be a topological space whose open sets and singletons are measurable, and `α` a
second-countable linear order with its order topology and Borel σ-algebra. A function `f : δ → α`
that is lower semicontinuous at all but countably many points is measurable. -/
theorem measurable_of_countable_not_lowerSemicontinuousAt {f : δ → α}
    (hf : {x | ¬LowerSemicontinuousAt f x}.Countable) : Measurable f := by
  -- Off the countable exceptional set, `f` is lower semicontinuous, hence measurable.
  refine measurable_of_measurable_on_compl_countable _ hf
    (lowerSemicontinuous_restrict_iff.2 fun x hx => ?_).measurable
  exact (not_not.1 hx).lowerSemicontinuousWithinAt _

end TauCeti

namespace MeasureTheory.Measure

/-- Two measures finite on initial intervals are equal if they agree on all initial intervals.
Unlike `Measure.ext_of_Iic`, this does not require finite total mass. -/
theorem ext_of_Iic' {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α]
    (μ ν : Measure α) (hμ : ∀ a, μ (Iic a) ≠ ∞)
    (h : ∀ a, μ (Iic a) = ν (Iic a)) : μ = ν := by
  -- This follows Mathlib's `Measure.ext_of_Ico'`: the intervals `Iic a` with `a` in a countable
  -- dense set `s` form a countable cover of `α` by sets of finite mass, so
  -- `Measure.ext_of_generateFrom_of_cover_subset` applies.
  obtain ⟨s, hs, hd, -, htop⟩ := exists_countable_dense_bot_top α
  -- `IsCofinal s` unfolds to `∀ x, ∃ y ∈ s, x ≤ y`, which `Dense.exists_ge'` provides.
  have hcof : IsCofinal s := fun x => hd.exists_ge' htop x
  exact ext_of_generateFrom_of_cover_subset (T := Iic '' s)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic α)) isPiSystem_Iic
    (image_subset_range _ _) (hs.image _)
    ((sUnion_image _ _).trans (isCofinal_iff_iUnion_Iic_eq_univ.1 hcof))
    (forall_mem_image.2 fun a _ => hμ a) (forall_mem_range.2 h)

end MeasureTheory.Measure
