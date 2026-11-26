/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Splitting a cylinder into the cylinders of patterns

On a product `∀ i, α i` of finite spaces with measurable singletons, a cylinder `cylinder s t`
over a finite window `s` is, for every finite window `E ⊇ s`, the disjoint union of the cylinders
`cylinder E {p}` of the patterns `p` on `E` whose restriction to `s` lies in `t`. So its measure
is the sum of the measures of these pattern cylinders, by Mathlib's
`MeasureTheory.sum_measure_preimage_singleton` for the restriction to `E`.

## Main result

* `TauCeti.MeasureTheory.measure_cylinder_eq_sum_measure_cylinder_singleton`
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- For finite windows `s ⊆ E`, the measure of the cylinder `cylinder s t` is the sum of the
measures of the cylinders `cylinder E {p}` of the patterns `p` on `E` whose restriction to `s`
lies in `t`. -/
theorem measure_cylinder_eq_sum_measure_cylinder_singleton [DecidableEq ι]
    [∀ i, Fintype (α i)] [∀ i, MeasurableSingletonClass (α i)] {μ : Measure (∀ i, α i)}
    {s E : Finset ι} (hsE : s ⊆ E) (t : Set (∀ i : s, α i)) [DecidablePred (· ∈ t)] :
    μ (cylinder s t) =
      ∑ p : (∀ i : E, α i) with Finset.restrict₂ hsE p ∈ t, μ (cylinder E {p}) := by
  refine (congrArg μ ?_).trans (sum_measure_preimage_singleton (f := E.restrict) _
    fun p _ => MeasurableSet.cylinder E (measurableSet_singleton p)).symm
  ext η
  simp [mem_cylinder, ← Finset.restrict₂_comp_restrict hsE]

end MeasureTheory

end TauCeti
