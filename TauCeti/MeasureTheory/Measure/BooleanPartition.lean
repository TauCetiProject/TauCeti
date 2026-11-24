/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Boolean partitions of measurable families

The Boolean membership vector of a measurable family is measurable. For a finite family,
each member's mass is the sum of the masses of the Boolean atoms with its bit set, without
any finiteness assumption on the measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

open Classical in
/-- The Boolean membership vector of a measurable family of sets is measurable. -/
theorem TauCeti.measurable_pi_decide_mem {X ι : Type*} [MeasurableSpace X]
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fun x i ↦ decide (x ∈ A i)) :=
  Measurable.of_eval fun i ↦ by
    simpa using (measurable_const.ite (hA i) measurable_const :
      Measurable fun x ↦ if x ∈ A i then true else false)

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

open Classical in
/-- A member of a finite measurable family has mass equal to the sum of the masses of the
atoms of its Boolean partition whose corresponding membership bit is true.
No finiteness assumption on the measure is needed. -/
theorem apply_eq_sum_mem_partition (μ : Measure X) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) (i : ι) :
    μ (A i) = ∑ b ∈ Finset.univ.filter (fun b : ι → Bool ↦ b i = true),
      μ ((fun x j ↦ decide (x ∈ A j)) ⁻¹' {b}) := by
  rw [sum_measure_preimage_singleton _
    (fun b _ ↦ TauCeti.measurable_pi_decide_mem hA (measurableSet_singleton b))]
  congr 1
  ext x
  simp

end MeasureTheory.Measure
