/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# Approximation of product-space events by measurable cylinders

Under a finite measure on a product space `∀ i, α i`, every measurable event is approximated in
measure by a measurable cylinder over finitely many coordinates. This is Mathlib's density theorem
for a generating set ring, `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`, applied to the
ring of measurable cylinders, which generates the product σ-algebra.

## Main result

* `TauCeti.MeasureTheory.exists_cylinder_measure_symmDiff_lt`
-/

public section

open MeasureTheory Set

open scoped ENNReal symmDiff

namespace TauCeti

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- Every measurable event of a product space is approximated, in measure under a finite measure,
by a measurable cylinder over a finite set of coordinates. -/
theorem exists_cylinder_measure_symmDiff_lt {ρ : Measure (∀ i, α i)} [IsFiniteMeasure ρ]
    {s : Set (∀ i, α i)} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset ι) (S : Set (∀ i : F, α i)),
      MeasurableSet S ∧ ρ (symmDiff (cylinder F S) s) < ε := by
  have hcov : ∃ D : Set (Set (∀ i, α i)), D.Countable ∧
      D ⊆ measurableCylinders α ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · rintro u (rfl : u = Set.univ)
      exact univ_mem_measurableCylinders α
    · simp
  obtain ⟨t, ht_mem, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ρ)
    isSetRing_measurableCylinders hcov generateFrom_measurableCylinders.symm hs hε
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht_mem
  exact ⟨F, S, hS, ht⟩

end MeasureTheory

end TauCeti
