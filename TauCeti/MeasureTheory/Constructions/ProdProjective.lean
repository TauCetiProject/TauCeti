/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# A product law is determined by finite-dimensional marginals in its path coordinate

A finite measure on `γ × (∀ i, β i)` is determined by its images under `Prod.map id F.restrict`,
as `F` ranges over the finite sets of coordinates. The sets `s ×ˢ cylinder F S`, with `s`
measurable in `γ` and `cylinder F S` a measurable cylinder of the path space `∀ i, β i`, form a
π-system generating the product σ-algebra, and the measure of `s ×ˢ cylinder F S` is read off from
the image under `Prod.map id F.restrict`.

This is the shape in which a coding of an infinite family of random variables, jointly with a fixed
observation, is assembled from the codings of its finite subfamilies.

## Main result

* `TauCeti.MeasureTheory.Measure.ext_prod_pi_of_forall_finset_map_restrict_eq` — a finite measure
  on `γ × (∀ i, β i)` equals any measure with the same image under every `Prod.map id F.restrict`.
-/

public section

open MeasureTheory

namespace TauCeti.MeasureTheory.Measure

variable {γ ι : Type*} {β : ι → Type*} [MeasurableSpace γ] [∀ i, MeasurableSpace (β i)]

/-- **Finite-dimensional marginals in the path coordinate determine a finite product law.** A
finite measure `μ` on `γ × (∀ i, β i)` equals a measure `ν` as soon as, for every finite set `F` of
coordinates, their images under `Prod.map id F.restrict` agree. -/
theorem ext_prod_pi_of_forall_finset_map_restrict_eq {μ ν : Measure (γ × (∀ i, β i))}
    [IsFiniteMeasure μ]
    (h : ∀ F : Finset ι, μ.map (Prod.map id F.restrict) = ν.map (Prod.map id F.restrict)) :
    μ = ν := by
  have hF (F : Finset ι) : Measurable (Prod.map (id : γ → γ) (F.restrict (π := β))) :=
    measurable_id.prodMap F.measurable_restrict
  refine ext_of_generate_finite _ ?_
    (MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_measurableCylinders) ?_ ?_
  · rw [← generateFrom_prod_eq isCountablySpanning_measurableSet
      ⟨fun _ => .univ, fun _ => univ_mem_measurableCylinders β, Set.iUnion_const _⟩,
      MeasurableSpace.generateFrom_measurableSet, generateFrom_measurableCylinders]
  · rintro _ ⟨s, hs, _, hC, rfl⟩
    obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hC
    have := congr($(h F) (s ×ˢ S))
    -- `cylinder F S` is by definition the preimage `F.restrict ⁻¹' S`.
    rwa [Measure.map_apply (hF F) (hs.prod hS), Measure.map_apply (hF F) (hs.prod hS),
      Set.preimage_prod_map_prod, Set.preimage_id] at this
  · simpa [Measure.map_apply (hF ∅)] using congr($(h ∅) .univ)

end TauCeti.MeasureTheory.Measure
