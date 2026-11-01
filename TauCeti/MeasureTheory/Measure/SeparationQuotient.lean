/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measures on the topological separation quotient

Pushforward to `SeparationQuotient` preserves the information in a Borel measure: the Borel
structure of a topological space is pulled back from that of its separation quotient.

The quotient carries its Borel measurable structure. `Measure.separationQuotient_def` exposes
its pushforward formula, and `Measure.separationQuotient_inj` simplifies equality of quotient laws.
-/

public section

universe u

namespace MeasureTheory.Measure

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X]

/-- The pushforward of a measure to the topological separation quotient, carrying the quotient's
Borel measurable structure. -/
noncomputable def separationQuotient (μ : Measure X) :
    @Measure (SeparationQuotient X) (borel (SeparationQuotient X)) :=
  @Measure.map X (SeparationQuotient X) _ (borel (SeparationQuotient X))
    SeparationQuotient.mk μ

/-- The separation-quotient measure is the pushforward along the quotient map. -/
theorem separationQuotient_def (μ : Measure X) :
    separationQuotient μ =
      @Measure.map X (SeparationQuotient X) _ (borel (SeparationQuotient X))
        SeparationQuotient.mk μ := by rfl

variable [BorelSpace X]

/-- Pushforward to the topological separation quotient is injective on Borel measures:
two Borel measures on a topological space agree exactly when their quotient laws agree. -/
@[simp]
theorem separationQuotient_inj {μ ν : Measure X} :
    separationQuotient μ = separationQuotient ν ↔ μ = ν := by
  have hcomap : ‹MeasurableSpace X› =
      (borel (SeparationQuotient X)).comap SeparationQuotient.mk := by
    rw [← borel_comap, ← SeparationQuotient.isInducing_mk.eq_induced]
    exact BorelSpace.measurable_eq
  refine ⟨fun h ↦ ext fun s hs ↦ ?_, congrArg _⟩
  rw [hcomap] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hmk := measurable_iff_comap_le.2 hcomap.ge
  simpa [separationQuotient_def, map_apply hmk ht] using congr($h t)

end MeasureTheory.Measure
