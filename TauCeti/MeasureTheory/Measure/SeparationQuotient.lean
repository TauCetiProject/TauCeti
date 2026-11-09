/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measures on the topological separation quotient

Pushforward to `SeparationQuotient` preserves the information in a Borel measure: the Borel
structure of a topological space is pulled back from that of its separation quotient.

The quotient carries its Borel measurable structure. `Measure.separationQuotient_def` exposes
its pushforward formula, `Measure.separationQuotient_apply` evaluates it on measurable sets, and
`Measure.separationQuotient_inj` simplifies equality of quotient laws.
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

/-- The separation-quotient measure of a measurable set is the measure of its preimage. -/
@[simp]
theorem separationQuotient_apply [OpensMeasurableSpace X] (μ : Measure X)
    {s : Set (SeparationQuotient X)} (hs : MeasurableSet[borel (SeparationQuotient X)] s) :
    separationQuotient μ s = μ (SeparationQuotient.mk ⁻¹' s) := by
  rw [separationQuotient_def]
  exact map_apply (measurable_iff_comap_le.2 <|
    SeparationQuotient.isInducing_mk.comap_borel.trans_le OpensMeasurableSpace.borel_le) hs

variable [BorelSpace X]

/-- Pushforward to the topological separation quotient is injective on Borel measures:
two Borel measures on a topological space agree exactly when their quotient laws agree. -/
@[simp]
theorem separationQuotient_inj {μ ν : Measure X} :
    separationQuotient μ = separationQuotient ν ↔ μ = ν := by
  refine ⟨fun h ↦ ext fun s hs ↦ ?_, congrArg _⟩
  rw [BorelSpace.measurable_eq (α := X), ← SeparationQuotient.isInducing_mk.comap_borel] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← separationQuotient_apply μ ht, ← separationQuotient_apply ν ht, h]

end MeasureTheory.Measure
