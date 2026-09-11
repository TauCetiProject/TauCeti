/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Separation.Basic

/-!
# Measures on the topological separation quotient

Pushforward to `SeparationQuotient` preserves the information in a finite Borel measure:
open sets are saturated under topological inseparability and determine finite Borel measures.

The quotient carries its Borel measurable structure. `Measure.separationQuotient_def` exposes
its pushforward formula, and `Measure.separationQuotient_inj` simplifies equality of quotient laws.
-/

public section

open Set

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

/-- Pushforward to the topological separation quotient is injective on finite Borel measures on a
topological space. Equivalently, such measures agree exactly when their quotient laws agree.

Every open set in `X` is saturated under the inseparability relation, so it is the preimage of its
open image in `SeparationQuotient X`. Equality of the pushforwards therefore gives equality on
open sets, which determine finite Borel measures. -/
@[simp]
theorem separationQuotient_inj (μ ν : Measure X) [IsFiniteMeasure μ] :
    separationQuotient μ = separationQuotient ν ↔ μ = ν := by
  let _ : MeasurableSpace (SeparationQuotient X) := borel (SeparationQuotient X)
  let _ : BorelSpace (SeparationQuotient X) := ⟨rfl⟩
  have hmk : Measurable (SeparationQuotient.mk : X → SeparationQuotient X) :=
    SeparationQuotient.continuous_mk.measurable
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [separationQuotient_def, separationQuotient_def] at h
  apply ext_of_generate_finite {s : Set X | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen
  · intro s hs
    have hqs : MeasurableSet (SeparationQuotient.mk '' s) :=
      (SeparationQuotient.isOpenMap_mk s hs).measurableSet
    have heval := congrArg (fun m : Measure (SeparationQuotient X) ↦
      m (SeparationQuotient.mk '' s)) h
    simpa only [Measure.map_apply hmk hqs, SeparationQuotient.preimage_image_mk_open hs] using heval
  · have heval := congrArg (fun m : Measure (SeparationQuotient X) ↦ m univ) h
    simpa only [Measure.map_apply_of_aemeasurable hmk.aemeasurable MeasurableSet.univ,
      preimage_univ] using heval

end MeasureTheory.Measure
