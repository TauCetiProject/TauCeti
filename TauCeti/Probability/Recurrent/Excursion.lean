/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Excursion.Reconstruction
public import TauCeti.Probability.Recurrent.Basic

/-!
# Excursion reconstruction for recurrent processes

A recurrent process started at `a₀` returns to that state infinitely often almost surely.
Its path law is therefore the image of its excursion law under concatenation. This
specializes the general reconstruction theorem without imposing any distributional symmetry.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **The path law of a recurrent process started at `a₀` is the image of its excursion law.**
Only the base state's singleton needs to be measurable. -/
theorem Recurrent.pathLaw_eq_map_pathOfExcursions
    (hrec : Recurrent μ X) (hX : ∀ i, AEMeasurable (X i) μ)
    (ha₀ : MeasurableSet ({a₀} : Set α)) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    pathLaw μ X = (pathLaw μ (excursionProcess X a₀)).map (pathOfExcursions a₀) := by
  apply TauCeti.Probability.pathLaw_eq_map_pathOfExcursions hX ha₀ _ h0
  filter_upwards [h0, hrec.ae_infinite_setOf_eq] with ω hω0 hωinf
  have h := hωinf 0
  rwa [hω0] at h

end Probability

end TauCeti

end

end
