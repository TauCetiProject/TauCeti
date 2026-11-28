/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The Fourier transform of a finite sum

Mathlib's `VectorFourier.fourierIntegral_add` splits the transform over a sum of two integrable
functions. This file extends it to finite sums: for a continuous character `e` and a continuous
pairing `L`, the transform of `∑ i ∈ s, g i` is `∑ i ∈ s, 𝓕 (g i)` when every `g i` is integrable.

## Main results

* `VectorFourier.fourierIntegral_finsetSum`: the transform of a finite sum of integrable functions
  is the sum of their transforms.
-/

public section

open MeasureTheory

namespace VectorFourier

variable {𝕜 V W E : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  [AddCommGroup W] [Module 𝕜 W] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] {e : AddChar 𝕜 Circle} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}

/-- The Fourier transform of a finite sum of integrable functions is the sum of their
transforms. -/
theorem fourierIntegral_finsetSum (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {ι : Type*} (s : Finset ι) {g : ι → V → E}
    (hg : ∀ i ∈ s, Integrable (g i) μ) :
    fourierIntegral e μ L (∑ i ∈ s, g i) = ∑ i ∈ s, fourierIntegral e μ L (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext w; simp [fourierIntegral]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, Integrable (g j) μ := fun j hj ↦ hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fourierIntegral_add he hL
      (hg i (Finset.mem_insert_self i s)) (integrable_finsetSum' s hs), ih hs]

end VectorFourier
