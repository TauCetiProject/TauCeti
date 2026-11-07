/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.EqualDimension
public import TauCeti.Analysis.Calculus.Sard.LowDimension

/-!
# Sard's theorem for a source of dimension at most that of the target

A map whose derivative vanishes along a set `s` sends `s` to an additive-Haar-null set whenever the
source has dimension at most that of the target. Below the dimension of the target the whole image
is null (`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`); at equal dimension every
point of `s` is critical, so the equal-dimension Sard lemma
(`TauCeti.addHaar_image_eq_zero_of_not_surjective_fderivWithin`) applies.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_finrank_le_finrank`: the combined statement.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set ContinuousLinearMap

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F] (ν : Measure F) [IsAddHaarMeasure ν]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → F} {s : Set E}

/-- A map whose derivative vanishes along `s` sends `s` to a null set when the source has
dimension at most that of the target: below it the whole image is null, and at equal dimension
every point of `s` is critical. -/
theorem addHaar_image_eq_zero_of_finrank_le_finrank (hEF : finrank ℝ E ≤ finrank ℝ F)
    (hdiff : ∀ x ∈ s, DifferentiableAt ℝ f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) :
    ν (f '' s) = 0 := by
  rcases hEF.lt_or_eq with hEF | hEF
  · exact DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank ν
      (fun x hx ↦ (hdiff x hx).differentiableWithinAt) hEF
  · borelize E
    refine addHaar_image_eq_zero_of_not_surjective_fderivWithin ν hEF
      (fun x hx ↦ (hdiff x hx).hasFDerivAt.hasFDerivWithinAt) fun x hx hsurj ↦ ?_
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    obtain ⟨v, hv⟩ := hsurj y
    exact hy (by rw [← hv, hs x hx, zero_apply])

end TauCeti
