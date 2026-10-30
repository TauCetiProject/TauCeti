/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import TauCeti.Analysis.Calculus.FDeriv.Dimension
import TauCeti.MeasureTheory.Measure.Haar.Hausdorff

/-!
# Sard's lemma when the source has smaller dimension

This file proves the lower-dimensional-source case of finite-dimensional Sard's theorem. If a
differentiable map goes from a finite-dimensional real normed space to one of strictly larger
dimension, then the image of every subset of the source has additive Haar measure zero. In
particular, the whole range is null.

Every derivative in this dimension range is nonsurjective, so the range is exactly the set of
critical values. The proof uses the Hausdorff-dimension route already developed in Mathlib:
`DifferentiableOn.dimH_image_le` says that differentiable maps do not increase dimension, and
`addHaar_eq_zero_of_dimH_lt_finrank` turns the strict dimension bound into nullity for every
normalization of additive Haar measure.

Together with the equal-dimensional case, this isolates the higher-regularity Morse--Sard argument
to the remaining case where the source dimension is larger.

## Main declarations

* `DifferentiableOn.addHaar_image_eq_zero_of_dimH_lt_finrank`: a differentiable map on a
  set of sufficiently small Hausdorff dimension sends it to an additive-Haar-null set.
* `DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`: a map differentiable on a
  set in a strictly lower-dimensional space sends that set to an additive-Haar-null set.
* `Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank`: the whole range of such a
  map is additive-Haar-null.
* `TauCeti.not_surjective_fderiv_of_finrank_lt_finrank`: every derivative in this dimension range
  is nonsurjective.
* `TauCeti.setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank`: every point belongs to the
  critical locus in this dimension range.
* `Differentiable.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank`: the
  critical values are additive-Haar-null, in the form used by Sard's theorem.

The Hausdorff-dimension argument follows the one used for the lower-dimensional Sard corollary in
Mathlib's `Topology.MetricSpace.HausdorffDimension`.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F}
  (ν : Measure F) [IsAddHaarMeasure ν]

omit [FiniteDimensional ℝ E] in
/-- A differentiable map on a set of Hausdorff dimension strictly smaller than the dimension of
the codomain sends that set to an additive-Haar-null set.

The source may be any real normed space, the codomain may carry an arbitrary finite-dimensional
norm, and `ν` may be any normalization of additive Haar measure. -/
theorem _root_.DifferentiableOn.addHaar_image_eq_zero_of_dimH_lt_finrank
    (hf : DifferentiableOn ℝ f s) (hsF : dimH s < finrank ℝ F) : ν (f '' s) = 0 :=
  addHaar_eq_zero_of_dimH_lt_finrank ν (hf.dimH_image_le.trans_lt hsF)

/-- A map differentiable on a subset of a finite-dimensional real normed space sends that set
to an additive-Haar-null set when the codomain has strictly larger dimension. -/
theorem _root_.DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank
    (hf : DifferentiableOn ℝ f s) (hEF : finrank ℝ E < finrank ℝ F) :
    ν (f '' s) = 0 := by
  apply hf.addHaar_image_eq_zero_of_dimH_lt_finrank ν
  exact (dimH_mono (subset_univ s)).trans_lt <| by
    simpa only [Real.dimH_univ_eq_finrank, Nat.cast_lt] using hEF

/-- A differentiable map from a finite-dimensional real normed space to a strictly
higher-dimensional one has additive-Haar-null range. This is the lower-dimensional-source case of
Sard's theorem: every point of the source is critical because no derivative can be surjective. -/
theorem _root_.Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank
    (hf : Differentiable ℝ f) (hEF : finrank ℝ E < finrank ℝ F) :
    ν (range f) = 0 := by
  rw [← image_univ]
  exact hf.differentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank ν hEF

/-- The critical values of a differentiable map from a finite-dimensional real normed space to a
strictly higher-dimensional one have additive Haar measure zero. In this dimension range every
point is critical, but stating the result for the critical locus gives the Sard form consumed by
later regular-value arguments. -/
theorem _root_.Differentiable.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank
    (hf : Differentiable ℝ f) (hEF : finrank ℝ E < finrank ℝ F) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  rw [setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank f hEF, image_univ]
  exact Differentiable.addHaar_range_eq_zero_of_finrank_lt_finrank ν hf hEF

end TauCeti

end
