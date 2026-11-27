/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.Analysis.Matrix.SkewAdjoint

/-!
# Haar measures on skew-Hermitian matrices

The Frobenius norm gives the same topology on complex matrices as the topology of entries.
This file transfers Borel and Haar structures between these presentations and makes the change
of variables formula available for derivatives computed in the Frobenius norm and measures on the
entry topology.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Matrix

variable {n : Type*} [Fintype n]

open scoped Matrix.Norms.Frobenius in
/-- The Borel structure of the skew-Hermitian matrices for the topology of the Frobenius norm,
which is the topology of entries up to unfolding. -/
theorem borelSpace_skewAdjoint_frobenius : @BorelSpace (skewAdjoint.submodule ℝ (Matrix n n ℂ))
    NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace _ :=
  ⟨by exact (@Subtype.borelSpace (Matrix n n ℂ) instTopologicalSpaceMatrix _ inferInstance
    _).measurable_eq⟩

end Matrix

namespace MeasureTheory.Measure

variable {n : Type*} [Fintype n] (μ : Measure (skewAdjoint.submodule ℝ (Matrix n n ℂ)))
  [μ.IsAddHaarMeasure]

open scoped Matrix.Norms.Frobenius in
/-- An additive Haar measure for the topology of entries is one for the Frobenius topology. -/
theorem isAddHaarMeasure_skewAdjoint_frobenius :
    @Measure.IsAddHaarMeasure (skewAdjoint.submodule ℝ (Matrix n n ℂ)) _
      NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace _ μ := by
  exact ‹μ.IsAddHaarMeasure›

omit [Fintype n] in
open scoped Matrix.Norms.Frobenius in
/-- An additive Haar measure on the skew-Hermitian matrices is invariant under negation. -/
instance isNegInvariant_skewAdjoint [Finite n] : μ.IsNegInvariant := by
  have := Fintype.ofFinite n
  have := Matrix.borelSpace_skewAdjoint_frobenius (n := n)
  have := μ.isAddHaarMeasure_skewAdjoint_frobenius
  have := FiniteDimensional.proper_real (skewAdjoint.submodule ℝ (Matrix n n ℂ))
  exact @Measure.IsAddHaarMeasure.isNegInvariant_of_regular _ _
    NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace _ _ _ μ _ _ _

omit [Fintype n] in
open scoped Matrix.Norms.Frobenius in
/-- The change of variables formula on the skew-Hermitian matrices, for a Haar measure of the
topology of entries and derivatives for the Frobenius norm. -/
theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul_skewAdjoint [Finite n]
    {s : Set (skewAdjoint.submodule ℝ (Matrix n n ℂ))}
    {f : skewAdjoint.submodule ℝ (Matrix n n ℂ) → skewAdjoint.submodule ℝ (Matrix n n ℂ)}
    {f' : skewAdjoint.submodule ℝ (Matrix n n ℂ) →
      skewAdjoint.submodule ℝ (Matrix n n ℂ) →L[ℝ] skewAdjoint.submodule ℝ (Matrix n n ℂ)}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)
    (g : skewAdjoint.submodule ℝ (Matrix n n ℂ) → ℝ≥0∞) :
    ∫⁻ x in f '' s, g x ∂μ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ := by
  have := Fintype.ofFinite n
  have := Matrix.borelSpace_skewAdjoint_frobenius (n := n)
  have := μ.isAddHaarMeasure_skewAdjoint_frobenius
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf' hf g

end MeasureTheory.Measure
