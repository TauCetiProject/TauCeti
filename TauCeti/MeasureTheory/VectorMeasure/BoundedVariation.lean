/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import TauCeti.MeasureTheory.VectorMeasure.IntervalIntegral
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

/-!
# Derivative vector measures of Stieltjes functions

For a right-continuous monotone function of bounded variation, Mathlib's derivative vector
measure agrees with the positive Stieltjes measure viewed as a signed measure. This identifies
the classical derivative measure of a distribution function, including its atoms and singular
continuous part, with the measure whose distribution function it is.

The comparison uses the existing interval formulas for both constructions and uniqueness of
vector measures from their values on closed intervals.

For continuous BV integrators the variation measure is atomless. Consequently, indefinite
Stieltjes integrals of L¹ integrands are continuous, including the endpoints of a finite horizon.
-/

public section

open MeasureTheory Set

/-- For a Stieltjes function of bounded variation, the classical derivative vector measure
is its positive Stieltjes measure, viewed as a signed measure. In particular this comparison
retains both the jump atoms and any singular continuous part. -/
theorem StieltjesFunction.vectorMeasure_eq_toSignedMeasure
    {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [CompactIccSpace α] [MeasurableSpace α] [BorelSpace α]
    (f : StieltjesFunction α) [IsFiniteMeasure f.measure] (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure = f.measure.toSignedMeasure := by
  apply VectorMeasure.ext_of_Icc
  intro a b hab
  rw [hf.vectorMeasure_Icc hab, f.rightLim_eq,
    Measure.toSignedMeasure_apply_measurable measurableSet_Icc, measureReal_def,
    f.measure_Icc, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (f.mono.leftLim_le hab)

namespace BoundedVariationOn

variable {α F : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α]
  [OrderTopology α] [SecondCountableTopology α] [CompactIccSpace α]
  [MeasurableSpace α] [BorelSpace α] [NormedAddCommGroup F] [CompleteSpace F]
  {g : α → F}

/-- The variation of the Stieltjes vector measure of a continuous BV function has no atoms. -/
theorem nullSingletonClass_variation_vectorMeasure (hg : BoundedVariationOn g univ)
    (hcont : Continuous g) : NullSingletonClass hg.vectorMeasure.variation := by
  constructor
  intro x
  rw [hg.variation_vectorMeasure_singleton,
    hcont.continuousAt.continuousWithinAt.rightLim_eq,
    hcont.continuousAt.continuousWithinAt.leftLim_eq]
  simp

/-- An L¹ Stieltjes integrand against a continuous BV path has a continuous accumulated integral
on the whole closed horizon. The integrand need only be integrable on `(a,b]`, and need not be
continuous or bounded. The pairing can in particular be real scalar multiplication. -/
theorem continuousOn_setIntegral_Ioc_vectorMeasure [NormedSpace ℝ F]
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hg : BoundedVariationOn g univ) (hcont : Continuous g) {f : α → E} {a b : α}
    (hf : hg.vectorMeasure.IntegrableOn f (Ioc a b)) (B : E →L[ℝ] F →L[ℝ] G) :
    ContinuousOn (fun t ↦ ∫ᵛ x in Ioc a t, f x ∂[B; hg.vectorMeasure]) (Icc a b) := by
  have := hg.nullSingletonClass_variation_vectorMeasure hcont
  exact hf.continuousOn_setIntegral_Ioc fun t _ ↦ measure_singleton t

end BoundedVariationOn
