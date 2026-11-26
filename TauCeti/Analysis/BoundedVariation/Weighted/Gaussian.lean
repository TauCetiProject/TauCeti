/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# The measure of the Gaussian weight

The measure `e^{−W} · volume` of the Gaussian weight `W = TauCeti.gaussianWeight E` is the standard
Gaussian measure `ProbabilityTheory.stdGaussian E`
(`TauCeti.withDensity_exp_neg_gaussianWeight`), so the Gaussian perimeter
`TauCeti.gaussianPerimeter` is the weighted perimeter of this measure. The density comes from
`TauCeti.Probability.stdGaussian_eq_withDensity_norm`.

Consequences: the Gaussian density `e^{−W}` is Lebesgue integrable
(`TauCeti.integrable_exp_neg_gaussianWeight`), and the Gaussian measure of a translate `v + A` is
`∫_A e^{−⟨y, v⟩ − ‖v‖² / 2} e^{−W(y)} dy` (`TauCeti.measureReal_stdGaussian_vadd`).
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The measure of the Gaussian weight is the standard Gaussian measure. -/
theorem withDensity_exp_neg_gaussianWeight :
    (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-gaussianWeight E x))) =
      ProbabilityTheory.stdGaussian E := by
  rw [Probability.stdGaussian_eq_withDensity_norm]
  congr 1 with x
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, gaussianWeight_def]
  congr 2
  ring

/-- The Gaussian density `e^{−W}` is Lebesgue integrable. -/
theorem integrable_exp_neg_gaussianWeight :
    Integrable fun x : E => Real.exp (-gaussianWeight E x) :=
  MeasureTheory.integrable_of_eq_withDensity withDensity_exp_neg_gaussianWeight.symm
    continuous_exp_neg_gaussianWeight.aemeasurable (ae_of_all _ fun _ => (Real.exp_pos _).le)

/-- The Gaussian measure of a translate `v + A`, as an integral over `A`. -/
theorem measureReal_stdGaussian_vadd (v : E) {A : Set E} (hA : NullMeasurableSet A) :
    (ProbabilityTheory.stdGaussian E).real (v +ᵥ A) =
      ∫ y in A, Real.exp (-(⟪y, v⟫ + ‖v‖ ^ 2 / 2)) * Real.exp (-gaussianWeight E y) := by
  rw [← withDensity_exp_neg_gaussianWeight, MeasureTheory.measureReal_withDensity_ofReal
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (hA.vadd v)
    continuous_exp_neg_gaussianWeight.aemeasurable]
  have hpre : (fun y : E => y + v) ⁻¹' (v +ᵥ A) = A := by
    ext y
    simp [Set.mem_vadd_set, add_comm]
  rw [← (measurePreserving_add_right volume v).setIntegral_preimage_emb
    (MeasurableEquiv.addRight v).measurableEmbedding, hpre]
  exact integral_congr_ae (ae_of_all _ fun y => exp_neg_gaussianWeight_add y v)

end TauCeti
