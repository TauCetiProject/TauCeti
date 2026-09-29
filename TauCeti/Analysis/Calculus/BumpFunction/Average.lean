/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Normalized bump averages

This file defines averaging against a normalized smooth bump for a strongly continuous family of
linear isometries on a real normed space. The resulting continuous linear operator is a contraction,
commutes with continuous linear maps that intertwine the isometry families, and converges strongly
to the value of the family at zero as the bump radius shrinks to zero.

## Main declarations

* `TauCeti.normedBumpAverageL`: normalized-bump averaging for a strongly continuous family of
  linear isometries on a normed space.
* `TauCeti.normedBumpAverageL_comm`: an intertwining continuous linear map commutes with
  normalized-bump averaging.
* `TauCeti.norm_normedBumpAverageL_le_one`: normalized-bump averaging is a contraction.
* `TauCeti.tendsto_normedBumpAverageL`: normalized-bump averages converge strongly as their radii
  shrink to zero.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Proposition 4.21.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ

/-- The normalized-bump average of a strongly continuous family of linear isometries, before it
is bundled as a continuous linear map by `TauCeti.normedBumpAverageL`. -/
private def normedBumpAverage (phi : ContDiffBump (0 : E))
    (mu : Measure E) (T : E → F ≃ₗᵢ[ℝ] F) (f : F) : F :=
  ∫ t, phi.normed mu t • T (-t) f ∂mu

private theorem integrable_normed_smul_neg (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [mu.IsAddHaarMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F) (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    Integrable (fun t ↦ phi.normed mu t • T (-t) f) mu := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact phi.continuous_normed.smul
      ((hT f).comp continuous_neg)
  · exact phi.hasCompactSupport_normed.smul_right

private theorem normedBumpAverage_add (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [mu.IsAddHaarMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F) (hT : ∀ f, Continuous fun h ↦ T h f) (f g : F) :
    normedBumpAverage phi mu T (f + g) =
      normedBumpAverage phi mu T f + normedBumpAverage phi mu T g := by
  rw [normedBumpAverage, normedBumpAverage, normedBumpAverage,
    ← integral_add (integrable_normed_smul_neg phi mu T hT f)
      (integrable_normed_smul_neg phi mu T hT g)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_add, smul_add]

omit [BorelSpace E] in
private theorem normedBumpAverage_smul (phi : ContDiffBump (0 : E)) (mu : Measure E)
    (T : E → F ≃ₗᵢ[ℝ] F) (c : ℝ) (f : F) :
    normedBumpAverage phi mu T (c • f) = c • normedBumpAverage phi mu T f := by
  rw [normedBumpAverage, normedBumpAverage, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_smul, smul_smul, mul_comm c]

private theorem norm_normedBumpAverage_le (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [mu.IsAddHaarMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F) (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    ‖normedBumpAverage phi mu T f‖ ≤ ‖f‖ := by
  calc
    ‖normedBumpAverage phi mu T f‖ ≤
        ∫ t, ‖phi.normed mu t • T (-t) f‖ ∂mu := by
      rw [normedBumpAverage]
      exact norm_integral_le_of_norm_le
        (integrable_normed_smul_neg phi mu T hT f).norm
        (Eventually.of_forall fun _ ↦ le_rfl)
    _ = ∫ t, phi.normed mu t * ‖f‖ ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), (T (-t)).norm_map]
    _ = ‖f‖ := by rw [integral_mul_const, phi.integral_normed, one_mul]

/-- Averaging a strongly continuous family of linear isometries against the normalized form of a
smooth bump centred at zero, as a continuous linear operator. The continuity hypothesis makes the
compactly supported integrand Bochner integrable. As with `MeasureTheory.average`, completeness is
needed only for the integral to have its usual value, and is therefore assumed by the convergence
theorem rather than this definition. -/
def normedBumpAverageL (phi : ContDiffBump (0 : E)) (mu : Measure E) [mu.IsAddHaarMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) : F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := normedBumpAverage phi mu T
      map_add' := normedBumpAverage_add phi mu T hT
      map_smul' := normedBumpAverage_smul phi mu T } 1
    fun f ↦ by rw [one_mul]; exact norm_normedBumpAverage_le phi mu T hT f

/-- The defining Bochner-integral formula for `normedBumpAverageL`. -/
theorem normedBumpAverageL_apply (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    normedBumpAverageL phi mu T hT f = ∫ t, phi.normed mu t • T (-t) f ∂mu := by
  rfl

/-- A continuous linear map between complete spaces commutes with a normalized-bump average. -/
theorem map_normedBumpAverageL {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    A (normedBumpAverageL phi mu T hT f) =
      ∫ t, phi.normed mu t • A (T (-t) f) ∂mu := by
  rw [normedBumpAverageL_apply,
    ← A.integral_comp_comm (integrable_normed_smul_neg phi mu T hT f)]
  apply integral_congr_ae
  filter_upwards with t
  rw [map_smul]

/-- A continuous linear map between complete spaces that intertwines two strongly continuous
families of linear isometries also intertwines their normalized-bump averages. -/
theorem normedBumpAverageL_comm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → F ≃ₗᵢ[ℝ] F) (T' : E → G ≃ₗᵢ[ℝ] G)
    (hT : ∀ f, Continuous fun h ↦ T h f) (hT' : ∀ g, Continuous fun h ↦ T' h g)
    (hA : ∀ h f, A (T h f) = T' h (A f)) (f : F) :
    A (normedBumpAverageL phi mu T hT f) = normedBumpAverageL phi mu T' hT' (A f) := by
  rw [map_normedBumpAverageL, normedBumpAverageL_apply]
  simp only [hA]

/-- A normalized-bump average of linear isometries has operator norm at most one. -/
theorem norm_normedBumpAverageL_le_one (phi : ContDiffBump (0 : E))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) :
    ‖normedBumpAverageL phi mu T hT‖ ≤ 1 := by
  rw [normedBumpAverageL]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Normalized-bump averages of a strongly continuous family of linear isometries converge to
the value of the family at zero as the bump radii tend to zero. -/
theorem tendsto_normedBumpAverageL [CompleteSpace F] {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    Tendsto (fun i ↦ normedBumpAverageL (phi i) mu T hT f) l (nhds (T 0 f)) := by
  have hval : ∀ i, normedBumpAverageL (phi i) mu T hT f =
      ((phi i).normed mu ⋆[lsmul ℝ ℝ, mu] fun h ↦ T h f) 0 := fun i ↦ by
    rw [normedBumpAverageL_apply, convolution_lsmul]
    simp only [zero_sub]
  simpa only [hval] using
    ContDiffBump.convolution_tendsto_right_of_continuous hphi (hT f) (0 : E)

end TauCeti
