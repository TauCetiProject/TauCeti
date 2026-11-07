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
`𝕜`-linear isometries of a normed space, indexed by a finite-dimensional real normed space. The
resulting `𝕜`-linear operator is a contraction, commutes with continuous linear maps that intertwine
the isometry families, and converges strongly to the value of the family at zero as the bump radius
shrinks to zero. The family may be given in any type of bundled linear isometries, such as linear
isometry equivalences.

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

open Filter MeasureTheory
open scoped Convolution

variable {𝕜 E F 𝓕 : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [FunLike 𝓕 F F] [LinearIsometryClass 𝓕 𝕜 F F]

private theorem integrable_normed_smul_neg (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (T : E → 𝓕) (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    Integrable (fun t ↦ phi.normed mu t • T (-t) f) mu :=
  (phi.continuous_normed.smul ((hT f).comp continuous_neg)).integrable_of_hasCompactSupport
    phi.hasCompactSupport_normed.smul_right

/-- Averaging a strongly continuous family of linear isometries against the normalized form of a
smooth bump centred at zero, as a continuous linear operator. The continuity hypothesis makes the
compactly supported integrand Bochner integrable. As with `MeasureTheory.average`, completeness is
needed only for the integral to have its usual value, and is therefore assumed by the convergence
theorem rather than this definition. -/
def normedBumpAverageL (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → 𝓕)
    (hT : ∀ f, Continuous fun h ↦ T h f) : F →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun f := ∫ t, phi.normed mu t • T (-t) f ∂mu
      map_add' f g := by
        simp only [map_add, smul_add]
        exact integral_add (integrable_normed_smul_neg phi mu T hT f)
          (integrable_normed_smul_neg phi mu T hT g)
      map_smul' c f := by simp only [map_smul, smul_comm _ c, integral_smul, RingHom.id_apply] } 1
    fun f ↦ calc
      ‖∫ t, phi.normed mu t • T (-t) f ∂mu‖ ≤ ∫ t, phi.normed mu t * ‖f‖ ∂mu :=
        norm_integral_le_of_norm_le (phi.integrable_normed.mul_const _) <| .of_forall fun t ↦ by
          rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), norm_map]
      _ = 1 * ‖f‖ := by rw [integral_mul_const, phi.integral_normed]

/-- The defining Bochner-integral formula for `normedBumpAverageL`. -/
theorem normedBumpAverageL_apply (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → 𝓕)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    normedBumpAverageL phi mu T hT f = ∫ t, phi.normed mu t • T (-t) f ∂mu := by
  rfl

/-- A continuous linear map between complete spaces can be moved inside a normalized-bump
average. -/
theorem map_normedBumpAverageL {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → 𝓕)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    A (normedBumpAverageL phi mu T hT f) =
      ∫ t, phi.normed mu t • A (T (-t) f) ∂mu := by
  simp only [normedBumpAverageL_apply,
    ← A.integral_comp_comm (integrable_normed_smul_neg phi mu T hT f), map_smul]

/-- A continuous linear map between complete spaces that intertwines two strongly continuous
families of linear isometries also intertwines their normalized-bump averages. -/
theorem normedBumpAverageL_comm {𝕜' G 𝓖 : Type*} [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]
    [FunLike 𝓖 G G] [LinearIsometryClass 𝓖 𝕜' G G] [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (T : E → 𝓕) (T' : E → 𝓖)
    (hT : ∀ f, Continuous fun h ↦ T h f) (hT' : ∀ g, Continuous fun h ↦ T' h g)
    (hA : ∀ h f, A (T h f) = T' h (A f)) (f : F) :
    A (normedBumpAverageL phi mu T hT f) = normedBumpAverageL phi mu T' hT' (A f) := by
  rw [map_normedBumpAverageL, normedBumpAverageL_apply]
  simp only [hA]

/-- A normalized-bump average of linear isometries has operator norm at most one. -/
theorem norm_normedBumpAverageL_le_one (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → 𝓕)
    (hT : ∀ f, Continuous fun h ↦ T h f) :
    ‖normedBumpAverageL phi mu T hT‖ ≤ 1 := by
  rw [normedBumpAverageL]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Normalized-bump averages of a strongly continuous family of linear isometries converge to
the value of the family at zero as the bump radii tend to zero. -/
theorem tendsto_normedBumpAverageL [CompleteSpace F] {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → 𝓕)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    Tendsto (fun i ↦ normedBumpAverageL (phi i) mu T hT f) l (nhds (T 0 f)) := by
  simpa only [normedBumpAverageL_apply, convolution_lsmul, zero_sub] using
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := mu) hphi (hT f) (0 : E)

end TauCeti
