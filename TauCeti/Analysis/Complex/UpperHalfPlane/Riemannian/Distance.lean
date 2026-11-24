/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance

/-!
# The hyperbolic distance on `ℍ` is the Riemannian distance of the Poincaré metric

Mathlib equips the complex upper half-plane `ℍ` with the hyperbolic distance
`dist z w = 2 arsinh (‖z - w‖ / (2 √(Im z Im w)))`, while
`TauCeti.UpperHalfPlane.poincareRiemannianMetric` equips the tangent bundle of `ℍ` with the smooth
Poincaré Riemannian metric `(dx² + dy²) / y²`. This file proves that Mathlib's metric-space
structure on `ℍ` is the Riemannian distance induced by the Poincaré metric:
`TauCeti.isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`.

Rather than differentiating the `arsinh` formula directly, the proof combines two geometric bounds
with two-point transitivity of `PSL(2, ℝ)` on parametrised geodesic lines
(`TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq`):

* **Lower bound (`UpperHalfPlane.edist_log_im_le_riemannianEDist`):** the smooth map
  `z ↦ log (Im z)` from `ℍ` to `ℝ` has differential `(Im v) / Im z` in the inclusion chart, whose
  Euclidean norm is at most `‖v‖ / Im z`, the Poincaré norm of `v`. Hence `z ↦ log (Im z)` is
  `1`-Lipschitz for the Riemannian extended distance (`TauCeti.Manifold.riemannianEDist_le_mul`), so
  `edist (log (Im z)) (log (Im w)) ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`. Moving any `z, w` by an element
  of `PSL(2, ℝ)` onto the upward imaginary axis puts `z` at height `1` and `w` at height
  `exp (dist z w)`, and invariance of `riemannianEDist` under the Riemannian isometry `pslToIsom`
  gives `edist z w ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`.
* **Upper bound (`TauCeti.UpperHalfPlane.pathELength_geodesicLine`):** the upward imaginary axis
  `t ↦ i exp t` has unit Poincaré speed everywhere, hence so does every `PSL(2, ℝ)`-translate
  `geodesicLine g`. Its Riemannian length on `[0, dist z w]` is `ENNReal.ofReal (dist z w) =
  edist z w`, giving `riemannianEDist 𝓘(ℝ, ℂ) z w ≤ edist z w`.

Identifying `edist` with `riemannianEDist` immediately implies via
`TauCeti.MetricSpace.ofRiemannianMetric_eq` that `TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ`
equals Mathlib's `MetricSpace ℍ`, and therefore inherits completeness from `ProperSpace ℍ`
(`completeSpace_of_riemannianMetric`).

## Main results

* `UpperHalfPlane.edist_log_im_le_riemannianEDist`: `z ↦ log (Im z)` does not increase Riemannian
  extended distance.
* `TauCeti.UpperHalfPlane.contMDiff_geodesicLine`,
  `TauCeti.UpperHalfPlane.norm_mfderiv_geodesicLine`, and
  `TauCeti.UpperHalfPlane.pathELength_geodesicLine`: every `geodesicLine g` is real-analytic and
  unit-speed for the Poincaré metric, of Riemannian length `ENNReal.ofReal (b - a)` on `[a, b]`.
* `TauCeti.isRiemannianManifold_upperHalfPlane`: `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`, with `simp`
  lemma `UpperHalfPlane.riemannianEDist_eq_edist`.
* `TauCeti.UpperHalfPlane.completeSpace_of_riemannianMetric`: the metric-space structure induced by
  the Poincaré metric is complete.

## References

* Svetlana Katok, *Fuchsian Groups*, University of Chicago Press (1992), §1.2.
* Alan Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), §7.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  and Theorem 6.15.
-/

public section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold MatrixGroups NNReal UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

private theorem norm_mfderiv_logIm_le (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : ℍ ↦ Real.log w.im) z v‖ ≤ (1 : ℝ≥0) * ‖v‖ := by
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : ℍ ↦ Real.log w.im) z :=
    (TauCeti.UpperHalfPlane.contMDiff_log_im (n := ∞) z).mdifferentiableAt (by simp)
  have hfderiv : HasFDerivAt
      (extChartAt 𝓘(ℝ, ℝ) (Real.log z.im) ∘ (fun w : ℍ ↦ Real.log w.im) ∘ ofComplex)
      ((z.im)⁻¹ • (Complex.imCLM : ℂ →L[ℝ] ℝ)) (z : ℂ) :=
    ((Real.hasDerivAt_log z.im_ne_zero).comp_hasFDerivAt (z : ℂ)
      Complex.imCLM.hasFDerivAt).congr_of_eventuallyEq <|
      by simpa [Function.comp_def] using
        (eventuallyEq_coe_comp_ofComplex z.im_pos).fun_comp (fun w : ℂ ↦ Real.log w.im)
  rw [norm_tangentSpace_vectorSpace, NormedSpace.fromTangentSpace,
    z.tangentSpaceCastModel_mfderiv_apply hmdiff v, hfderiv.fderiv, z.norm_tangentSpace v]
  simpa [abs_of_pos z.im_pos, div_eq_inv_mul] using
    mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v))
      (inv_nonneg.2 z.im_pos.le)

/-- The map `z ↦ log (Im z)` does not increase Riemannian extended distance from the Poincaré
upper half-plane to the Euclidean real line. -/
theorem edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), ← one_mul (Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w),
    ← ENNReal.coe_one]
  exact TauCeti.Manifold.riemannianEDist_le_mul TauCeti.UpperHalfPlane.contMDiff_log_im one_ne_zero
    norm_mfderiv_logIm_le z w

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

private theorem contMDiff_geodesicLine_one {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine (1 : PSL(2, ℝ))) := by
  apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
  have hfun : UpperHalfPlane.coe ∘ geodesicLine (1 : PSL(2, ℝ)) =
      fun t : ℝ ↦ (Real.exp t : ℂ) * Complex.I :=
    funext coe_geodesicLine_one
  rw [hfun, contMDiff_iff_contDiff]
  exact (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul contDiff_const

/-- Every parametrised geodesic line `geodesicLine g` in `ℍ` is real-analytic (and hence smooth of
every order `n : ℕ∞ω`). -/
theorem contMDiff_geodesicLine {n : ℕ∞ω} (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine g) := by
  have hcomp : geodesicLine g = (g • ·) ∘ geodesicLine (1 : PSL(2, ℝ)) := by
    funext t
    simp
  rw [hcomp]
  exact (contMDiff_const_smul g).comp contMDiff_geodesicLine_one

private theorem norm_mfderiv_geodesicLine_one (t : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) t) :
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t v‖ = ‖v‖ := by
  rw [norm_tangentSpace,
    ((contMDiff_geodesicLine_one (n := ∞) t).mdifferentiableAt (by simp)
      |>.tangentSpaceCastModel_mfderiv_apply v)]
  have hwritten : writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) t (geodesicLine (1 : PSL(2, ℝ))) =
      fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I := by
    funext s
    simp [writtenInExtChartAt, coe_geodesicLine_one]
  have hchart : extChartAt 𝓘(ℝ, ℝ) t t = t := by simp
  have hfderiv : HasFDerivAt (fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I)
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((Real.exp t : ℂ) * Complex.I)) t :=
    ((Real.hasDerivAt_exp t).ofReal_comp.mul_const Complex.I).hasFDerivAt
  have him : (geodesicLine (1 : PSL(2, ℝ)) t).im = Real.exp t := by
    simp [geodesicLine_one_apply]
  have hv : ‖tangentSpaceCastModel 𝓘(ℝ, ℝ) t v‖ = ‖v‖ := by
    rw [norm_tangentSpace_vectorSpace, NormedSpace.fromTangentSpace]
  rw [hwritten, hchart, hfderiv.fderiv]
  simp [him, hv, Real.exp_ne_zero t]

/-- Every parametrised geodesic line `geodesicLine g` has differential preserving norms at every
parameter `t : ℝ`. -/
@[simp]
theorem norm_mfderiv_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) t) :
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t v‖ = ‖v‖ := by
  have hcomp : geodesicLine g = pslToIsom g ∘ geodesicLine (1 : PSL(2, ℝ)) := by
    funext s
    simp
  rw [hcomp, mfderiv_comp_apply t ((pslToIsom g).mdifferentiableAt _)
    ((contMDiff_geodesicLine_one (n := ∞) t).mdifferentiableAt (by simp)) v,
    (pslToIsom g).norm_mfderiv, norm_mfderiv_geodesicLine_one]

/-- Every parametrised geodesic line `geodesicLine g` has unit Poincaré speed everywhere. -/
@[simp]
theorem norm_curveVelocity_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine g) t‖ = 1 := by
  have hvel : Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine g) t =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t ((NormedSpace.fromTangentSpace t).symm 1) := by
    rw [Manifold.curveVelocity_apply]
    exact congrArg _ (NormedSpace.fromTangentSpace_symm_apply t 1).symm
  rw [hvel, norm_mfderiv_geodesicLine, norm_tangentSpace_vectorSpace]
  simp

/-- On any interval `[a, b]`, `geodesicLine g` has Poincaré path length `ENNReal.ofReal (b - a)`
(which is `0` when `b < a`). -/
@[simp]
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) :=
  TauCeti.Manifold.pathELength_eq_of_norm_curveVelocity_eq_one fun t _ ↦
    norm_curveVelocity_geodesicLine g t

end TauCeti.UpperHalfPlane

namespace TauCeti

open _root_.UpperHalfPlane TauCeti.UpperHalfPlane

/-- Mathlib's hyperbolic metric on the complex upper half-plane `ℍ` is the Riemannian distance of
the Poincaré metric `TauCeti.UpperHalfPlane.poincareRiemannianMetric`. -/
instance isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ where
  out z w := by
    obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
    apply le_antisymm
    · have himz : Real.log (g⁻¹ • z).im = 0 := by
        simpa only [hz] using log_im_inv_smul_geodesicLine g 0
      have himw : Real.log (g⁻¹ • w).im = dist z w := by
        simpa only [hw] using log_im_inv_smul_geodesicLine g (dist z w)
      have hed : edist z w = edist (Real.log (g⁻¹ • z).im) (Real.log (g⁻¹ • w).im) := by
        rw [himz, himw]
        simp [edist_dist, Real.dist_eq, abs_of_nonneg dist_nonneg]
      calc edist z w
          = edist (Real.log (g⁻¹ • z).im) (Real.log (g⁻¹ • w).im) := hed
        _ ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) (g⁻¹ • z) (g⁻¹ • w) :=
            edist_log_im_le_riemannianEDist _ _
        _ = Manifold.riemannianEDist 𝓘(ℝ, ℂ) (pslToIsom g⁻¹ z) (pslToIsom g⁻¹ w) := by
            rw [pslToIsom_apply, pslToIsom_apply]
        _ = Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := (pslToIsom g⁻¹).riemannianEDist_eq z w
    · calc Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w
          ≤ Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) 0 (dist z w) :=
            Manifold.riemannianEDist_le_pathELength (contMDiff_geodesicLine g).contMDiffOn
              hz hw dist_nonneg
        _ = ENNReal.ofReal (dist z w - 0) := pathELength_geodesicLine g 0 (dist z w)
        _ = edist z w := by rw [sub_zero, edist_dist]

end TauCeti

namespace UpperHalfPlane

/-- The Riemannian extended distance of the Poincaré metric on `ℍ` equals Mathlib's `edist`. -/
@[simp]
theorem riemannianEDist_eq_edist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = edist z w :=
  (IsRiemannianManifold.out (I := 𝓘(ℝ, ℂ)) z w).symm

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- The Riemannian distance of the Poincaré metric on `ℍ` is complete, matching the `complete`
field of `TauCeti.HyperbolicMetric`. -/
theorem completeSpace_of_riemannianMetric :
    @CompleteSpace ℍ
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toUniformSpace :=
  MetricSpace.completeSpace_ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ

end TauCeti.UpperHalfPlane

end
