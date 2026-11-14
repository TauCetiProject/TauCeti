/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Equality of the Poincaré Riemannian distance and Mathlib's hyperbolic distance on `ℍ`

Mathlib endows `ℍ` with an explicit hyperbolic `MetricSpace` structure via
`2 * arsinh (dist z w / (2 * √(z.im * w.im)))`, while `PoincareMetric/Basic.lean` endows its real
tangent bundle with the Poincaré Riemannian metric `⟨u, v⟩_ℂ / (Im z)²`. This file proves that the
two structures induce the same extended distance (`TauCeti.isRiemannianManifold_upperHalfPlane`),
reconciling the Riemannian metric space `TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ` with
Mathlib's `MetricSpace ℍ` and transferring properness and metric completeness.

Along the imaginary axis, the parametrised geodesic `geodesicLine 1 : t ↦ ⟨0, exp t⟩` is smooth of
unit Poincaré speed, giving an arc-length upper bound `ENNReal.ofReal d` between `I` and
`⟨0, exp d⟩`, while the logarithmic height `z ↦ Real.log z.im` has differential of Poincaré
operator norm at most `1` and provides the matching `1`-Lipschitz lower bound. Two-point
transitivity of `PSL(2, ℝ)` on parametrised geodesic lines
(`TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq`) and `PSL(2, ℝ)`-invariance of
both distances then equate them on arbitrary pairs of points.

## Main results

* `UpperHalfPlane.norm_mfderiv_log_im_le` and `UpperHalfPlane.edist_log_im_le_riemannianEDist`:
  the map `z ↦ Real.log z.im` is `1`-Lipschitz for the Poincaré Riemannian extended distance.
* `TauCeti.UpperHalfPlane.contMDiff_geodesicLine`,
  `TauCeti.UpperHalfPlane.norm_curveVelocity_geodesicLine`, and
  `TauCeti.UpperHalfPlane.pathELength_geodesicLine`: every `geodesicLine g` is smooth of unit
  Poincaré speed, with arc length `ENNReal.ofReal (b - a)` on `[a, b]`.
* `TauCeti.isRiemannianManifold_upperHalfPlane`: `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.metricSpace_ofRiemannianMetric_eq`,
  `TauCeti.UpperHalfPlane.properSpace_ofRiemannianMetric`, and
  `TauCeti.UpperHalfPlane.completeSpace_ofRiemannianMetric`: equality of the Riemannian metric space
  structure on `ℍ` with Mathlib's `MetricSpace ℍ`, and the resulting properness and completeness.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §1.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Example 3.16 and
  Theorem 6.15.
-/

public section

noncomputable section

open Bundle Manifold UpperHalfPlane
open scoped ContDiff ENNReal Manifold MatrixGroups NNReal Topology

/-! ### Smoothness and Lipschitz bound for the logarithmic height `z ↦ log (Im z)` -/

namespace UpperHalfPlane

/-- The real-part projection `ℍ → ℝ` is `C^n` for every smoothness exponent `n`. -/
theorem contMDiff_re {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n UpperHalfPlane.re :=
  Complex.reCLM.contDiff.contMDiff.comp (fun _ ↦ contMDiffAt_extChartAt)

/-- The imaginary-part projection `ℍ → ℝ` is `C^n` for every smoothness exponent `n`. -/
theorem contMDiff_im {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n UpperHalfPlane.im :=
  Complex.imCLM.contDiff.contMDiff.comp (fun _ ↦ contMDiffAt_extChartAt)

/-- The logarithmic height `z ↦ Real.log z.im` is `C^n` on `ℍ` for every smoothness exponent `n`. -/
theorem contMDiff_log_im {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n (fun z : ℍ ↦ Real.log z.im) :=
  fun z ↦ (Real.contDiffAt_log.2 z.im_ne_zero).contMDiffAt.comp z (contMDiff_im z)

/-- The vector-valued differential of `z ↦ Real.log z.im` at `z : ℍ` sends `v` to `u.im / z.im`,
where `u = tangentSpaceCastModel 𝓘(ℝ, ℂ) z v`. -/
theorem mvfderiv_log_im (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    mvfderiv 𝓘(ℝ, ℂ) (fun w : ℍ ↦ Real.log w.im) z v =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v).im / z.im := by
  rw [TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm]
  have hlocal : ((fun w : ℍ ↦ Real.log w.im) ∘ (extChartAt 𝓘(ℝ, ℂ) z).symm) =ᶠ[𝓝 (z : ℂ)]
      Real.log ∘ Complex.im := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have him : ((extChartAt 𝓘(ℝ, ℂ) z).symm w).im = w.im :=
      congr_arg Complex.im ((extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw))
    dsimp only [Function.comp_apply]
    rw [him]
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  have hfderiv : HasFDerivAt (Real.log ∘ Complex.im) (z.im⁻¹ • Complex.imCLM) (z : ℂ) :=
    (Real.hasDerivAt_log z.im_ne_zero).comp_hasFDerivAt (z : ℂ) Complex.imCLM.hasFDerivAt
  rw [hchart, hlocal.fderiv_eq, hfderiv.fderiv]
  simp [div_eq_mul_inv, mul_comm]

/-- The differential of `z ↦ Real.log z.im` has operator norm at most `1` with respect to the
Poincaré metric on `ℍ`. -/
theorem norm_mfderiv_log_im_le (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : ℍ ↦ Real.log w.im) z v‖ ≤ ‖v‖ := by
  rw [norm_tangentSpace_vectorSpace]
  change ‖mvfderiv 𝓘(ℝ, ℂ) (fun w : ℍ ↦ Real.log w.im) z v‖ ≤ ‖v‖
  rw [mvfderiv_log_im, norm_tangentSpace, Real.norm_eq_abs, abs_div, abs_of_pos z.im_pos]
  gcongr
  exact Complex.abs_im_le_norm _

/-- The logarithmic-height distance `edist (Real.log z.im) (Real.log w.im)` is bounded above by the
Poincaré Riemannian extended distance `Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w`. -/
theorem edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)) (Real.log z.im) (Real.log w.im)]
  simpa using TauCeti.Manifold.riemannianEDist_le_mul
    (f := fun x : ℍ ↦ Real.log x.im) contMDiff_log_im (C := 1) one_ne_zero
    (fun x v ↦ by simpa using norm_mfderiv_log_im_le x v) z w

end UpperHalfPlane

/-! ### Smoothness, unit speed, and arc length of parametrised geodesic lines -/

namespace TauCeti.UpperHalfPlane

/-- The upward imaginary-axis geodesic `geodesicLine 1 : t ↦ ⟨0, exp t⟩` is `C^n` for every
smoothness exponent `n`. -/
theorem contMDiff_geodesicLine_one {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine 1) := by
  apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
  have hfun : _root_.UpperHalfPlane.coe ∘ geodesicLine 1 =
      (Complex.I • Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ Real.exp := by
    funext t
    apply Complex.ext <;> simp [geodesicLine_one_apply, Complex.exp_ofReal_re]
  rw [hfun]
  exact ((Complex.I • Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp Real.contDiff_exp).contMDiff

/-- Every parametrised geodesic line `geodesicLine g` (`g : PSL(2, ℝ)`) is `C^n` on `ℝ`. -/
theorem contMDiff_geodesicLine {n : ℕ∞ω} (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine g) := by
  have hcomp : geodesicLine g = (g • ·) ∘ geodesicLine 1 := by
    funext t
    rw [Function.comp_apply, smul_geodesicLine, mul_one]
  rw [hcomp]
  exact (contMDiff_const_smul g).comp contMDiff_geodesicLine_one

/-- In the standard inclusion chart, the velocity vector of `geodesicLine 1` at `t : ℝ` is
`I * exp t`. -/
theorem tangentSpaceCastModel_curveVelocity_geodesicLine_one (t : ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (geodesicLine 1 t)
        (Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine 1) t) =
      Complex.I * (Real.exp t : ℂ) := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t :=
    (contMDiff_geodesicLine_one (n := 1) t).mdifferentiableAt one_ne_zero
  have hchart := Manifold.hasDerivAt_extChartAt_comp_curve (Manifold.hasMFDerivAt_curveVelocity hmd)
  have hfun : extChartAt 𝓘(ℝ, ℂ) (geodesicLine 1 t) ∘ geodesicLine 1 =
      fun s : ℝ ↦ Complex.I * (Real.exp s : ℂ) := by
    funext s
    apply Complex.ext <;> simp [geodesicLine_one_apply, Complex.exp_ofReal_re]
  rw [hfun] at hchart
  exact hchart.unique (((Real.hasDerivAt_exp t).ofReal_comp).const_mul Complex.I)

/-- The upward imaginary-axis geodesic `geodesicLine 1` has unit Poincaré velocity everywhere. -/
theorem norm_curveVelocity_geodesicLine_one (t : ℝ) :
    ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine 1) t‖ = 1 := by
  rw [_root_.UpperHalfPlane.norm_tangentSpace,
    tangentSpaceCastModel_curveVelocity_geodesicLine_one]
  simp [geodesicLine_one_apply]

private theorem norm_curveVelocity_congr {γ₁ γ₂ : ℝ → ℍ} (h : γ₁ = γ₂) (t : ℝ) :
    ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) γ₁ t‖ = ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) γ₂ t‖ := by
  cases h
  rfl

/-- Every parametrised geodesic line `geodesicLine g` (`g : PSL(2, ℝ)`) has unit `curveVelocity`
everywhere. -/
@[simp]
theorem norm_curveVelocity_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine g) t‖ = 1 := by
  have hcomp : geodesicLine g = (pslToIsom g : ℍ → ℍ) ∘ geodesicLine 1 := by
    funext s
    rw [Function.comp_apply, pslToIsom_apply, smul_geodesicLine, mul_one]
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) Set.univ t :=
    ((contMDiff_geodesicLine_one (n := 1) t).mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
  rw [norm_curveVelocity_congr hcomp, ← Manifold.curveVelocityWithin_univ,
    Manifold.curveVelocityWithin_map ((pslToIsom g).mdifferentiableAt (geodesicLine 1 t))
      uniqueDiffWithinAt_univ h1,
    Manifold.curveVelocityWithin_univ, (pslToIsom g).norm_mfderiv,
    norm_curveVelocity_geodesicLine_one]

/-- The Poincaré arc length of `geodesicLine 1` on `[a, b]` equals `ENNReal.ofReal (b - a)`. -/
theorem pathELength_geodesicLine_one (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine 1) a b = ENNReal.ofReal (b - a) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  have hcongr : (∫⁻ t in Set.Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t (1 : ℝ)‖ₑ) =
      ∫⁻ _ in Set.Ioo a b, (1 : ℝ≥0∞) :=
    MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ by
      rw [← Manifold.curveVelocity_apply, ← ofReal_norm, norm_curveVelocity_geodesicLine_one,
        ENNReal.ofReal_one]
  exact hcongr.trans ((MeasureTheory.setLIntegral_one _).trans Real.volume_Ioo)

/-- The Poincaré arc length of `geodesicLine g` on `[a, b]` equals `ENNReal.ofReal (b - a)`. -/
@[simp]
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) := by
  have hcomp : geodesicLine g = (pslToIsom g : ℍ → ℍ) ∘ geodesicLine 1 := by
    funext s
    rw [Function.comp_apply, pslToIsom_apply, smul_geodesicLine, mul_one]
  rw [hcomp, (pslToIsom g).pathELength_comp, pathELength_geodesicLine_one]

end TauCeti.UpperHalfPlane

/-! ### `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ` and agreement of metric structures -/

namespace TauCeti

open TauCeti.UpperHalfPlane

/-- **Mathlib's hyperbolic distance on `ℍ` is the Riemannian distance of the Poincaré metric.** -/
instance isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ where
  out z w := by
    obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
    have hg0 : pslToIsom g (geodesicLine 1 0) = z := by
      rw [pslToIsom_apply, smul_geodesicLine, mul_one, hz]
    have hgd : pslToIsom g (geodesicLine 1 (dist z w)) = w := by
      rw [pslToIsom_apply, smul_geodesicLine, mul_one, hw]
    rw [← hg0, ← hgd, (pslToIsom g).riemannianEDist_eq]
    rw [hg0, hgd, edist_dist]
    apply le_antisymm
    · have him0 : (geodesicLine 1 0).im = 1 := by simp [geodesicLine_one_apply]
      have himd : (geodesicLine 1 (dist z w)).im = Real.exp (dist z w) := by
        simp [geodesicLine_one_apply]
      calc ENNReal.ofReal (dist z w)
          = edist (Real.log (geodesicLine 1 0).im)
              (Real.log (geodesicLine 1 (dist z w)).im) := by
            rw [him0, himd, Real.log_one, Real.log_exp, edist_dist, Real.dist_eq, zero_sub,
              abs_neg, abs_of_nonneg dist_nonneg]
        _ ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0)
              (geodesicLine 1 (dist z w)) :=
            _root_.UpperHalfPlane.edist_log_im_le_riemannianEDist _ _
    · calc Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0) (geodesicLine 1 (dist z w))
          ≤ Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine 1) 0 (dist z w) :=
            Manifold.riemannianEDist_le_pathELength contMDiff_geodesicLine_one.contMDiffOn
              rfl rfl dist_nonneg
        _ = ENNReal.ofReal (dist z w) := by
            rw [pathELength_geodesicLine_one, sub_zero]

end TauCeti

namespace UpperHalfPlane

/-- The Poincaré Riemannian extended distance on `ℍ` equals Mathlib's `edist`. -/
theorem riemannianEDist_eq_edist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = edist z w :=
  (IsRiemannianManifold.out (I := 𝓘(ℝ, ℂ)) z w).symm

/-- The Poincaré Riemannian extended distance on `ℍ` is `ENNReal.ofReal (dist z w)`. -/
theorem riemannianEDist_eq_ofReal_dist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = ENNReal.ofReal (dist z w) := by
  rw [riemannianEDist_eq_edist, edist_dist]

/-- The real value of the Poincaré Riemannian extended distance on `ℍ` equals `dist z w`. -/
@[simp]
theorem toReal_riemannianEDist_eq_dist (z w : ℍ) :
    (Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w).toReal = dist z w :=
  (TauCeti.IsRiemannianManifold.dist_eq_toReal_riemannianEDist 𝓘(ℝ, ℂ) z w).symm

/-- Along the imaginary axis, the Poincaré Riemannian distance between `I` and `2 * I` is
`Real.log 2`, matching the unit-curvature normalisation `K = -1`. -/
theorem toReal_riemannianEDist_I_two_mul_I :
    (Manifold.riemannianEDist 𝓘(ℝ, ℂ) UpperHalfPlane.I
      ⟨2 * Complex.I, by simp⟩).toReal = Real.log 2 := by
  rw [toReal_riemannianEDist_eq_dist, dist_of_re_eq (by simp)]
  simp [Real.dist_eq, abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]

/-- The `EMetricSpace` induced by the Poincaré Riemannian metric coincides with Mathlib's
`EMetricSpace ℍ`. -/
theorem emetricSpace_ofRiemannianMetric_eq :
    EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ = inferInstanceAs (EMetricSpace ℍ) := by
  apply EMetricSpace.ext
  ext z w
  exact riemannianEDist_eq_edist z w

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- The `MetricSpace` induced by the Poincaré Riemannian metric (`MetricSpace.ofRiemannianMetric`)
coincides with Mathlib's `MetricSpace ℍ`. -/
theorem metricSpace_ofRiemannianMetric_eq :
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ = inferInstanceAs (MetricSpace ℍ) := by
  apply MetricSpace.ext
  ext z w
  exact _root_.UpperHalfPlane.toReal_riemannianEDist_eq_dist z w

/-- Equipped with the metric space induced by the Poincaré Riemannian metric, `ℍ` is a proper
metric space. -/
theorem properSpace_ofRiemannianMetric :
    @ProperSpace ℍ (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace := by
  rw [metricSpace_ofRiemannianMetric_eq]
  infer_instance

/-- Equipped with the metric space induced by the Poincaré Riemannian metric, `ℍ` is a complete
metric space. -/
theorem completeSpace_ofRiemannianMetric :
    @CompleteSpace ℍ (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toUniformSpace := by
  rw [metricSpace_ofRiemannianMetric_eq]
  infer_instance

end TauCeti.UpperHalfPlane

end
