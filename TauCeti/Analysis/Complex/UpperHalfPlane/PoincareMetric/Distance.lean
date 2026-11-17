/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance

/-!
# The Poincaré Riemannian distance agrees with Mathlib's hyperbolic metric

Mathlib equips `ℍ` with an explicit hyperbolic metric `UpperHalfPlane.dist_eq`, whose vertical
axis `t ↦ i exp t` is a unit-speed geodesic (`UpperHalfPlane.isometry_vertical_line`). Here we
prove that this metric is the Riemannian distance of the Poincaré tensor
`TauCeti.UpperHalfPlane.poincareRiemannianMetric`, establishing
`TauCeti.isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`.

Every `PSL(2, ℝ)`-translate `geodesicLine g` of the imaginary axis is real-analytic and has unit
Poincaré speed (`norm_curveVelocity_geodesicLine`), so its Poincaré path length over `[a, b]` is
`ENNReal.ofReal (b - a)` (`pathELength_geodesicLine`). Since any two points `z, w : ℍ` are joined
by some `geodesicLine g` with parameters `0` and `dist z w`, this gives the upper bound
`riemannianEDist 𝓘(ℝ, ℂ) z w ≤ edist z w`.

For the lower bound, the logarithmic height function `z ↦ Real.log z.im` has differential bounded
by `1` in the Poincaré norm (`|dy| / y ≤ √(dx² + dy²) / y`), so
`TauCeti.Manifold.riemannianEDist_le_mul` yields
`edist (Real.log z.im) (Real.log w.im) ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`. Moving `z` and `w` to `i`
and `i exp (dist z w)` by the Riemannian isometry `pslIsomHom g⁻¹` gives the matching lower bound
`edist z w ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`.

As an immediate consequence, Mathlib's `ProperSpace ℍ` transfers completeness to the intrinsic
Riemannian metric space `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ`.

## Main results

* `TauCeti.UpperHalfPlane.contMDiff_geodesicLine`: every geodesic line `geodesicLine g` is
  real-analytic (hence `C^n` for all `n : ℕ∞ω`).
* `TauCeti.UpperHalfPlane.norm_curveVelocity_geodesicLine`: every geodesic line has unit Poincaré
  speed.
* `TauCeti.UpperHalfPlane.pathELength_geodesicLine` and
  `TauCeti.UpperHalfPlane.pathELength_geodesicLine_eq_edist`: the Poincaré length of a geodesic
  segment equals the parameter difference (and the hyperbolic distance when `a ≤ b`).
* `UpperHalfPlane.edist_log_im_le_riemannianEDist`: `z ↦ Real.log z.im` is 1-Lipschitz for the
  Poincaré Riemannian extended distance.
* `TauCeti.isRiemannianManifold_upperHalfPlane`: Mathlib's hyperbolic metric on `ℍ` is the
  Riemannian distance of the Poincaré metric (`IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`).
* `TauCeti.UpperHalfPlane.completeSpace_of_riemannianMetric`: the intrinsic Riemannian metric on
  `ℍ` is complete.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press (1992), §1.1–§1.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold MatrixGroups NNReal UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

/-! ### Smoothness, speed, and length of geodesic lines -/

private theorem coe_geodesicLine_one (t : ℝ) :
    ((geodesicLine (1 : PSL(2, ℝ)) t : ℍ) : ℂ) = (Real.exp t : ℂ) * Complex.I := by
  rw [geodesicLine_one_apply, _root_.UpperHalfPlane.coe_mk]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- Every geodesic line `geodesicLine g` is `C^n` (indeed real-analytic) as a curve in the
real manifold `ℍ`. -/
theorem contMDiff_geodesicLine {n : ℕ∞ω} (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) n (geodesicLine g) := by
  have h1 : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ω (geodesicLine (1 : PSL(2, ℝ))) := by
    refine ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe ?_
    have hcomp : ((↑) : ℍ → ℂ) ∘ geodesicLine (1 : PSL(2, ℝ)) =
        fun t : ℝ ↦ (Real.exp t : ℂ) * Complex.I :=
      funext coe_geodesicLine_one
    rw [hcomp]
    exact ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul contDiff_const).contMDiff
  have hcomp : geodesicLine g = (g • ·) ∘ geodesicLine (1 : PSL(2, ℝ)) :=
    funext fun t ↦ by simp
  rw [hcomp]
  exact ((contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ω) g).comp h1).of_le le_top

private theorem norm_curveVelocity_geodesicLine_one (t : ℝ) :
    ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t‖ = 1 := by
  rw [_root_.UpperHalfPlane.norm_tangentSpace]
  have hd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t :=
    (contMDiff_geodesicLine (n := ω) 1 t).mdifferentiableAt (by simp)
  have hcast := hd.tangentSpaceCastModel_mfderiv_apply ((tangentSpaceCastModel 𝓘(ℝ) t).symm 1)
  have hvel : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t
      ((tangentSpaceCastModel 𝓘(ℝ) t).symm 1) =
      Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t :=
    Manifold.curveVelocity_apply.symm
  rw [hvel, ContinuousLinearEquiv.apply_symm_apply] at hcast
  have hfun : writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, ℂ) t (geodesicLine (1 : PSL(2, ℝ))) =
      fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I :=
    funext fun s ↦ by
      simpa [writtenInExtChartAt, extChartAt] using coe_geodesicLine_one s
  have hderiv : HasDerivAt (fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I)
      ((Real.exp t : ℂ) * Complex.I) t :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_exp t)).mul_const Complex.I
  have hchart : extChartAt 𝓘(ℝ) t t = t := rfl
  rw [hcast, hfun, hchart, hderiv.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), Complex.norm_I, mul_one]
  have him : (geodesicLine (1 : PSL(2, ℝ)) t).im = Real.exp t := by
    simp [geodesicLine_one_apply]
  rw [him, div_self (Real.exp_pos t).ne']

/-- Every geodesic line `geodesicLine g` has unit Poincaré speed everywhere. -/
theorem norm_curveVelocity_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    ‖Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine g) t‖ = 1 := by
  have hcomp : geodesicLine g = pslIsomHom g ∘ geodesicLine (1 : PSL(2, ℝ)) :=
    funext fun s ↦ by simp
  have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (pslIsomHom g) (geodesicLine (1 : PSL(2, ℝ)) t) := by
    have hfn : ⇑(pslIsomHom g) = (g • ·) := funext (pslIsomHom_apply g)
    rw [hfn]
    exact (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ω) g _).mdifferentiableAt (by simp)
  rw [hcomp, ← Manifold.curveVelocityWithin_univ,
    Manifold.curveVelocityWithin_map hd uniqueDiffWithinAt_univ
      ((contMDiff_geodesicLine (n := ω) 1 t).mdifferentiableAt (by simp)).mdifferentiableWithinAt,
    Manifold.curveVelocityWithin_univ, (pslIsomHom g).norm_mfderiv,
    norm_curveVelocity_geodesicLine_one]

/-- The Poincaré path length of `geodesicLine g` over `[a, b]` is `ENNReal.ofReal (b - a)`. -/
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  have h1 (t : ℝ) : ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t (1 : ℝ)‖ₑ = 1 := by
    rw [← ofReal_norm, ← Manifold.curveVelocity_apply, norm_curveVelocity_geodesicLine,
      ENNReal.ofReal_one]
  calc
    ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t (1 : ℝ)‖ₑ =
        ∫⁻ _ in Ioo a b, (1 : ℝ≥0∞) :=
      MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ h1 t
    _ = ENNReal.ofReal (b - a) := by
      simp only [MeasureTheory.setLIntegral_const, one_mul, Real.volume_Ioo]

/-- Along `geodesicLine g`, the Poincaré path length from `a` to `b` (`a ≤ b`) equals the
hyperbolic extended distance between the endpoints. -/
theorem pathELength_geodesicLine_eq_edist (g : PSL(2, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b =
      edist (geodesicLine g a) (geodesicLine g b) := by
  rw [pathELength_geodesicLine, edist_dist, dist_geodesicLine, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hab)]

end TauCeti.UpperHalfPlane

/-! ### Lower bound from logarithmic height and `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ` -/

/-- The logarithmic height `z ↦ Real.log z.im` is 1-Lipschitz with respect to the Poincaré
Riemannian extended distance on `ℍ`. -/
theorem UpperHalfPlane.edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  let f : ℍ → ℝ := fun u ↦ Real.log u.im
  have hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 f := by
    intro u
    have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 _root_.UpperHalfPlane.im u :=
      Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp u (contMDiffAt_extChartAt (I := 𝓘(ℝ, ℂ)))
    exact (Real.contDiffAt_log.mpr u.im_pos.ne').contMDiffAt.comp u him
  have hbound : ∀ (u : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) u),
      ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ) f u v‖ ≤ (1 : ℝ≥0) * ‖v‖ := by
    intro u v
    have hlocal : f ∘ (extChartAt 𝓘(ℝ, ℂ) u).symm =ᶠ[nhds (u : ℂ)]
        fun c : ℂ ↦ Real.log c.im := by
      have h1 : f ∘ (extChartAt 𝓘(ℝ, ℂ) u).symm =ᶠ[nhds (u : ℂ)] f ∘ ofComplex := by
        simpa [extChartAt] using TauCeti.UpperHalfPlane.comp_chartAt_symm_eventuallyEq f u
      filter_upwards [h1, isOpen_upperHalfPlaneSet.mem_nhds u.im_pos] with c hc hcim
      rw [hc, Function.comp_apply, ofComplex_apply_of_im_pos hcim]
      rfl
    have hfd : HasFDerivAt (fun c : ℂ ↦ Real.log c.im) ((u.im)⁻¹ • Complex.imCLM) (u : ℂ) :=
      (Real.hasDerivAt_log u.im_pos.ne').comp_hasFDerivAt (u : ℂ) Complex.imCLM.hasFDerivAt
    have hchart : extChartAt 𝓘(ℝ, ℂ) u u = (u : ℂ) := by simp
    rw [norm_tangentSpace_vectorSpace, NormedSpace.fromTangentSpace_apply,
      ← mvfderiv_apply_eq_mfderiv_apply, TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm,
      hchart, hlocal.fderiv_eq, hfd.fderiv, FunLike.coe_smul, Pi.smul_apply,
      Complex.imCLM_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos u.im_pos,
      ← div_eq_inv_mul, NNReal.coe_one, one_mul, UpperHalfPlane.norm_tangentSpace]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) u.im_pos.le
  simpa [f, IsRiemannianManifold.out (I := 𝓘(ℝ))] using
    TauCeti.Manifold.riemannianEDist_le_mul (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ)) hf one_ne_zero hbound z w

namespace TauCeti

/-- Mathlib's hyperbolic metric on the upper half-plane `ℍ` agrees with the Riemannian distance
of the Poincaré metric. -/
instance isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ where
  out z w := by
    obtain ⟨g, hz, hw⟩ := UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq z w
    apply le_antisymm
    · have hz' : (UpperHalfPlane.pslIsomHom g⁻¹ z).im = 1 := by
        rw [UpperHalfPlane.pslIsomHom_apply, ← hz, UpperHalfPlane.smul_geodesicLine,
          inv_mul_cancel, UpperHalfPlane.geodesicLine_one_apply]
        simp
      have hw' : (UpperHalfPlane.pslIsomHom g⁻¹ w).im = Real.exp (dist z w) := by
        rw [UpperHalfPlane.pslIsomHom_apply]
        conv_lhs => rw [← hw]
        rw [UpperHalfPlane.smul_geodesicLine, inv_mul_cancel, UpperHalfPlane.geodesicLine_one_apply]
        simp
      have hlow := _root_.UpperHalfPlane.edist_log_im_le_riemannianEDist
        (UpperHalfPlane.pslIsomHom g⁻¹ z) (UpperHalfPlane.pslIsomHom g⁻¹ w)
      rw [hz', hw', Real.log_one, Real.log_exp, edist_dist, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg dist_nonneg, ← edist_dist,
        (UpperHalfPlane.pslIsomHom g⁻¹).riemannianEDist_eq] at hlow
      exact hlow
    · have hup := Manifold.riemannianEDist_le_pathELength (I := 𝓘(ℝ, ℂ))
        ((UpperHalfPlane.contMDiff_geodesicLine (n := 1) g).contMDiffOn) hz hw dist_nonneg
      rwa [UpperHalfPlane.pathELength_geodesicLine_eq_edist g dist_nonneg, hz, hw] at hup

namespace UpperHalfPlane

/-- The intrinsic Riemannian metric space `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ` of the
Poincaré metric is complete. -/
theorem completeSpace_of_riemannianMetric :
    @CompleteSpace ℍ
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toUniformSpace :=
  (IsRiemannianManifold.completeSpace_ofRiemannianMetric_iff 𝓘(ℝ, ℂ) ℍ).mpr inferInstance

end UpperHalfPlane

end TauCeti

end
