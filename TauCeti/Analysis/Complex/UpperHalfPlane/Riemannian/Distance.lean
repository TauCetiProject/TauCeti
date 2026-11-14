/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The Riemannian distance of the Poincaré metric on the upper half-plane

Mathlib equips the upper half-plane `ℍ` with the hyperbolic distance
`dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))`. This file proves
`TauCeti.UpperHalfPlane.isRiemannianManifold_upperHalfPlane`: `ℍ` satisfies
`IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ` for the Poincaré Riemannian metric
`TauCeti.UpperHalfPlane.poincareRiemannianMetric`, so the infimum of Poincaré lengths of `C¹` curves
joining `z` and `w` equals Mathlib's `edist z w`.

The geometric proof follows Katok, §1.2:

1. **Logarithmic height bound (`|d log y| ≤ ds`).** The smooth map `z ↦ Real.log z.im` from `ℍ` to
   `ℝ` has differential `v ↦ (Im v) / z.im` in model coordinates, whose Euclidean norm on `ℝ` is
   `|Im v| / z.im ≤ ‖v‖ / z.im = ‖v‖_ℍ`. Hence it neither increases `C¹` curve lengths nor
   increases `Manifold.riemannianEDist`.
2. **Imaginary axis (`geodesicLine 1`).** The upward vertical ray `t ↦ i exp t` has unit Poincaré
   speed at every parameter, so its `C¹` length on `[a, b]` is `b - a` and the Riemannian distance
   between `geodesicLine 1 s` and `geodesicLine 1 t` equals `edist s t` by combining the upper
   bound with step 1.
3. **`PSL(2, ℝ)` two-point transitivity.** Every pair `z, w : ℍ` lies on `geodesicLine g` at
   parameters `0` and `dist z w` (`TauCeti.UpperHalfPlane.exists_geodesicLine_zero_eq_and_dist_eq`).
   Because `pslIsomHom g` is a Riemannian isometry, `Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w` equals
   `Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0) (geodesicLine 1 (dist z w)) = edist z w`.

Identifying `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ` with Mathlib's `MetricSpace ℍ` then yields
metric completeness of the Poincaré Riemannian distance directly from Mathlib's `ProperSpace ℍ`.

## Main results

* `UpperHalfPlane.edist_log_im_le_riemannianEDist` and
  `UpperHalfPlane.edist_log_im_le_pathELength`: the logarithmic-height lower bound on Riemannian
  extended distance and `C¹` path length.
* `TauCeti.UpperHalfPlane.pathELength_geodesicLine` and
  `TauCeti.UpperHalfPlane.riemannianEDist_geodesicLine`: every `PSL(2, ℝ)` geodesic line has unit
  Poincaré speed and realises the Riemannian distance between its points.
* `UpperHalfPlane.riemannianEDist_eq_edist` and
  `TauCeti.UpperHalfPlane.isRiemannianManifold_upperHalfPlane`: `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`.
* `UpperHalfPlane.exists_pathELength_eq_edist`: every pair of points in `ℍ` is joined by a
  smooth curve on `[0, 1]` whose Poincaré length equals `edist z w`.
* `TauCeti.UpperHalfPlane.metricSpace_ofRiemannianMetric_eq` and
  `TauCeti.UpperHalfPlane.completeSpace_of_riemannianMetric`: completeness of the Poincaré
  Riemannian distance.

## References

* Svetlana Katok, *Fuchsian Groups*, §1.2.
* Alan Beardon, *The Geometry of Discrete Groups*, §7.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3.
-/

public section

open Bundle Manifold MeasureTheory Set Topology
open scoped ContDiff ENNReal Manifold MatrixGroups NNReal UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- The logarithmic height `z ↦ Real.log z.im` is smooth on the upper half-plane. -/
theorem contMDiff_log_im {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n fun z : ℍ ↦ Real.log z.im := by
  intro z
  have hcoe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n UpperHalfPlane.coe z := contMDiffAt_extChartAt
  have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n UpperHalfPlane.im z :=
    Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp z hcoe
  exact (Real.contDiffAt_log.mpr z.im_ne_zero).contMDiffAt.comp z him

/-- In model coordinates, the differential of `z ↦ Real.log z.im` at `z` sends `v` to
`(Im v) / z.im`. -/
theorem tangentSpaceCastModel_mfderiv_log_im (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    tangentSpaceCastModel 𝓘(ℝ, ℝ) (Real.log z.im)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : ℍ ↦ Real.log w.im) z v) =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v).im / z.im := by
  rw [(contMDiff_log_im (n := ∞).mdifferentiableAt (by simp)).tangentSpaceCastModel_mfderiv_apply]
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) z (fun w : ℍ ↦ Real.log w.im)
      =ᶠ[𝓝 (z : ℂ)] Real.log ∘ Complex.im := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos]
      with w hw
    have hsymm : (extChartAt 𝓘(ℝ, ℂ) z).symm w = ⟨w, hw⟩ := by
      apply coe_injective
      exact (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
    have hchartR (x : ℝ) : extChartAt 𝓘(ℝ, ℝ) (Real.log z.im) x = x := by simp
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, hsymm, hchartR]
    simp
  have hchart : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hchart, hlocal.fderiv_eq,
    ((Real.hasDerivAt_log z.im_ne_zero).comp_hasFDerivAt (z : ℂ) Complex.imCLM.hasFDerivAt).fderiv]
  simp [div_eq_inv_mul]

/-- The differential of `z ↦ Real.log z.im` has operator norm at most `1` with respect to the
Poincaré metric on `ℍ` and the Euclidean metric on `ℝ`: `|Im v| / z.im ≤ ‖v‖ / z.im`. -/
theorem norm_mfderiv_log_im_le (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : ℍ ↦ Real.log w.im) z v‖ ≤ ‖v‖ := by
  have hnormR (x : ℝ) (u : TangentSpace 𝓘(ℝ, ℝ) x) :
      ‖u‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℝ) x u‖ := by
    rw [norm_tangentSpace_vectorSpace]
    rfl
  rw [hnormR, tangentSpaceCastModel_mfderiv_log_im, norm_tangentSpace, Real.norm_eq_abs,
    abs_div, abs_of_pos z.im_pos]
  exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) z.im_pos.le

/-- **Logarithmic height bound on Riemannian extended distance.** For any `z, w : ℍ`, the distance
between `Real.log z.im` and `Real.log w.im` is at most the Poincaré Riemannian extended distance
`Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w`. -/
theorem edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ))]
  simpa using TauCeti.Manifold.riemannianEDist_le_mul (f := fun p : ℍ ↦ Real.log p.im)
    (contMDiff_log_im (n := 1)) (C := 1) one_ne_zero
    (fun x u ↦ by simpa using norm_mfderiv_log_im_le x u) z w

/-- **Logarithmic height bound on curve length.** Every `C¹` curve `γ` in `ℍ` on `[a, b]` (`a ≤ b`)
has Poincaré length at least `edist (Real.log (γ a).im) (Real.log (γ b).im)`. -/
theorem edist_log_im_le_pathELength {γ : ℝ → ℍ} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ (Icc a b)) (hab : a ≤ b) :
    edist (Real.log (γ a).im) (Real.log (γ b).im) ≤ Manifold.pathELength 𝓘(ℝ, ℂ) γ a b := by
  refine (TauCeti.IsRiemannianManifold.edist_le_pathELength (I := 𝓘(ℝ, ℝ))
    ((contMDiff_log_im (n := 1)).comp_contMDiffOn hγ) hab).trans ?_
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo, Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht ↦ ?_
  have hdiff := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hcomp := DFunLike.congr_fun
    (mfderiv_comp t ((contMDiff_log_im (n := 1) (γ t)).mdifferentiableAt one_ne_zero) hdiff)
    (1 : ℝ)
  calc
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((fun z : ℍ ↦ Real.log z.im) ∘ γ) t (1 : ℝ)‖ₑ
      = ENNReal.ofReal
          ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ((fun z : ℍ ↦ Real.log z.im) ∘ γ) t (1 : ℝ)‖ :=
        (ofReal_norm _).symm
    _ = ENNReal.ofReal
          ‖mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℍ ↦ Real.log z.im) (γ t)
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ))‖ :=
        congrArg (fun v ↦ ENNReal.ofReal ‖v‖) hcomp
    _ ≤ ENNReal.ofReal ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ)‖ :=
        ENNReal.ofReal_le_ofReal (norm_mfderiv_log_im_le (γ t) _)
    _ = ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ)‖ₑ := ofReal_norm _

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

/-- Every `PSL(2, ℝ)` geodesic line `t ↦ g • mk ⟨0, exp t⟩ _` is smooth as a curve in `ℍ`. -/
theorem contMDiff_geodesicLine {n : WithTop ℕ∞} (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine g) := by
  have hone : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) n (geodesicLine 1) := by
    apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
    let ι : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
    have hcomp : UpperHalfPlane.coe ∘ geodesicLine 1 = ι ∘ Real.exp := by
      funext t
      rw [Function.comp_apply, geodesicLine_one_apply, UpperHalfPlane.coe_mk]
      apply Complex.ext <;> simp [ι, Complex.exp_ofReal_re]
    rw [hcomp]
    exact (ι.contDiff.comp Real.contDiff_exp).contMDiff
  have hsmul : geodesicLine g = (g • ·) ∘ geodesicLine 1 := by
    funext t
    simp [smul_geodesicLine]
  rw [hsmul]
  exact (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g).comp hone

/-- In model coordinates, the differential of the vertical geodesic line `geodesicLine 1` at `t` on
a tangent vector `u` is `(u * exp t) * Complex.I`. -/
theorem tangentSpaceCastModel_mfderiv_geodesicLine_one (t : ℝ)
    (u : TangentSpace 𝓘(ℝ, ℝ) t) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (geodesicLine 1 t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t u) =
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t u * Real.exp t : ℝ) : ℂ) * Complex.I := by
  rw [((contMDiff_geodesicLine (n := ∞) 1).mdifferentiableAt
    (by simp)).tangentSpaceCastModel_mfderiv_apply]
  let ι : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I
  have hlocal : writtenInExtChartAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) t (geodesicLine 1) = ι ∘ Real.exp := by
    funext s
    have hchart1 (x : ℍ) : extChartAt 𝓘(ℝ, ℂ) (geodesicLine 1 t) x = (x : ℂ) := by simp
    have hchartR : (extChartAt 𝓘(ℝ, ℝ) t).symm s = s := by simp
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, hchartR, hchart1,
      geodesicLine_one_apply, UpperHalfPlane.coe_mk]
    apply Complex.ext <;> simp [ι, Complex.exp_ofReal_re]
  have hchart : extChartAt 𝓘(ℝ, ℝ) t t = t := by simp
  have hderiv : HasDerivAt (ι ∘ Real.exp) (ι (Real.exp t)) t :=
    ι.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_exp t)
  rw [hchart, hlocal, hderiv.hasFDerivAt.fderiv]
  simp [ι, Complex.real_smul, mul_assoc]

/-- Every `PSL(2, ℝ)` geodesic line has unit Poincaré speed: its differential is an isometry on
every tangent space. -/
theorem norm_mfderiv_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) (u : TangentSpace 𝓘(ℝ, ℝ) t) :
    ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t u‖ = ‖u‖ := by
  have hone : ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t u‖ = ‖u‖ := by
    have hnormR : ‖u‖ = ‖tangentSpaceCastModel 𝓘(ℝ, ℝ) t u‖ := by
      rw [norm_tangentSpace_vectorSpace]
      rfl
    have him : (geodesicLine 1 t).im = Real.exp t := by simp [geodesicLine_one_apply]
    rw [norm_tangentSpace, tangentSpaceCastModel_mfderiv_geodesicLine_one, him, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos t), mul_div_cancel_right₀ _ (Real.exp_pos t).ne',
      ← Real.norm_eq_abs, hnormR]
  have hsmul : geodesicLine g = (pslIsomHom g : ℍ → ℍ) ∘ geodesicLine 1 := by
    funext s
    simp [smul_geodesicLine]
  rw [hsmul, mfderiv_comp t ((pslIsomHom g).mdifferentiableAt _)
    ((contMDiff_geodesicLine (n := ∞) 1).mdifferentiableAt (by simp)),
    ContinuousLinearMap.comp_apply, (pslIsomHom g).norm_mfderiv, hone]

/-- Every `PSL(2, ℝ)` geodesic line has unit Poincaré curve velocity at every parameter `t`. -/
@[simp]
theorem norm_curveVelocity_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    ‖TauCeti.Manifold.curveVelocity 𝓘(ℝ, ℂ) (geodesicLine g) t‖ = 1 := by
  rw [TauCeti.Manifold.curveVelocity_apply]
  exact (norm_mfderiv_geodesicLine g t (1 : ℝ)).trans (norm_tangentSpace_vectorSpace.trans norm_one)

/-- The Poincaré length of `geodesicLine g` over `[a, b]` is `ENNReal.ofReal (b - a)`. -/
@[simp]
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) := by
  calc
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b
      = ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t (1 : ℝ)‖ₑ :=
        Manifold.pathELength_eq_lintegral_mfderiv_Ioo
    _ = ∫⁻ _ in Ioo a b, 1 := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
        rw [← TauCeti.Manifold.curveVelocity_apply, ← ofReal_norm,
          norm_curveVelocity_geodesicLine, ENNReal.ofReal_one]
    _ = ENNReal.ofReal (b - a) := by
        rw [setLIntegral_one, Real.volume_Ioo]

/-- Along any `PSL(2, ℝ)` geodesic line, the Poincaré Riemannian extended distance between
parameters `s` and `t` equals `edist s t`. -/
@[simp]
theorem riemannianEDist_geodesicLine (g : PSL(2, ℝ)) (s t : ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine g s) (geodesicLine g t) = edist s t := by
  have hsmul (u : ℝ) : geodesicLine g u = pslIsomHom g (geodesicLine 1 u) := by
    simp [smul_geodesicLine]
  rw [hsmul s, hsmul t, (pslIsomHom g).riemannianEDist_eq]
  apply le_antisymm
  · rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ))]
    simpa using TauCeti.Manifold.riemannianEDist_le_mul (f := geodesicLine 1)
      (contMDiff_geodesicLine (n := 1) 1) (C := 1) one_ne_zero
      (fun x u ↦ by simp [norm_mfderiv_geodesicLine]) s t
  · have hlog (u : ℝ) : Real.log (geodesicLine 1 u).im = u := by
      simp [geodesicLine_one_apply]
    simpa only [hlog] using edist_log_im_le_riemannianEDist (geodesicLine 1 s) (geodesicLine 1 t)

/-- **The distance comparison (`riemannianEDist` form).** The Riemannian extended distance of the
Poincaré metric on `ℍ` agrees with Mathlib's `edist` for all `z, w : ℍ`. -/
theorem _root_.UpperHalfPlane.riemannianEDist_eq_edist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = edist z w := by
  obtain ⟨g, rfl, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  conv_lhs => rw [← hw]
  rw [riemannianEDist_geodesicLine, edist_dist, edist_dist, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg dist_nonneg]

/-- **The distance comparison.** Mathlib's hyperbolic metric space `ℍ` satisfies
`IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ` for the Poincaré Riemannian metric
`TauCeti.UpperHalfPlane.poincareRiemannianMetric`. -/
instance isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ :=
  ⟨fun z w ↦ (_root_.UpperHalfPlane.riemannianEDist_eq_edist z w).symm⟩

/-- Every pair of points `z, w : ℍ` is joined by an explicit `C¹` curve on `[0, 1]` whose Poincaré
length equals `edist z w`. -/
theorem _root_.UpperHalfPlane.exists_pathELength_eq_edist (z w : ℍ) :
    ∃ γ : ℝ → ℍ, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ (Icc 0 1) ∧ γ 0 = z ∧ γ 1 = w ∧
      Manifold.pathELength 𝓘(ℝ, ℂ) γ 0 1 = edist z w := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  let φ : ℝ → ℝ := fun s ↦ s * dist z w
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 (geodesicLine g ∘ φ) (Icc 0 1) :=
    ((contMDiff_geodesicLine (n := 1) g).comp
      (contDiff_id.mul contDiff_const).contMDiff).contMDiffOn
  refine ⟨geodesicLine g ∘ φ, hγ, by simpa [φ] using hz, by simpa [φ] using hw, ?_⟩
  calc
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g ∘ φ) 0 1
      = ∫⁻ t in Ioo 0 1,
          ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (geodesicLine g ∘ φ) t (1 : ℝ)‖ₑ :=
        Manifold.pathELength_eq_lintegral_mfderiv_Ioo
    _ = ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (dist z w) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
        have hφ' : HasDerivAt φ (dist z w) t := by
          simpa [φ] using (hasDerivAt_id t).mul_const (dist z w)
        rw [← TauCeti.Manifold.curveVelocity_apply,
          TauCeti.Manifold.curveVelocity_comp hφ'
            ((contMDiff_geodesicLine (n := ∞) g).mdifferentiableAt (by simp)),
          ← ofReal_norm, norm_smul, norm_curveVelocity_geodesicLine]
        simp [abs_of_nonneg dist_nonneg]
    _ = edist z w := by
        rw [setLIntegral_const, Real.volume_Ioo, edist_dist]
        simp

/-- `TauCeti.MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ` coincides as a `MetricSpace` structure with
Mathlib's installed hyperbolic metric space on `ℍ`. -/
theorem metricSpace_ofRiemannianMetric_eq :
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ = (inferInstance : MetricSpace ℍ) := by
  ext z w
  -- Unfold `dist` on `MetricSpace.ofRiemannianMetric` to `(riemannianEDist 𝓘(ℝ, ℂ) z w).toReal`.
  change (Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w).toReal = dist z w
  rw [_root_.UpperHalfPlane.riemannianEDist_eq_edist, dist_edist]

/-- **Completeness of the Poincaré metric.** `ℍ` equipped with the Riemannian distance of the
Poincaré metric is metrically complete. -/
theorem completeSpace_of_riemannianMetric :
    @CompleteSpace ℍ
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toUniformSpace := by
  rw [metricSpace_ofRiemannianMetric_eq]
  infer_instance

end TauCeti.UpperHalfPlane

namespace TauCeti

export UpperHalfPlane (isRiemannianManifold_upperHalfPlane)

end TauCeti

end
