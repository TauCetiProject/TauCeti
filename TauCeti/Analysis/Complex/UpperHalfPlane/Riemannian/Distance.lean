/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Riemannian.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization

/-!
# The Riemannian distance and hyperbolic structure of the upper half-plane

This file identifies the Riemannian distance of the Poincaré metric
`TauCeti.UpperHalfPlane.poincareRiemannianMetric` with Mathlib's hyperbolic distance on `ℍ`,
deduces the metric isometry to the two-dimensional upper half-space model
`TauCeti.UpperHalfSpace ℝ`, proves completeness of the Riemannian distance from Mathlib's
`ProperSpace ℍ`, and packages `poincareRiemannianMetric` as a `TauCeti.HyperbolicMetric`.

## Proof of the distance comparison

1. **Lower bound.** The height logarithm `z ↦ Real.log z.im` is smooth on `ℍ` with differential
   `v ↦ v.im / z.im`. Since `|v.im| ≤ ‖v‖`, this differential has operator norm at most `1` for
   the Poincaré metric, so `TauCeti.Manifold.edist_le_mul_riemannianEDist` yields
   `edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w` for all
   `z, w : ℍ`.
2. **Upper bound along the imaginary axis.** The vertical geodesic `geodesicLine 1 : t ↦ i exp t`
   is smooth with velocity norm `1` everywhere in the Poincaré metric, so its length on `[a, b]`
   is `ENNReal.ofReal (b - a)` (for all `a, b : ℝ`). Together with the lower bound this shows that
   `riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0) (geodesicLine 1 d) = ENNReal.ofReal d` for `0 ≤ d`.
3. **General pairs.** By two-point transitivity (`exists_geodesicLine_zero_eq_and_dist_eq`), every
   pair `(z, w)` is carried from `(geodesicLine 1 0, geodesicLine 1 (dist z w))` by some
   `g : PSL(2, ℝ)`. Since `pslToIsom g` preserves `riemannianEDist`
   (`RiemannianIsometry.riemannianEDist_eq`), we obtain
   `Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = ENNReal.ofReal (dist z w) = edist z w`.

## Main definitions

* `TauCeti.UpperHalfPlane.upperHalfSpaceIsometryEquiv`: the metric isometry
  `ℍ ≃ᵢ UpperHalfSpace ℝ` from Mathlib's `dist` to the Riemannian distance
  `MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)`.
* `TauCeti.UpperHalfPlane.poincareHyperbolicMetric`: the Poincaré metric packaged as a complete
  constant-curvature `-1` `TauCeti.HyperbolicMetric` on `ℍ`.

## Main results

* `UpperHalfPlane.edist_log_im_le_riemannianEDist`:
  `|log (Im w) - log (Im z)| ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`.
* `TauCeti.UpperHalfPlane.pathELength_geodesicLine`: every `geodesicLine g` is unit-speed and
  minimizing for the Poincaré metric.
* `UpperHalfPlane.riemannianEDist_eq_edist` and `TauCeti.isRiemannianManifold_upperHalfPlane`:
  Mathlib's hyperbolic distance on `ℍ` equals the Riemannian extended distance of the Poincaré
  metric (`IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`).
* `TauCeti.UpperHalfPlane.riemannianEDist_upperHalfSpace_eq`: intrinsic identification of the
  Riemannian extended distance on `UpperHalfSpace ℝ` with `edist` on `ℍ`.
* `TauCeti.UpperHalfPlane.completeSpace_of_riemannianMetric`: metric completeness of
  `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ`.
* `TauCeti.UpperHalfPlane.isHyperbolic`: `ℍ` carries a complete hyperbolic metric.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §1.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Chapter 3.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold MatrixGroups NNReal UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

/-! ### Lower bound from `z ↦ log (Im z)` -/

/-- `z ↦ Real.log z.im` is smooth on the upper half-plane. -/
theorem contMDiff_log_im :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun z : ℍ ↦ Real.log z.im) := by
  intro z
  have hcoe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ _root_.UpperHalfPlane.coe z :=
    contMDiffAt_extChartAt
  have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ _root_.UpperHalfPlane.im z :=
    Complex.imCLM.contMDiff.contMDiffAt.comp z hcoe
  exact (Real.contDiffAt_log.mpr z.im_pos.ne').contMDiffAt.comp z him

/-- In tangent coordinates, the differential of `z ↦ Real.log z.im` is `v ↦ v.im / z.im`. -/
theorem _root_.UpperHalfPlane.mvfderiv_log_im (z : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) z) :
    mvfderiv 𝓘(ℝ, ℂ) (fun w : ℍ ↦ Real.log w.im) z v =
      (tangentSpaceCastModel 𝓘(ℝ, ℂ) z v).im / z.im := by
  have hlog : HasFDerivAt (fun w : ℂ ↦ Real.log w.im) (z.im⁻¹ • Complex.imCLM) (z : ℂ) := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Real.hasDerivAt_log z.im_pos.ne').comp_hasFDerivAt (z : ℂ) Complex.imCLM.hasFDerivAt
  have hlocal :
      (fun w : ℍ ↦ Real.log w.im) ∘ (extChartAt 𝓘(ℝ, ℂ) z).symm =ᶠ[nhds (z : ℂ)]
        fun w : ℂ ↦ Real.log w.im := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos]
      with w hw
    have hinv : (extChartAt 𝓘(ℝ, ℂ) z).symm w = (⟨w, hw⟩ : ℍ) := by
      apply _root_.UpperHalfPlane.ext
      simpa using (extChartAt 𝓘(ℝ, ℂ) z).right_inv (by simpa using hw)
    simp only [Function.comp_apply, hinv]
    rfl
  rw [TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm]
  have hz : extChartAt 𝓘(ℝ, ℂ) z z = (z : ℂ) := by simp
  rw [hz, hlocal.fderiv_eq, hlog.fderiv]
  simp [div_eq_inv_mul]

/-- The logarithmic height difference is a lower bound on the Poincaré Riemannian extended
distance: `edist (Real.log z.im) (Real.log w.im) ≤ riemannianEDist 𝓘(ℝ, ℂ) z w`. -/
theorem _root_.UpperHalfPlane.edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  have h := TauCeti.Manifold.edist_le_mul_riemannianEDist
    (f := fun τ : ℍ ↦ Real.log τ.im) (contMDiff_log_im.of_le (by simp))
    (C := 1) one_ne_zero (fun τ v ↦ ?_) z w
  · simpa using h
  · rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [_root_.UpperHalfPlane.mvfderiv_log_im, _root_.UpperHalfPlane.norm_tangentSpace_eq,
      Real.norm_eq_abs, abs_div, abs_of_pos τ.im_pos]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) τ.im_pos.le

/-! ### Speed and length of geodesic lines -/

/-- The upward unit-speed imaginary axis `geodesicLine 1` is smooth. -/
private theorem contMDiff_geodesicLine_one :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ (geodesicLine (1 : PSL(2, ℝ))) := by
  apply ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe
  have hfun : (_root_.UpperHalfPlane.coe ∘ geodesicLine (1 : PSL(2, ℝ))) =
      fun t : ℝ ↦ Real.exp t • Complex.I := by
    funext t
    rw [Function.comp_apply, geodesicLine_one_apply, _root_.UpperHalfPlane.coe_mk,
      Complex.real_smul]
    apply Complex.ext <;> simp [Complex.exp_ofReal_re]
  rw [hfun]
  exact (Real.contDiff_exp.smul contDiff_const).contMDiff

/-- Every geodesic line `geodesicLine g` is smooth as a curve into the real manifold `ℍ`. -/
theorem contMDiff_geodesicLine (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ (geodesicLine g) := by
  have hfun : geodesicLine g = (g • ·) ∘ geodesicLine (1 : PSL(2, ℝ)) := by
    funext t
    simp
  rw [hfun]
  exact (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) g).comp contMDiff_geodesicLine_one

/-- The velocity of `geodesicLine 1` in model coordinates is `(exp t) • I`. -/
theorem tangentSpaceCastModel_mfderiv_geodesicLine_one (t : ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ)) t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t 1) =
      Real.exp t • Complex.I := by
  rw [(contMDiff_geodesicLine_one.mdifferentiableAt (by simp)).tangentSpaceCastModel_mfderiv_apply]
  have hfun :
      writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, ℂ) t (geodesicLine (1 : PSL(2, ℝ))) =
        fun s : ℝ ↦ Real.exp s • Complex.I := by
    funext s
    have hchart : ∀ τ : ℍ, extChartAt 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ)) t) τ = (τ : ℂ) :=
      fun _ ↦ by simp
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq, hchart]
    rw [geodesicLine_one_apply, _root_.UpperHalfPlane.coe_mk, Complex.real_smul]
    apply Complex.ext <;> simp [Complex.exp_ofReal_re]
  have hderiv : HasDerivAt (fun s : ℝ ↦ Real.exp s • Complex.I)
      (Real.exp t • Complex.I) t :=
    (Real.hasDerivAt_exp t).smul_const Complex.I
  have hcast : tangentSpaceCastModel 𝓘(ℝ, ℝ) t 1 = (1 : ℝ) := rfl
  rw [hfun, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq, hderiv.hasFDerivAt.fderiv,
    hcast]
  simp

/-- The vertical geodesic `geodesicLine 1` has unit speed in the Poincaré metric. -/
private theorem norm_mfderiv_geodesicLine_one (t : ℝ) :
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) t 1‖ = 1 := by
  rw [_root_.UpperHalfPlane.norm_tangentSpace_eq, tangentSpaceCastModel_mfderiv_geodesicLine_one]
  simp [geodesicLine_one_apply]

/-- Every geodesic line `geodesicLine g` has unit speed in the Poincaré metric. -/
@[simp]
theorem norm_mfderiv_geodesicLine (g : PSL(2, ℝ)) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t 1‖ = 1 := by
  have hfun : geodesicLine g = (pslToIsom g : ℍ → ℍ) ∘ geodesicLine (1 : PSL(2, ℝ)) := by
    funext s
    simp
  rw [hfun, mfderiv_comp_apply t ((pslToIsom g).mdifferentiableAt _)
    (contMDiff_geodesicLine_one.mdifferentiableAt (by simp))]
  rw [(pslToIsom g).norm_mfderiv, norm_mfderiv_geodesicLine_one]

/-- The Poincaré length of `geodesicLine g` on `[a, b]` is `ENNReal.ofReal (b - a)`. -/
@[simp]
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  have hconst : ∀ t ∈ Ioo a b,
      ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine g) t 1‖ₑ = 1 := fun t _ ↦ by
    rw [← ofReal_norm, norm_mfderiv_geodesicLine, ENNReal.ofReal_one]
  rw [setLIntegral_congr_fun measurableSet_Ioo hconst, setLIntegral_one, Real.volume_Ioo]

/-! ### The distance comparison (`IsRiemannianManifold`) -/

private theorem riemannianEDist_geodesicLine_one_zero {d : ℝ} (hd : 0 ≤ d) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ)) 0)
        (geodesicLine (1 : PSL(2, ℝ)) d) =
      ENNReal.ofReal d := by
  apply le_antisymm
  · calc Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ)) 0)
          (geodesicLine (1 : PSL(2, ℝ)) d)
        ≤ Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine (1 : PSL(2, ℝ))) 0 d :=
          Manifold.riemannianEDist_le_pathELength
            ((contMDiff_geodesicLine_one.of_le (by simp)).contMDiffOn) rfl rfl hd
      _ = ENNReal.ofReal (d - 0) := pathELength_geodesicLine 1 0 d
      _ = ENNReal.ofReal d := by rw [sub_zero]
  · have hlow := _root_.UpperHalfPlane.edist_log_im_le_riemannianEDist
      (geodesicLine (1 : PSL(2, ℝ)) 0) (geodesicLine (1 : PSL(2, ℝ)) d)
    simpa [geodesicLine_one_apply, edist_dist, Real.dist_eq, abs_of_nonneg hd] using hlow

/-- **The distance comparison.** The Riemannian extended distance of the Poincaré metric on `ℍ`
equals Mathlib's hyperbolic extended distance `edist`. -/
@[simp]
theorem _root_.UpperHalfPlane.riemannianEDist_eq_edist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = edist z w := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  have hz' : pslToIsom g (geodesicLine (1 : PSL(2, ℝ)) 0) = z := by simpa using hz
  have hw' : pslToIsom g (geodesicLine (1 : PSL(2, ℝ)) (dist z w)) = w := by simpa using hw
  calc Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w
      = Manifold.riemannianEDist 𝓘(ℝ, ℂ)
          (pslToIsom g (geodesicLine (1 : PSL(2, ℝ)) 0))
          (pslToIsom g (geodesicLine (1 : PSL(2, ℝ)) (dist z w))) := by rw [hz', hw']
    _ = Manifold.riemannianEDist 𝓘(ℝ, ℂ)
          (geodesicLine (1 : PSL(2, ℝ)) 0)
          (geodesicLine (1 : PSL(2, ℝ)) (dist z w)) := (pslToIsom g).riemannianEDist_eq _ _
    _ = ENNReal.ofReal (dist z w) := riemannianEDist_geodesicLine_one_zero dist_nonneg
    _ = edist z w := (edist_dist z w).symm

/-- Mathlib's metric space `ℍ` satisfies `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ` for the Poincaré metric:
for all `z, w : ℍ`, `edist z w` is the infimum of the Poincaré lengths of `C¹` paths from `z` to
`w`. -/
instance _root_.TauCeti.isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ :=
  ⟨fun z w ↦ (_root_.UpperHalfPlane.riemannianEDist_eq_edist z w).symm⟩

/-- Every geodesic line `geodesicLine g` realizes the hyperbolic distance between any two of its
points. -/
theorem pathELength_geodesicLine_eq_edist (g : PSL(2, ℝ)) {a b : ℝ} (hab : a ≤ b) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b =
      edist (geodesicLine g a) (geodesicLine g b) := by
  rw [pathELength_geodesicLine g a b, edist_dist, dist_geodesicLine, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr hab)]

/-! ### Comparison metric isometry with `UpperHalfSpace ℝ` -/

/-- Intrinsic distance formula on `UpperHalfSpace ℝ`: its Riemannian extended distance is Mathlib's
hyperbolic extended distance pulled back along `upperHalfSpaceIsometry.symm`. -/
theorem riemannianEDist_upperHalfSpace_eq (p q : UpperHalfSpace ℝ) :
    Manifold.riemannianEDist 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) p q =
      edist (upperHalfSpaceIsometry.symm p) (upperHalfSpaceIsometry.symm q) := by
  rw [← _root_.UpperHalfPlane.riemannianEDist_eq_edist,
    ← upperHalfSpaceIsometry.symm.riemannianEDist_eq]

/-- The comparison isometry `ℍ ≃ᵢ UpperHalfSpace ℝ` from Mathlib's hyperbolic distance on `ℍ` to
the Riemannian distance `MetricSpace.ofRiemannianMetric` on `UpperHalfSpace ℝ`. -/
def upperHalfSpaceIsometryEquiv :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    ℍ ≃ᵢ UpperHalfSpace ℝ :=
  letI : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  (upperHalfSpaceIsometry : ℍ ≃ᵢ UpperHalfSpace ℝ)

/-- `upperHalfSpaceIsometryEquiv` has the same underlying map as `upperHalfSpaceIsometry`. -/
@[simp]
theorem _root_.UpperHalfPlane.upperHalfSpaceIsometryEquiv_apply (z : ℍ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv z = upperHalfSpaceIsometry z := by
  rfl

/-- The inverse of `upperHalfSpaceIsometryEquiv` is `upperHalfSpaceIsometry.symm`. -/
@[simp]
theorem upperHalfSpaceIsometryEquiv_symm_apply (p : UpperHalfSpace ℝ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    upperHalfSpaceIsometryEquiv.symm p = upperHalfSpaceIsometry.symm p := by
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  exact upperHalfSpaceIsometryEquiv.injective (by simp)

/-- The distance of `MetricSpace.ofRiemannianMetric` on `UpperHalfSpace ℝ` between the images of
`z` and `w` equals Mathlib's `dist z w`. -/
@[simp]
theorem _root_.UpperHalfPlane.dist_upperHalfSpace_ofRiemannianMetric (z w : ℍ) :
    letI : MetricSpace (UpperHalfSpace ℝ) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
    dist (upperHalfSpaceIsometry z) (upperHalfSpaceIsometry w) = dist z w := by
  let _ : MetricSpace (UpperHalfSpace ℝ) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (ℝ × ℝ)) (UpperHalfSpace ℝ)
  exact upperHalfSpaceIsometryEquiv.dist_eq z w

/-! ### Completeness and `HyperbolicMetric` structure -/

/-- The Riemannian distance of the Poincaré metric on `ℍ` is metrically complete, because it agrees
with Mathlib's hyperbolic distance, which is complete by `ProperSpace ℍ`.

The explicit `UniformSpace` argument matches `TauCeti.HyperbolicMetric.complete`. -/
theorem completeSpace_of_riemannianMetric :
    @CompleteSpace ℍ
      ((MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toUniformSpace) :=
  (@IsometryEquiv.completeSpace_iff ℍ ℍ
    (inferInstance : MetricSpace ℍ).toPseudoMetricSpace.toPseudoEMetricSpace
    (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toPseudoEMetricSpace
    (@IsometryEquiv.mk ℍ ℍ
      (inferInstance : MetricSpace ℍ).toPseudoMetricSpace.toPseudoEMetricSpace
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toPseudoEMetricSpace
      (Equiv.refl ℍ) (fun z w ↦ _root_.UpperHalfPlane.riemannianEDist_eq_edist z w))).mp
    inferInstance

/-- The Poincaré metric on `ℍ` has the constant-curvature tensor with parameter `-1`. -/
theorem poincareRiemannianMetric_isConstantCurvatureTensor :
    poincareRiemannianMetric.IsConstantCurvatureTensor (-1) := by
  rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
  have h := (CovariantDerivative.hasConstantSectionalCurvature_iff_isConstantCurvatureTensor
    (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, ℂ) ℍ)
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection 𝓘(ℝ, ℂ))
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, ℂ)) (-1)).mp
    hasConstantSectionalCurvature
  rwa [RiemannianMetric.isConstantCurvatureTensor_iff] at h

/-- The Poincaré metric on `ℍ`, packaged with its completeness and constant-curvature `-1` tensor
as a `TauCeti.HyperbolicMetric`. -/
def poincareHyperbolicMetric : HyperbolicMetric (I := 𝓘(ℝ, ℂ)) (M := ℍ) where
  metric := poincareRiemannianMetric
  complete := completeSpace_of_riemannianMetric
  curvature := poincareRiemannianMetric_isConstantCurvatureTensor

/-- Forgetting completeness and curvature recovers `poincareRiemannianMetric`. -/
@[simp]
theorem poincareHyperbolicMetric_metric :
    poincareHyperbolicMetric.metric = poincareRiemannianMetric := by
  rfl

/-- The upper half-plane carries a complete hyperbolic metric. -/
theorem isHyperbolic : IsHyperbolic (I := 𝓘(ℝ, ℂ)) (M := ℍ) :=
  TauCeti.isHyperbolic_iff.mpr ⟨poincareHyperbolicMetric⟩

end TauCeti.UpperHalfPlane

end
