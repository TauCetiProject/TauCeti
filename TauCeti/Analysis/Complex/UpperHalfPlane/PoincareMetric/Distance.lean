/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.PoincareMetric.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# The Riemannian distance of the Poincaré metric

This file identifies the Riemannian distance of the Poincaré metric on the upper half-plane `ℍ`
with Mathlib's hyperbolic distance `dist`
(`TauCeti.UpperHalfPlane.isRiemannianManifold_upperHalfPlane`), and deduces completeness of the
intrinsic Riemannian distance.

The proof follows the standard two-sided comparison (Katok, §1.2):

1. **Lower bound**: the map `z ↦ log (Im z)` has differential `v ↦ (Im v) / (Im z)`, whose
   absolute value is at most the Poincaré norm `‖v‖ = |v| / Im z`. By
   `TauCeti.Manifold.edist_le_mul_riemannianEDist`, `edist (log z.im) (log w.im)` is at most the
   Riemannian distance between `z` and `w`.
2. **Upper bound**: the vertical geodesic `geodesicLine 1 : t ↦ i exp t` is smooth with constant
   unit Poincaré speed, so its length on `[a, b]` is `ENNReal.ofReal (b - a)`. By invariance under
   `pslToIsom`, every geodesic line `geodesicLine g` has the same unit-speed length.
3. **General pairs**: two-point transitivity (`exists_geodesicLine_zero_eq_and_dist_eq`) gives
   `g : PSL(2, ℝ)` with `geodesicLine g 0 = z` and `geodesicLine g (dist z w) = w`. The geodesic
   segment bounds `riemannianEDist z w` above by `edist z w`, while moving back by `(pslToIsom g)⁻¹`
   to `(i, i exp (dist z w))` and applying the logarithmic lower bound bounds it below by
   `edist z w`.

Completeness of the intrinsic Riemannian metric `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ` then
follows directly from Mathlib's `ProperSpace ℍ` instance via `IsometryEquiv.completeSpace_iff`.

## Main results

* `UpperHalfPlane.edist_log_im_le_riemannianEDist`: `edist (log z.im) (log w.im)` bounds the
  Riemannian extended distance from below.
* `TauCeti.UpperHalfPlane.contMDiff_geodesicLine` and `pathELength_geodesicLine`: every geodesic
  line `geodesicLine g` is smooth and unit-speed for the Poincaré metric.
* `UpperHalfPlane.riemannianEDist_eq_edist`: the Poincaré Riemannian extended distance equals
  Mathlib's `edist` on `ℍ`.
* `TauCeti.UpperHalfPlane.isRiemannianManifold_upperHalfPlane`: `IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ`
  for Mathlib's `MetricSpace ℍ` and the Poincaré metric.
* `TauCeti.UpperHalfPlane.completeSpace_of_riemannianMetric`: completeness of the intrinsic
  Riemannian metric `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ`.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, 1992, §1.2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Chapter 3.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold MatrixGroups NNReal UpperHalfPlane

noncomputable section

namespace TauCeti.UpperHalfPlane

/-! ### The logarithmic lower bound -/

/-- The logarithmic height `z ↦ log (Im z)` is `1`-Lipschitz for the Poincaré Riemannian
distance. -/
theorem _root_.UpperHalfPlane.edist_log_im_le_riemannianEDist (z w : ℍ) :
    edist (Real.log z.im) (Real.log w.im) ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
  let f : ℍ → ℝ := fun τ ↦ Real.log τ.im
  have hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 f := fun τ ↦ by
    have him : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) 1 _root_.UpperHalfPlane.im τ :=
      (Complex.imCLM.contDiff.of_le le_top).contMDiff.contMDiffAt.comp τ contMDiffAt_extChartAt
    exact (Real.contDiffAt_log.mpr τ.im_pos.ne').contMDiffAt.comp τ him
  have hC : ∀ (τ : ℍ) (v : TangentSpace 𝓘(ℝ, ℂ) τ),
      ‖mvfderiv 𝓘(ℝ, ℂ) f τ v‖ₑ ≤ ((1 : ℝ≥0) : ℝ≥0∞) * ‖v‖ₑ := by
    intro τ v
    have hlocal : f ∘ (extChartAt 𝓘(ℝ, ℂ) τ).symm =ᶠ[nhds (τ : ℂ)]
        Real.log ∘ Complex.im := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos]
        with u hu
      have hinv : (((extChartAt 𝓘(ℝ, ℂ) τ).symm u : ℍ) : ℂ) = u := by
        simpa using (extChartAt 𝓘(ℝ, ℂ) τ).right_inv (by simpa using hu)
      simp only [Function.comp_apply, f, ← _root_.UpperHalfPlane.coe_im, hinv]
    have hderiv :=
      (Real.hasDerivAt_log τ.im_pos.ne').hasFDerivAt.comp (τ : ℂ) Complex.imCLM.hasFDerivAt
    have hmv : mvfderiv 𝓘(ℝ, ℂ) f τ v =
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) τ v).im / τ.im := by
      rw [TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm]
      have hchart : extChartAt 𝓘(ℝ, ℂ) τ τ = (τ : ℂ) := by simp
      rw [hchart, hlocal.fderiv_eq, hderiv.fderiv]
      simp [div_eq_mul_inv]
    rw [← ofReal_norm, ← ofReal_norm, ENNReal.coe_one, one_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hmv, _root_.UpperHalfPlane.norm_tangentSpace_eq, Real.norm_eq_abs, abs_div,
      abs_of_pos τ.im_pos]
    exact div_le_div_of_nonneg_right
      (Complex.abs_im_le_norm (tangentSpaceCastModel 𝓘(ℝ, ℂ) τ v)) τ.im_pos.le
  simpa using TauCeti.Manifold.edist_le_mul_riemannianEDist hf one_ne_zero hC z w

/-! ### Smoothness and length of geodesic lines -/

private theorem coe_geodesicLine_one (t : ℝ) :
    ((geodesicLine (1 : PSL(2, ℝ)) t : ℍ) : ℂ) = (Real.exp t : ℂ) * Complex.I := by
  rw [geodesicLine_one_apply, _root_.UpperHalfPlane.coe_mk]
  apply Complex.ext <;> simp [Complex.exp_ofReal_re]

private theorem contMDiff_geodesicLine_one :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ (geodesicLine (1 : PSL(2, ℝ))) := by
  refine ContMDiff.of_comp_isOpenEmbedding _root_.UpperHalfPlane.isOpenEmbedding_coe ?_
  have heq : (_root_.UpperHalfPlane.coe ∘ geodesicLine (1 : PSL(2, ℝ))) =
      fun t : ℝ ↦ (Real.exp t : ℂ) * Complex.I :=
    funext coe_geodesicLine_one
  rw [heq]
  exact ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul contDiff_const).contMDiff

/-- Every geodesic line `geodesicLine g` is smooth as a curve into the real manifold `ℍ`. -/
theorem contMDiff_geodesicLine (g : PSL(2, ℝ)) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) ∞ (geodesicLine g) := by
  have heq : geodesicLine g = (g • · : ℍ → ℍ) ∘ geodesicLine 1 := by
    funext t
    rw [Function.comp_apply, smul_geodesicLine, mul_one]
  rw [heq]
  exact (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := ∞) g).comp contMDiff_geodesicLine_one

private theorem tangentSpaceCastModel_mfderiv_geodesicLine_one (t : ℝ) :
    tangentSpaceCastModel 𝓘(ℝ, ℂ) (geodesicLine 1 t)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t 1) =
      (Real.exp t : ℂ) * Complex.I := by
  have hd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t :=
    contMDiff_geodesicLine_one.mdifferentiable (by simp) t
  rw [hd.tangentSpaceCastModel_mfderiv_apply]
  have hw : writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, ℂ) t (geodesicLine 1) =
      fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I := by
    funext s
    simpa [writtenInExtChartAt] using coe_geodesicLine_one s
  have hderiv : HasDerivAt (fun s : ℝ ↦ (Real.exp s : ℂ) * Complex.I)
      ((Real.exp t : ℂ) * Complex.I) t :=
    ((Real.hasDerivAt_exp t).ofReal_comp).mul_const Complex.I
  have hchart : extChartAt 𝓘(ℝ) t t = t := by simp
  have h1 : tangentSpaceCastModel 𝓘(ℝ) t (1 : TangentSpace 𝓘(ℝ) t) = 1 := rfl
  rw [hw, hchart, hderiv.hasFDerivAt.fderiv, h1]
  simp

private theorem enorm_mfderiv_geodesicLine_one (t : ℝ) :
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (geodesicLine 1) t 1‖ₑ = 1 := by
  rw [← ofReal_norm, _root_.UpperHalfPlane.norm_tangentSpace_eq,
    tangentSpaceCastModel_mfderiv_geodesicLine_one, geodesicLine_one_apply,
    _root_.UpperHalfPlane.mk_im, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos t).le, Complex.norm_I, mul_one,
    div_self (Real.exp_pos t).ne', ENNReal.ofReal_one]

/-- Every geodesic line `geodesicLine g` has unit speed for the Poincaré metric: its Riemannian
length on `[a, b]` is `ENNReal.ofReal (b - a)`. -/
@[simp]
theorem pathELength_geodesicLine (g : PSL(2, ℝ)) (a b : ℝ) :
    Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) a b = ENNReal.ofReal (b - a) := by
  have heq : geodesicLine g = pslToIsom g ∘ geodesicLine 1 := by
    funext t
    simp [smul_geodesicLine]
  rw [heq, (pslToIsom g).pathELength_comp, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  simp_rw [enorm_mfderiv_geodesicLine_one]
  rw [setLIntegral_const, Real.volume_Icc, one_mul]

/-! ### The distance comparison and completeness -/

/-- The Riemannian extended distance of the Poincaré metric on `ℍ` coincides with Mathlib's
hyperbolic extended distance `edist`. -/
@[simp]
theorem _root_.UpperHalfPlane.riemannianEDist_eq_edist (z w : ℍ) :
    Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w = edist z w := by
  obtain ⟨g, hz, hw⟩ := exists_geodesicLine_zero_eq_and_dist_eq z w
  have hd : 0 ≤ dist z w := dist_nonneg
  apply le_antisymm
  · calc Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w
        ≤ Manifold.pathELength 𝓘(ℝ, ℂ) (geodesicLine g) 0 (dist z w) :=
          Manifold.riemannianEDist_le_pathELength
            ((contMDiff_geodesicLine g).of_le (by simp)).contMDiffOn hz hw hd
      _ = ENNReal.ofReal (dist z w - 0) := pathELength_geodesicLine g 0 (dist z w)
      _ = edist z w := by rw [sub_zero, ← edist_dist]
  · have hz' : pslToIsom g (geodesicLine 1 0) = z := by
      simpa [smul_geodesicLine] using hz
    have hw' : pslToIsom g (geodesicLine 1 (dist z w)) = w := by
      simpa [smul_geodesicLine] using hw
    calc edist z w = ENNReal.ofReal (dist z w) := edist_dist z w
      _ = edist (Real.log (geodesicLine 1 0).im) (Real.log (geodesicLine 1 (dist z w)).im) := by
        rw [geodesicLine_one_apply, geodesicLine_one_apply, _root_.UpperHalfPlane.mk_im,
          _root_.UpperHalfPlane.mk_im, Real.log_exp, Real.log_exp, edist_dist, Real.dist_eq,
          zero_sub, abs_neg, abs_of_nonneg hd]
      _ ≤ Manifold.riemannianEDist 𝓘(ℝ, ℂ) (geodesicLine 1 0) (geodesicLine 1 (dist z w)) :=
        _root_.UpperHalfPlane.edist_log_im_le_riemannianEDist _ _
      _ = Manifold.riemannianEDist 𝓘(ℝ, ℂ) z w := by
        rw [← (pslToIsom g).riemannianEDist_eq, hz', hw']

/-- **The distance comparison.** Mathlib's hyperbolic distance on `ℍ` is the Riemannian distance
of the Poincaré metric `poincareRiemannianMetric`. -/
instance isRiemannianManifold_upperHalfPlane : IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ :=
  ⟨fun z w ↦ (_root_.UpperHalfPlane.riemannianEDist_eq_edist z w).symm⟩

/-- The intrinsic Riemannian metric `MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ` of the
Poincaré metric on the upper half-plane is complete. -/
theorem completeSpace_of_riemannianMetric :
    @CompleteSpace ℍ
      ((MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toPseudoMetricSpace.toUniformSpace) := by
  have hcomp : CompleteSpace ℍ := inferInstance
  have hm : (letI : MetricSpace ℍ := MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ
      IsRiemannianManifold 𝓘(ℝ, ℂ) ℍ) := inferInstance
  let e : @IsometryEquiv ℍ ℍ _
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toEMetricSpace.toPseudoEMetricSpace :=
    @IsometryEquiv.mk ℍ ℍ _
      (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toEMetricSpace.toPseudoEMetricSpace
      (Equiv.refl ℍ) fun z w ↦
        (hm.out z w).trans (_root_.UpperHalfPlane.riemannianEDist_eq_edist z w)
  exact (@IsometryEquiv.completeSpace_iff ℍ ℍ _
    (MetricSpace.ofRiemannianMetric 𝓘(ℝ, ℂ) ℍ).toEMetricSpace.toPseudoEMetricSpace e).mp hcomp

end TauCeti.UpperHalfPlane

end
