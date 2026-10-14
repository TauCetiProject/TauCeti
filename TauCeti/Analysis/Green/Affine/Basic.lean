/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.Complex.Coordinates
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Affine changes of planar coordinates

The pullback of `P dx + Q dy` along a continuous real affine map transports circulation along
absolutely continuous curves. Its curl scales by the signed determinant of the linear part,
including for singular maps. For affine equivalences, planar area scales by its absolute value.
The coordinate interchange has determinant `-1`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The horizontal coefficient of the pullback of `P dx + Q dy`. -/
def affinePullbackP (A : ℂ →ᴬ[ℝ] ℂ) (P Q : ℂ → ℝ) (z : ℂ) : ℝ :=
  oneForm P Q (A z) (A.contLinear 1)

/-- The vertical coefficient of the pullback of `P dx + Q dy`. -/
def affinePullbackQ (A : ℂ →ᴬ[ℝ] ℂ) (P Q : ℂ → ℝ) (z : ℂ) : ℝ :=
  oneForm P Q (A z) (A.contLinear Complex.I)

/-- The horizontal pullback coefficient in real coordinates. -/
theorem affinePullbackP_apply (A : ℂ →ᴬ[ℝ] ℂ) (P Q : ℂ → ℝ) (z : ℂ) :
    affinePullbackP A P Q z =
      P (A z) * (A.contLinear 1).re + Q (A z) * (A.contLinear 1).im :=
  oneForm_apply P Q (A z) (A.contLinear 1)

/-- The vertical pullback coefficient in real coordinates. -/
theorem affinePullbackQ_apply (A : ℂ →ᴬ[ℝ] ℂ) (P Q : ℂ → ℝ) (z : ℂ) :
    affinePullbackQ A P Q z =
      P (A z) * (A.contLinear Complex.I).re + Q (A z) * (A.contLinear Complex.I).im :=
  oneForm_apply P Q (A z) (A.contLinear Complex.I)

/-- The coefficient definitions give the actual pullback as a continuous linear map. -/
theorem oneForm_affinePullback (A : ℂ →ᴬ[ℝ] ℂ) (P Q : ℂ → ℝ) (z : ℂ) :
    oneForm (affinePullbackP A P Q) (affinePullbackQ A P Q) z =
      (oneForm P Q (A z)).comp A.contLinear := by
  ext v
  rw [oneForm_apply, ← ContinuousLinearMap.coe_coe,
    LinearMap.apply_eq_re_smul_one_add_im_smul_I
      ((oneForm P Q (A z)).comp A.contLinear).toLinearMap v]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, smul_eq_mul,
    affinePullbackP, affinePullbackQ]
  ring

/-- Curl transforms by the signed determinant under an affine pullback. Only differentiability
at the image point is needed, in particular this applies to locally real `C¹` fields. -/
theorem curl_affinePullback (A : ℂ →ᴬ[ℝ] ℂ) {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P (A z))
    (hQ : DifferentiableAt ℝ Q (A z)) :
    curl (affinePullbackP A P Q) (affinePullbackQ A P Q) z =
      A.linear.det * curl P Q (A z) := by
  have hp := hP.hasFDerivAt.comp z A.hasFDerivAt
  have hq := hQ.hasFDerivAt.comp z A.hasFDerivAt
  have hp' : HasFDerivAt (affinePullbackP A P Q)
      ((A.contLinear 1).re • (fderiv ℝ P (A z)).comp A.contLinear +
        (A.contLinear 1).im • (fderiv ℝ Q (A z)).comp A.contLinear) z := by
    convert (hp.mul_const (A.contLinear 1).re).add (hq.mul_const (A.contLinear 1).im) using 1
    ext w
    simp only [affinePullbackP, oneForm_apply, Pi.add_apply, Function.comp_apply]
  have hq' : HasFDerivAt (affinePullbackQ A P Q)
      ((A.contLinear Complex.I).re • (fderiv ℝ P (A z)).comp A.contLinear +
        (A.contLinear Complex.I).im • (fderiv ℝ Q (A z)).comp A.contLinear) z := by
    convert (hp.mul_const (A.contLinear Complex.I).re).add
      (hq.mul_const (A.contLinear Complex.I).im) using 1
    ext w
    simp only [affinePullbackQ, oneForm_apply, Pi.add_apply, Function.comp_apply]
  rw [curl, hp'.fderiv, hq'.fderiv, LinearMap.det_complex, curl]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  have heval (L : ℂ →L[ℝ] ℝ) (w : ℂ) : L w = w.re * L 1 + w.im * L Complex.I := by
    simpa only [ContinuousLinearMap.coe_coe, smul_eq_mul] using
      LinearMap.apply_eq_re_smul_one_add_im_smul_I L.toLinearMap w
  rw [heval _ (A.contLinear 1), heval _ (A.contLinear Complex.I),
    heval _ (A.contLinear 1), heval _ (A.contLinear Complex.I)]
  simp only [ContinuousAffineMap.coe_contLinear]
  ring

/-- Affine transport preserves absolute continuity without a bounded-speed assumption. -/
theorem absolutelyContinuousOnInterval_affineMap (A : ℂ →ᴬ[ℝ] ℂ)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (A ∘ γ) a b := by
  rw [A.decomp]
  exact ((isometry_add_right (A 0)).lipschitzWith.comp
    A.contLinear.lipschitzWith).comp_absolutelyContinuousOnInterval hγ

private theorem circulationFun_affineMap_ae (A : ℂ →ᴬ[ℝ] ℂ)
    (P Q : ℂ → ℝ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    circulationFun P Q (A ∘ γ) =ᵐ[volume.restrict (uIoc a b)]
      circulationFun (affinePullbackP A P Q) (affinePullbackQ A P Q) γ := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htmem
  have hd := ht (uIoc_subset_uIcc htmem)
  rw [circulationFun_eq_oneForm, circulationFun_eq_oneForm, oneForm_affinePullback]
  have hder : HasDerivAt (A ∘ γ) (A.contLinear (deriv γ t)) t :=
    A.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt
  rw [hder.deriv]
  rfl

/-- Integrability of circulation is preserved by pulling back the field along affine transport. -/
theorem intervalIntegrable_circulationFun_affineMap_iff (A : ℂ →ᴬ[ℝ] ℂ)
    (P Q : ℂ → ℝ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (circulationFun P Q (A ∘ γ)) volume a b ↔
      IntervalIntegrable
        (circulationFun (affinePullbackP A P Q) (affinePullbackQ A P Q) γ) volume a b := by
  exact intervalIntegrable_congr_ae (circulationFun_affineMap_ae A P Q hγ)

/-- The actual raw circulation integrals agree under affine pullback. -/
theorem integral_circulationFun_affineMap (A : ℂ →ᴬ[ℝ] ℂ)
    (P Q : ℂ → ℝ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    (∫ t in a..b, circulationFun P Q (A ∘ γ) t) =
      ∫ t in a..b,
        circulationFun (affinePullbackP A P Q) (affinePullbackQ A P Q) γ t := by
  exact intervalIntegral.integral_congr_ae_restrict
    (circulationFun_affineMap_ae A P Q hγ)

/-- The area measure on an affine image is the pushforward of the absolute determinant density. -/
theorem map_withDensity_affineMap (A : ℂ ≃ᴬ[ℝ] ℂ) {s : Set ℂ}
    (hs : NullMeasurableSet s volume) :
    Measure.map A
      ((volume.restrict s).withDensity
        (fun _ ↦ ENNReal.ofReal |A.linear.toLinearMap.det|)) =
      volume.restrict (A '' s) := by
  simpa only [ContinuousLinearMap.det,
    ContinuousAffineMap.coe_contLinear_eq_linear,
    ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.linear_toAffineMap] using
    map_withDensity_abs_det_fderiv_eq_addHaar volume hs
      (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn

/-- Change of variables for planar area under an invertible affine coordinate map. -/
theorem integral_affineMap_image (A : ℂ ≃ᴬ[ℝ] ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) (f : ℂ → ℝ) :
    (∫ z in A '' s, f z) =
      |A.linear.toLinearMap.det| * ∫ z in s, f (A z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn f]
  simp only [smul_eq_mul, integral_const_mul, ContinuousLinearMap.det,
    ContinuousAffineMap.coe_contLinear_eq_linear,
    ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.linear_toAffineMap]

/-- Affine images scale planar area by the absolute real determinant. -/
theorem volume_affineMap_image (A : ℂ ≃ᴬ[ℝ] ℂ) {s : Set ℂ}
    (hs : NullMeasurableSet s volume) :
    volume (A '' s) =
      ENNReal.ofReal |A.linear.toLinearMap.det| * volume s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hs
    (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn]
  simp only [lintegral_const, Measure.restrict_apply_univ, ContinuousLinearMap.det,
    ContinuousAffineMap.coe_contLinear_eq_linear,
    ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap,
    AffineEquiv.linear_toAffineMap]

/-- Area integrability is preserved under an invertible affine coordinate map. -/
theorem integrableOn_affineMap_image_iff (A : ℂ ≃ᴬ[ℝ] ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) (f : ℂ → ℝ) :
    IntegrableOn f (A '' s) ↔ IntegrableOn (f ∘ A) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (f := A) (f' := fun _ ↦ A.toContinuousAffineMap.contLinear)
    (fun _ _ ↦ A.toContinuousAffineMap.hasFDerivWithinAt)
    A.injective.injOn f]
  exact integrable_smul_iff (abs_ne_zero.mpr A.linear.isUnit_det'.ne_zero) _

/-- Integrability of curl is preserved by affine pullback for differentiable fields. -/
theorem integrableOn_curl_affinePullback_iff (A : ℂ ≃ᴬ[ℝ] ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) {P Q : ℂ → ℝ}
    (hP : ∀ z ∈ s, DifferentiableAt ℝ P (A z))
    (hQ : ∀ z ∈ s, DifferentiableAt ℝ Q (A z)) :
    IntegrableOn (curl (affinePullbackP A.toContinuousAffineMap P Q)
      (affinePullbackQ A.toContinuousAffineMap P Q)) s ↔
      IntegrableOn (curl P Q) (A '' s) := by
  rw [integrableOn_affineMap_image_iff A hs,
    integrableOn_congr_fun
      (fun z hz ↦ curl_affinePullback A.toContinuousAffineMap (hP z hz) (hQ z hz)) hs]
  exact integrable_smul_iff A.linear.isUnit_det'.ne_zero _

/-- Curl integration transports with the orientation factor `det A / |det A|`. The source
hypotheses hold, in particular, for fields locally real `C¹` on the affine image. -/
theorem integral_curl_affinePullback (A : ℂ ≃ᴬ[ℝ] ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) {P Q : ℂ → ℝ}
    (hP : ∀ z ∈ s, DifferentiableAt ℝ P (A z))
    (hQ : ∀ z ∈ s, DifferentiableAt ℝ Q (A z)) :
    (∫ z in s, curl (affinePullbackP A.toContinuousAffineMap P Q)
      (affinePullbackQ A.toContinuousAffineMap P Q) z) =
      (A.linear.toLinearMap.det / |A.linear.toLinearMap.det|) *
        ∫ z in A '' s, curl P Q z := by
  calc
    _ = ∫ z in s, A.linear.toLinearMap.det *
        curl P Q (A z) := setIntegral_congr_fun hs fun z hz ↦
          curl_affinePullback A.toContinuousAffineMap (hP z hz) (hQ z hz)
    _ = _ := by
      rw [integral_const_mul, integral_affineMap_image A hs]
      field_simp [abs_ne_zero.mpr A.linear.isUnit_det'.ne_zero]

/-- Coordinate interchange exchanges the two coefficients of a pulled-back 1-form. -/
theorem oneForm_coordinateSwap (P Q : ℂ → ℝ) (z : ℂ) :
    (oneForm P Q (Complex.coordinateSwapCLE z)).comp
      Complex.coordinateSwapCLE.toContinuousLinearMap =
      oneForm (Q ∘ Complex.coordinateSwapCLE) (P ∘ Complex.coordinateSwapCLE) z := by
  ext v
  simp [oneForm_apply, Complex.coordinateSwapCLE_apply, ContinuousLinearEquiv.coe_coe]
  ring

/-- Interchanging real and imaginary coordinates negates the curl. -/
theorem curl_coordinateSwap {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P (Complex.coordinateSwapCLE z))
    (hQ : DifferentiableAt ℝ Q (Complex.coordinateSwapCLE z)) :
    curl (Q ∘ Complex.coordinateSwapCLE) (P ∘ Complex.coordinateSwapCLE) z =
      -curl P Q (Complex.coordinateSwapCLE z) := by
  have hp : affinePullbackP Complex.coordinateSwapCLE.toContinuousAffineEquiv.toContinuousAffineMap
      P Q = Q ∘ Complex.coordinateSwapCLE := by
    ext w
    change oneForm P Q (Complex.coordinateSwapCLE w) (Complex.coordinateSwapCLE 1) = _
    simp [oneForm_apply, Complex.coordinateSwapCLE_apply]
  have hq : affinePullbackQ Complex.coordinateSwapCLE.toContinuousAffineEquiv.toContinuousAffineMap
      P Q = P ∘ Complex.coordinateSwapCLE := by
    ext w
    change oneForm P Q (Complex.coordinateSwapCLE w)
      (Complex.coordinateSwapCLE Complex.I) = _
    simp [oneForm_apply, Complex.coordinateSwapCLE_apply]
  have he := curl_affinePullback
    Complex.coordinateSwapCLE.toContinuousAffineEquiv.toContinuousAffineMap hP hQ
  rw [hp, hq] at he
  change curl (Q ∘ Complex.coordinateSwapCLE) (P ∘ Complex.coordinateSwapCLE) z =
    Complex.coordinateSwapCLE.toLinearEquiv.toLinearMap.det *
      curl P Q (Complex.coordinateSwapCLE z) at he
  simpa only [Complex.det_coordinateSwapCLE, neg_one_mul] using he

private theorem oneForm_affineMap_lineMap (A : ℂ →ᴬ[ℝ] ℂ) (p q : ℂ)
    (P Q : ℂ → ℝ) (t : ℝ) :
    oneForm P Q (AffineMap.lineMap (A p) (A q) t)
        (A q - A p) =
      oneForm (affinePullbackP A P Q) (affinePullbackQ A P Q)
        (AffineMap.lineMap p q t) (q - p) := by
  rw [oneForm_affinePullback, ContinuousLinearMap.comp_apply, A.apply_lineMap]
  congr 1
  exact (A.contLinear_map_vsub q p).symm

/-- Genuine segment integrability is preserved by affine pullback of the planar 1-form. -/
theorem curveIntegrable_segment_affineMap_iff (A : ℂ →ᴬ[ℝ] ℂ) (p q : ℂ) (P Q : ℂ → ℝ) :
    CurveIntegrable (oneForm P Q) (Path.segment (A p) (A q)) ↔
      CurveIntegrable (oneForm (affinePullbackP A P Q) (affinePullbackQ A P Q))
        (Path.segment p q) := by
  rw [curveIntegrable_segment, curveIntegrable_segment]
  exact intervalIntegrable_congr fun t _ ↦ oneForm_affineMap_lineMap A p q P Q t

/-- Actual segment circulation transports to the pulled-back planar 1-form. -/
theorem curveIntegral_segment_affineMap (A : ℂ →ᴬ[ℝ] ℂ) (p q : ℂ) (P Q : ℂ → ℝ) :
    curveIntegral (oneForm P Q) (Path.segment (A p) (A q)) =
      curveIntegral (oneForm (affinePullbackP A P Q) (affinePullbackQ A P Q))
        (Path.segment p q) := by
  rw [curveIntegral_segment, curveIntegral_segment]
  exact intervalIntegral.integral_congr fun t _ ↦ oneForm_affineMap_lineMap A p q P Q t

end TauCeti.Green
