/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.Green.Cell
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Invertible affine changes of planar coordinates

The pullback of `P dx + Q dy` along `z ↦ A z + c` transports circulation along absolutely
continuous curves. Its curl scales by the signed real determinant of `A`, whereas planar area
scales by its absolute value. The coordinate interchange has determinant `-1`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- An invertible real affine change of planar coordinates. -/
def affineMap (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (z : ℂ) : ℂ := A z + c

/-- Evaluation of the affine coordinate map. -/
@[simp]
theorem affineMap_apply (A : ℂ ≃L[ℝ] ℂ) (c z : ℂ) : affineMap A c z = A z + c := (rfl)

/-- The horizontal coefficient of the pullback of `P dx + Q dy`. -/
def affinePullbackP (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (P Q : ℂ → ℝ) (z : ℂ) : ℝ :=
  oneForm P Q (affineMap A c z) (A 1)

/-- The vertical coefficient of the pullback of `P dx + Q dy`. -/
def affinePullbackQ (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (P Q : ℂ → ℝ) (z : ℂ) : ℝ :=
  oneForm P Q (affineMap A c z) (A Complex.I)

/-- The horizontal pullback coefficient in real coordinates. -/
theorem affinePullbackP_apply (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (P Q : ℂ → ℝ) (z : ℂ) :
    affinePullbackP A c P Q z =
      P (affineMap A c z) * (A 1).re + Q (affineMap A c z) * (A 1).im :=
  oneForm_apply P Q (affineMap A c z) (A 1)

/-- The vertical pullback coefficient in real coordinates. -/
theorem affinePullbackQ_apply (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (P Q : ℂ → ℝ) (z : ℂ) :
    affinePullbackQ A c P Q z =
      P (affineMap A c z) * (A Complex.I).re + Q (affineMap A c z) * (A Complex.I).im :=
  oneForm_apply P Q (affineMap A c z) (A Complex.I)

/-- The coefficient definitions give the actual pullback as a continuous linear map. -/
theorem oneForm_affinePullback (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (P Q : ℂ → ℝ) (z : ℂ) :
    oneForm (affinePullbackP A c P Q) (affinePullbackQ A c P Q) z =
      (oneForm P Q (affineMap A c z)).comp A.toContinuousLinearMap := by
  ext v
  rw [oneForm_apply, ← ContinuousLinearMap.coe_coe,
    LinearMap.apply_eq_re_smul_one_add_im_smul_I
      ((oneForm P Q (affineMap A c z)).comp A.toContinuousLinearMap).toLinearMap v]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, smul_eq_mul,
    affinePullbackP, affinePullbackQ, ContinuousLinearEquiv.coe_coe]
  ring

/-- The affine coordinate map has constant derivative `A`. -/
theorem hasFDerivAt_affineMap (A : ℂ ≃L[ℝ] ℂ) (c z : ℂ) :
    HasFDerivAt (affineMap A c) A.toContinuousLinearMap z :=
  A.toContinuousLinearMap.hasFDerivAt.add_const c

/-- Curl transforms by the signed determinant under an affine pullback. Only differentiability
at the image point is needed, in particular this applies to locally real `C¹` fields. -/
theorem curl_affinePullback (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P (affineMap A c z))
    (hQ : DifferentiableAt ℝ Q (affineMap A c z)) :
    curl (affinePullbackP A c P Q) (affinePullbackQ A c P Q) z =
      A.toLinearEquiv.toLinearMap.det * curl P Q (affineMap A c z) := by
  have hp := hP.hasFDerivAt.comp z (hasFDerivAt_affineMap A c z)
  have hq := hQ.hasFDerivAt.comp z (hasFDerivAt_affineMap A c z)
  have hp' : HasFDerivAt (affinePullbackP A c P Q)
      ((A 1).re • (fderiv ℝ P (affineMap A c z)).comp A.toContinuousLinearMap +
        (A 1).im • (fderiv ℝ Q (affineMap A c z)).comp A.toContinuousLinearMap) z := by
    convert (hp.mul_const (A 1).re).add (hq.mul_const (A 1).im) using 1
    ext w
    simp only [affinePullbackP, oneForm_apply, Pi.add_apply, Function.comp_apply]
  have hq' : HasFDerivAt (affinePullbackQ A c P Q)
      ((A Complex.I).re • (fderiv ℝ P (affineMap A c z)).comp A.toContinuousLinearMap +
        (A Complex.I).im • (fderiv ℝ Q (affineMap A c z)).comp A.toContinuousLinearMap) z := by
    convert (hp.mul_const (A Complex.I).re).add (hq.mul_const (A Complex.I).im) using 1
    ext w
    simp only [affinePullbackQ, oneForm_apply, Pi.add_apply, Function.comp_apply]
  rw [curl, hp'.fderiv, hq'.fderiv, LinearMap.det_complex, curl]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  simp only [← ContinuousLinearMap.coe_coe]
  rw [LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ P (affineMap A c z)).toLinearMap (A 1),
    LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ P (affineMap A c z)).toLinearMap (A Complex.I),
    LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ Q (affineMap A c z)).toLinearMap (A 1),
    LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ Q (affineMap A c z)).toLinearMap (A Complex.I)]
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul]
  ring

/-- Affine transport preserves absolute continuity without a bounded-speed assumption. -/
theorem absolutelyContinuousOnInterval_affineMap (A : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (affineMap A c ∘ γ) a b := by
  exact ((isometry_add_right c).lipschitzWith.comp
    A.toContinuousLinearMap.lipschitzWith).comp_absolutelyContinuousOnInterval hγ

private theorem circulationFun_affineMap_ae (A : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (P Q : ℂ → ℝ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    circulationFun P Q (affineMap A c ∘ γ) =ᵐ[volume.restrict (uIoc a b)]
      circulationFun (affinePullbackP A c P Q) (affinePullbackQ A c P Q) γ := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htmem
  have hd := ht (uIoc_subset_uIcc htmem)
  rw [circulationFun_eq_oneForm, circulationFun_eq_oneForm, oneForm_affinePullback]
  have hder : HasDerivAt (affineMap A c ∘ γ) (A (deriv γ t)) t :=
    (hasFDerivAt_affineMap A c (γ t)).comp_hasDerivAt t hd.hasDerivAt
  rw [hder.deriv]
  rfl

/-- Integrability of circulation is preserved by pulling back the field along affine transport. -/
theorem intervalIntegrable_circulationFun_affineMap_iff (A : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (P Q : ℂ → ℝ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (circulationFun P Q (affineMap A c ∘ γ)) volume a b ↔
      IntervalIntegrable
        (circulationFun (affinePullbackP A c P Q) (affinePullbackQ A c P Q) γ) volume a b := by
  exact intervalIntegrable_congr_ae (circulationFun_affineMap_ae A c P Q hγ)

/-- The actual raw circulation integrals agree under affine pullback. -/
theorem integral_circulationFun_affineMap (A : ℂ ≃L[ℝ] ℂ) (c : ℂ)
    (P Q : ℂ → ℝ) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    (∫ t in a..b, circulationFun P Q (affineMap A c ∘ γ) t) =
      ∫ t in a..b,
        circulationFun (affinePullbackP A c P Q) (affinePullbackQ A c P Q) γ t := by
  exact intervalIntegral.integral_congr_ae_restrict
    (circulationFun_affineMap_ae A c P Q hγ)

/-- The area measure on an affine image is the pushforward of the absolute determinant density. -/
theorem map_withDensity_affineMap (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {s : Set ℂ}
    (hs : NullMeasurableSet s volume) :
    Measure.map (affineMap A c)
      ((volume.restrict s).withDensity
        (fun _ ↦ ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det|)) =
      volume.restrict (affineMap A c '' s) := by
  simpa only [ContinuousLinearMap.det,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap] using
    map_withDensity_abs_det_fderiv_eq_addHaar volume hs
      (f' := fun _ ↦ A.toContinuousLinearMap)
    (fun z _ ↦ (hasFDerivAt_affineMap A c z).hasFDerivWithinAt)
    (fun _ _ _ _ h ↦ A.injective (add_right_cancel h))

/-- Change of variables for planar area under an invertible affine coordinate map. -/
theorem integral_affineMap_image (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) (f : ℂ → ℝ) :
    (∫ z in affineMap A c '' s, f z) =
      |A.toLinearEquiv.toLinearMap.det| * ∫ z in s, f (affineMap A c z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (f' := fun _ ↦ A.toContinuousLinearMap)
    (fun z _ ↦ (hasFDerivAt_affineMap A c z).hasFDerivWithinAt)
    (fun _ _ _ _ h ↦ A.injective (add_right_cancel h)) f]
  simp only [smul_eq_mul, integral_const_mul, ContinuousLinearMap.det,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- Affine images scale planar area by the absolute real determinant. -/
theorem volume_affineMap_image (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {s : Set ℂ}
    (hs : NullMeasurableSet s volume) :
    volume (affineMap A c '' s) =
      ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det| * volume s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hs
    (f' := fun _ ↦ A.toContinuousLinearMap)
    (fun z _ ↦ (hasFDerivAt_affineMap A c z).hasFDerivWithinAt)
    (fun _ _ _ _ h ↦ A.injective (add_right_cancel h))]
  simp only [lintegral_const, Measure.restrict_apply_univ, ContinuousLinearMap.det,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- Area integrability is preserved under an invertible affine coordinate map. -/
theorem integrableOn_affineMap_image_iff (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) (f : ℂ → ℝ) :
    IntegrableOn f (affineMap A c '' s) ↔ IntegrableOn (f ∘ affineMap A c) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (f' := fun _ ↦ A.toContinuousLinearMap)
    (fun z _ ↦ (hasFDerivAt_affineMap A c z).hasFDerivWithinAt)
    (fun _ _ _ _ h ↦ A.injective (add_right_cancel h)) f]
  exact integrable_smul_iff (abs_ne_zero.mpr A.toLinearEquiv.isUnit_det'.ne_zero) _

/-- Integrability of curl is preserved by affine pullback for differentiable fields. -/
theorem integrableOn_curl_affinePullback_iff (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) {P Q : ℂ → ℝ}
    (hP : ∀ z ∈ s, DifferentiableAt ℝ P (affineMap A c z))
    (hQ : ∀ z ∈ s, DifferentiableAt ℝ Q (affineMap A c z)) :
    IntegrableOn (curl (affinePullbackP A c P Q) (affinePullbackQ A c P Q)) s ↔
      IntegrableOn (curl P Q) (affineMap A c '' s) := by
  rw [integrableOn_affineMap_image_iff A c hs,
    integrableOn_congr_fun (fun z hz ↦ curl_affinePullback A c (hP z hz) (hQ z hz)) hs]
  exact integrable_smul_iff A.toLinearEquiv.isUnit_det'.ne_zero _

/-- Curl integration transports with the orientation factor `det A / |det A|`. The source
hypotheses hold, in particular, for fields locally real `C¹` on the affine image. -/
theorem integral_curl_affinePullback (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) {P Q : ℂ → ℝ}
    (hP : ∀ z ∈ s, DifferentiableAt ℝ P (affineMap A c z))
    (hQ : ∀ z ∈ s, DifferentiableAt ℝ Q (affineMap A c z)) :
    (∫ z in s, curl (affinePullbackP A c P Q) (affinePullbackQ A c P Q) z) =
      (A.toLinearEquiv.toLinearMap.det / |A.toLinearEquiv.toLinearMap.det|) *
        ∫ z in affineMap A c '' s, curl P Q z := by
  calc
    _ = ∫ z in s, A.toLinearEquiv.toLinearMap.det *
        curl P Q (affineMap A c z) := setIntegral_congr_fun hs fun z hz ↦
          curl_affinePullback A c (hP z hz) (hQ z hz)
    _ = _ := by
      rw [integral_const_mul, integral_affineMap_image A c hs]
      field_simp [abs_ne_zero.mpr A.toLinearEquiv.isUnit_det'.ne_zero]

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
  have hp : affinePullbackP Complex.coordinateSwapCLE 0 P Q = Q ∘ Complex.coordinateSwapCLE := by
    ext w
    simp [affinePullbackP, affineMap, oneForm_apply, Complex.coordinateSwapCLE_apply]
  have hq : affinePullbackQ Complex.coordinateSwapCLE 0 P Q = P ∘ Complex.coordinateSwapCLE := by
    ext w
    simp [affinePullbackQ, affineMap, oneForm_apply, Complex.coordinateSwapCLE_apply]
  have he := curl_affinePullback Complex.coordinateSwapCLE 0 (P := P) (Q := Q) (z := z)
    (by simpa only [affineMap, Complex.coordinateSwapCLE_apply,
      Complex.coordinateSwapCLE_apply, add_zero] using hP)
    (by simpa only [affineMap, Complex.coordinateSwapCLE_apply,
      Complex.coordinateSwapCLE_apply, add_zero] using hQ)
  rw [hp, hq, Complex.det_coordinateSwapCLE] at he
  simpa only [affineMap, Complex.coordinateSwapCLE_apply,
    add_zero, neg_one_mul] using he

/-- An affine coordinate map carries convex hulls to the convex hulls of their images. -/
theorem affineMap_image_convexHull (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (s : Set ℂ) :
    affineMap A c '' convexHull ℝ s = convexHull ℝ (affineMap A c '' s) := by
  let T : ℂ →ᵃ[ℝ] ℂ := A.toLinearEquiv.toLinearMap.toAffineMap + AffineMap.const ℝ ℂ c
  have heq : (T : ℂ → ℂ) = affineMap A c := by
    ext z
    rw [affineMap_apply]
    rfl
  simpa only [heq] using T.image_convexHull s

/-- Affine coordinates commute with taking interiors. -/
theorem affineMap_image_interior (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (s : Set ℂ) :
    affineMap A c '' interior s = interior (affineMap A c '' s) := by
  have heq : affineMap A c = Homeomorph.addRight c ∘ A := by
    ext z
    rw [affineMap_apply]
    rfl
  have hT : IsHomeomorph (affineMap A c) := by
    rw [heq]
    exact (Homeomorph.addRight c).isHomeomorph.comp A.toHomeomorph.isHomeomorph
  exact hT.image_interior s

/-- Affine transport commutes with parameterization of straight segments. -/
theorem affineMap_lineMap (A : ℂ ≃L[ℝ] ℂ) (c p q : ℂ) (t : ℝ) :
    affineMap A c (AffineMap.lineMap p q t) =
      AffineMap.lineMap (affineMap A c p) (affineMap A c q) t := by
  simp only [affineMap_apply, AffineMap.lineMap_apply_module, map_add, map_smul, smul_add]
  module

private theorem oneForm_affineMap_lineMap (A : ℂ ≃L[ℝ] ℂ) (c p q : ℂ)
    (P Q : ℂ → ℝ) (t : ℝ) :
    oneForm P Q (AffineMap.lineMap (affineMap A c p) (affineMap A c q) t)
        (affineMap A c q - affineMap A c p) =
      oneForm (affinePullbackP A c P Q) (affinePullbackQ A c P Q)
        (AffineMap.lineMap p q t) (q - p) := by
  rw [oneForm_affinePullback, ContinuousLinearMap.comp_apply, affineMap_lineMap]
  congr 1
  simp only [affineMap_apply, map_sub, ContinuousLinearEquiv.coe_coe]
  abel

/-- Genuine segment integrability is preserved by affine pullback of the planar 1-form. -/
theorem curveIntegrable_segment_affineMap_iff (A : ℂ ≃L[ℝ] ℂ) (c p q : ℂ) (P Q : ℂ → ℝ) :
    CurveIntegrable (oneForm P Q) (Path.segment (affineMap A c p) (affineMap A c q)) ↔
      CurveIntegrable (oneForm (affinePullbackP A c P Q) (affinePullbackQ A c P Q))
        (Path.segment p q) := by
  rw [curveIntegrable_segment, curveIntegrable_segment]
  exact intervalIntegrable_congr fun t _ ↦ oneForm_affineMap_lineMap A c p q P Q t

/-- Actual segment circulation transports to the pulled-back planar 1-form. -/
theorem curveIntegral_segment_affineMap (A : ℂ ≃L[ℝ] ℂ) (c p q : ℂ) (P Q : ℂ → ℝ) :
    curveIntegral (oneForm P Q) (Path.segment (affineMap A c p) (affineMap A c q)) =
      curveIntegral (oneForm (affinePullbackP A c P Q) (affinePullbackQ A c P Q))
        (Path.segment p q) := by
  rw [curveIntegral_segment, curveIntegral_segment]
  exact intervalIntegral.integral_congr fun t _ ↦ oneForm_affineMap_lineMap A c p q P Q t

/-- Affine coordinate maps are real smooth. -/
theorem contDiff_affineMap (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (affineMap A c) := by
  convert A.toContinuousLinearMap.contDiff.add (contDiff_const (c := c)) using 1
  ext z
  rw [affineMap_apply]
  rfl

end TauCeti.Green
