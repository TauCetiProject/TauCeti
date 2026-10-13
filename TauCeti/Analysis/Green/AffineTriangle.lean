/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Affine
public import TauCeti.Analysis.Green.Polygonal.Geometry
public import TauCeti.Analysis.Green.Division.TriangleGreen
import Mathlib.Analysis.Convex.Hull

/-!
# Affine coordinates on nondegenerate triangles

The positive real basis `(1,I)` gives an invertible affine coordinate map from the standard
triangle to any nondegenerate ordered triangle. Its determinant is the existing `triangleDet`.
Area uses the absolute determinant; the oriented three-segment circulation retains its sign.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The real linear map sending the positive basis to the two edges based at `c`. -/
def triangleLinearMap (c p q : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  Complex.basisOneI.constr ℝ ![p - c, q - c]

/-- The first basis vector is sent to the first edge. -/
@[simp]
theorem triangleLinearMap_one (c p q : ℂ) : triangleLinearMap c p q 1 = p - c := by
  simpa only [triangleLinearMap, Complex.coe_basisOneI, Matrix.cons_val_zero] using
    Complex.basisOneI.constr_basis ℝ ![p - c, q - c] 0

/-- The second basis vector is sent to the second edge. -/
@[simp]
theorem triangleLinearMap_I (c p q : ℂ) : triangleLinearMap c p q Complex.I = q - c := by
  simpa only [triangleLinearMap, Complex.coe_basisOneI, Matrix.cons_val_one,
    Matrix.cons_val_zero] using
    Complex.basisOneI.constr_basis ℝ ![p - c, q - c] 1

/-- The determinant of the triangle coordinate map is the existing oriented triangle determinant. -/
theorem det_triangleLinearMap (c p q : ℂ) : (triangleLinearMap c p q).det = triangleDet c p q := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, triangleLinearMap_one, triangleLinearMap_I]
  rw [triangleDet_def]
  ring

/-- Nonzero triangle determinant gives an invertible real continuous linear coordinate map. -/
def triangleCoordinates (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ((triangleLinearMap c p q).equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr ((det_triangleLinearMap c p q).trans_ne hdet))).toContinuousLinearEquiv

/-- The invertible triangle coordinates have the prescribed underlying linear map. -/
theorem triangleCoordinates_toLinearMap (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    (triangleCoordinates c p q hdet).toLinearEquiv.toLinearMap = triangleLinearMap c p q := by
  rw [triangleCoordinates, LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]
  exact LinearMap.coe_equivOfIsUnitDet _

/-- Triangle coordinates send `1` to the first edge vector. -/
@[simp]
theorem triangleCoordinates_one (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    triangleCoordinates c p q hdet 1 = p - c := by
  have h := congrArg (fun L : ℂ →ₗ[ℝ] ℂ ↦ L 1) (triangleCoordinates_toLinearMap c p q hdet)
  simpa only [triangleLinearMap_one, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

/-- Triangle coordinates send `I` to the second edge vector. -/
@[simp]
theorem triangleCoordinates_I (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    triangleCoordinates c p q hdet Complex.I = q - c := by
  have h := congrArg (fun L : ℂ →ₗ[ℝ] ℂ ↦ L Complex.I)
    (triangleCoordinates_toLinearMap c p q hdet)
  simpa only [triangleLinearMap_I, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

/-- The coordinate determinant is the oriented triangle determinant. -/
theorem det_triangleCoordinates (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    (triangleCoordinates c p q hdet).toLinearEquiv.toLinearMap.det = triangleDet c p q := by
  rw [triangleCoordinates_toLinearMap, det_triangleLinearMap]

/-- An affine coordinate map carries convex hulls to the convex hulls of their images. -/
theorem affineMap_image_convexHull (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) (s : Set ℂ) :
    affineMap A c '' convexHull ℝ s = convexHull ℝ (affineMap A c '' s) := by
  let T : ℂ →ᵃ[ℝ] ℂ := A.toLinearEquiv.toLinearMap.toAffineMap + AffineMap.const ℝ ℂ c
  have heq : (T : ℂ → ℂ) = affineMap A c := by
    ext z
    rw [affineMap_apply]
    rfl
  simpa only [heq] using T.image_convexHull s

/-- Triangle coordinates identify the actual closed convex hulls. -/
theorem affineMap_image_standardTriangle (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    affineMap (triangleCoordinates c p q hdet) c '' standardTriangle = convexHull ℝ {c, p, q} := by
  rw [standardTriangle_def, affineMap_image_convexHull]
  simp only [image_insert_eq, image_singleton, affineMap_apply, map_zero, zero_add,
    triangleCoordinates_one, triangleCoordinates_I, sub_add_cancel]

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

/-- The actual open triangle is the image of the standard triangle interior. -/
theorem affineMap_image_interior_standardTriangle (c p q : ℂ)
    (hdet : triangleDet c p q ≠ 0) :
    affineMap (triangleCoordinates c p q hdet) c '' interior standardTriangle =
      interior (convexHull ℝ {c, p, q}) := by
  rw [affineMap_image_interior, affineMap_image_standardTriangle]

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

/-- The literal three-segment triangle chain transports its actual curve-integral sum. -/
theorem curveIntegral_triangle_affineMap (A : ℂ ≃L[ℝ] ℂ) (c p q r : ℂ) (P Q : ℂ → ℝ) :
    Finsupp.linearCombination ℤ (fun γ : Arc ↦ curveIntegral (oneForm P Q) γ.2.2)
      (BoundaryChain.triangle (affineMap A c p) (affineMap A c q) (affineMap A c r)) =
    Finsupp.linearCombination ℤ
      (fun γ : Arc ↦ curveIntegral
        (oneForm (affinePullbackP A c P Q) (affinePullbackQ A c P Q)) γ.2.2)
      (BoundaryChain.triangle p q r) := by
  simp only [BoundaryChain.triangle_def, map_sub, map_add, BoundaryChain.ofPath_def,
    Finsupp.linearCombination_single, one_smul, curveIntegral_segment_affineMap]

/-- Positive planar area on an ordered triangle scales by the absolute triangle determinant. -/
theorem volume_convexHull_triangle (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    volume (convexHull ℝ {c, p, q}) =
      ENNReal.ofReal |triangleDet c p q| * volume standardTriangle := by
  rw [← affineMap_image_standardTriangle c p q hdet,
    volume_affineMap_image _ _ isCompact_standardTriangle.measurableSet.nullMeasurableSet,
    det_triangleCoordinates]

/-- Area integration on an actual triangle agrees with the affine-coordinate integral. -/
theorem integral_convexHull_triangle (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) (f : ℂ → ℝ) :
    (∫ z in convexHull ℝ {c, p, q}, f z) = |triangleDet c p q| *
      ∫ z in standardTriangle, f (affineMap (triangleCoordinates c p q hdet) c z) := by
  rw [← affineMap_image_standardTriangle c p q hdet,
    integral_affineMap_image _ _ isCompact_standardTriangle.measurableSet,
    det_triangleCoordinates]

/-- Affine coordinate maps are real smooth. -/
theorem contDiff_affineMap (A : ℂ ≃L[ℝ] ℂ) (c : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (affineMap A c) := by
  convert A.toContinuousLinearMap.contDiff.add (contDiff_const (c := c)) using 1
  ext z
  rw [affineMap_apply]
  rfl

private theorem contDiffOn_affinePullback {A : ℂ ≃L[ℝ] ℂ} {c : ℂ} {U : Set ℂ}
    {P Q : ℂ → ℝ} (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ContDiffOn ℝ 1 (affinePullbackP A c P Q) (affineMap A c ⁻¹' U) ∧
      ContDiffOn ℝ 1 (affinePullbackQ A c P Q) (affineMap A c ⁻¹' U) := by
  have hp := hP.comp (contDiff_affineMap A c).contDiffOn (mapsTo_preimage _ _)
  have hq := hQ.comp (contDiff_affineMap A c).contDiffOn (mapsTo_preimage _ _)
  constructor
  · convert (hp.mul (contDiffOn_const (c := (A 1).re))).add
      (hq.mul (contDiffOn_const (c := (A 1).im))) using 1
    ext z
    exact affinePullbackP_apply A c P Q z
  · convert (hp.mul (contDiffOn_const (c := (A Complex.I).re))).add
      (hq.mul (contDiffOn_const (c := (A Complex.I).im))) using 1
    ext z
    exact affinePullbackQ_apply A c P Q z

/-- Green's theorem on any nondegenerate ordered triangle. The sign of its orientation is
`triangleDet / |triangleDet|`, and the area integral uses the usual positive planar volume. -/
theorem green_triangle_of_det_ne_zero {c p q : ℂ} (hdet : triangleDet c p q ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hTU : convexHull ℝ {c, p, q} ⊆ U)
    {P Q : ℂ → ℝ} (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IntegrableOn (curl P Q) (convexHull ℝ {c, p, q}) ∧
      curveIntegral (oneForm P Q) (Path.segment c p) +
        curveIntegral (oneForm P Q) (Path.segment p q) -
        curveIntegral (oneForm P Q) (Path.segment c q) =
      (triangleDet c p q / |triangleDet c p q|) *
        ∫ z in convexHull ℝ {c, p, q}, curl P Q z := by
  let A := triangleCoordinates c p q hdet
  have hTcont := (contDiff_affineMap A c (n := 1)).continuous
  have hstd : standardTriangle ⊆ affineMap A c ⁻¹' U := by
    intro z hz
    exact hTU (affineMap_image_standardTriangle c p q hdet ▸ mem_image_of_mem _ hz)
  have hpq := contDiffOn_affinePullback (A := A) (c := c) hP hQ
  have hbase := green_standardTriangle (hU.preimage hTcont) hstd hpq.1 hpq.2
  have hPd (z : ℂ) (hz : z ∈ standardTriangle) :
      DifferentiableAt ℝ P (affineMap A c z) :=
    (hP _ (hstd hz)).contDiffAt (hU.mem_nhds (hstd hz)) |>.differentiableAt one_ne_zero
  have hQd (z : ℂ) (hz : z ∈ standardTriangle) :
      DifferentiableAt ℝ Q (affineMap A c z) :=
    (hQ _ (hstd hz)).contDiffAt (hU.mem_nhds (hstd hz)) |>.differentiableAt one_ne_zero
  have hi := (integrableOn_curl_affinePullback_iff A c isCompact_standardTriangle.measurableSet
    hPd hQd).mp hbase.1
  rw [affineMap_image_standardTriangle] at hi
  refine ⟨hi, ?_⟩
  have harea := integral_curl_affinePullback A c isCompact_standardTriangle.measurableSet hPd hQd
  rw [affineMap_image_standardTriangle, det_triangleCoordinates] at harea
  rw [← curveIntegral_segment_affineMap A c 0 1 P Q,
    ← curveIntegral_segment_affineMap A c 1 Complex.I P Q,
    ← curveIntegral_segment_affineMap A c 0 Complex.I P Q, harea] at hbase
  have ht0 : affineMap A c 0 = c := by rw [affineMap_apply, map_zero, zero_add]
  have ht1 : affineMap A c 1 = p := by
    rw [affineMap_apply, triangleCoordinates_one, sub_add_cancel]
  have htI : affineMap A c Complex.I = q := by
    rw [affineMap_apply, triangleCoordinates_I, sub_add_cancel]
  rw [ht0, ht1, htI] at hbase
  exact hbase.2

end TauCeti.Green
