/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Affine.Basic
import TauCeti.LinearAlgebra.Complex.Determinant
public import TauCeti.Analysis.Green.Polygonal.Geometry
public import TauCeti.Analysis.Green.Division.Triangle.Green

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
  rw [LinearMap.det_complex, triangleLinearMap_one, triangleLinearMap_I, triangleDet_def]
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

/-- Triangle coordinates identify the actual closed convex hulls. -/
theorem affineMap_image_standardTriangle (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) :
    affineMap (triangleCoordinates c p q hdet).toContinuousLinearMap c '' standardTriangle =
      convexHull ℝ {c, p, q} := by
  rw [standardTriangle_def, affineMap_image_convexHull]
  simp only [image_insert_eq, image_singleton, affineMap_apply, map_zero, zero_add,
    ContinuousLinearEquiv.coe_coe, triangleCoordinates_one, triangleCoordinates_I, sub_add_cancel]

/-- The actual open triangle is the image of the standard triangle interior. -/
theorem affineMap_image_interior_standardTriangle (c p q : ℂ)
    (hdet : triangleDet c p q ≠ 0) :
    affineMap (triangleCoordinates c p q hdet).toContinuousLinearMap c ''
      interior standardTriangle =
      interior (convexHull ℝ {c, p, q}) := by
  rw [affineMap_image_interior, affineMap_image_standardTriangle]

/-- The literal three-segment triangle chain transports its actual curve-integral sum. -/
theorem curveIntegral_triangle_affineMap (A : ℂ →L[ℝ] ℂ) (c p q r : ℂ) (P Q : ℂ → ℝ) :
    Finsupp.linearCombination ℤ (fun γ : Arc ↦ curveIntegral (oneForm P Q) γ.2.2)
      (BoundaryChain.triangle (affineMap A c p) (affineMap A c q) (affineMap A c r)) =
    Finsupp.linearCombination ℤ
      (fun γ : Arc ↦ curveIntegral
        (oneForm (affinePullbackP A c P Q) (affinePullbackQ A c P Q)) γ.2.2)
      (BoundaryChain.triangle p q r) := by
  simp only [BoundaryChain.triangle_def, map_sub, map_add, BoundaryChain.ofPath_def,
    Finsupp.linearCombination_single, one_smul, curveIntegral_segment_affineMap]

/-- Positive planar area on an ordered triangle scales by the absolute triangle determinant. -/
theorem volume_convexHull_triangle (c p q : ℂ) :
    volume (convexHull ℝ {c, p, q}) =
      ENNReal.ofReal |triangleDet c p q| * volume standardTriangle := by
  by_cases hdet : triangleDet c p q = 0
  · rw [volume_convexHull_triangle_eq_zero hdet, hdet, abs_zero, ENNReal.ofReal_zero, zero_mul]
  · rw [← affineMap_image_standardTriangle c p q hdet,
      volume_affineMap_image _ _ isCompact_standardTriangle.measurableSet.nullMeasurableSet,
      det_triangleCoordinates]

/-- Area integration on an actual triangle agrees with the affine-coordinate integral. -/
theorem integral_convexHull_triangle (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) (f : ℂ → ℝ) :
    (∫ z in convexHull ℝ {c, p, q}, f z) = |triangleDet c p q| *
      ∫ z in standardTriangle,
        f (affineMap (triangleCoordinates c p q hdet).toContinuousLinearMap c z) := by
  rw [← affineMap_image_standardTriangle c p q hdet,
    integral_affineMap_image _ _ isCompact_standardTriangle.measurableSet,
    det_triangleCoordinates]

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
  have hTcont := (contDiff_affineMap A.toContinuousLinearMap c (n := 1)).continuous
  have hstd : standardTriangle ⊆ affineMap A.toContinuousLinearMap c ⁻¹' U := by
    intro z hz
    exact hTU (affineMap_image_standardTriangle c p q hdet ▸ mem_image_of_mem _ hz)
  have hpq := contDiffOn_affinePullback (A := A.toContinuousLinearMap) (c := c) hP hQ
  have hbase := green_standardTriangle (hU.preimage hTcont) hstd hpq.1 hpq.2
  have hPd (z : ℂ) (hz : z ∈ standardTriangle) :
      DifferentiableAt ℝ P (affineMap A.toContinuousLinearMap c z) :=
    (hP _ (hstd hz)).contDiffAt (hU.mem_nhds (hstd hz)) |>.differentiableAt one_ne_zero
  have hQd (z : ℂ) (hz : z ∈ standardTriangle) :
      DifferentiableAt ℝ Q (affineMap A.toContinuousLinearMap c z) :=
    (hQ _ (hstd hz)).contDiffAt (hU.mem_nhds (hstd hz)) |>.differentiableAt one_ne_zero
  have hi := (integrableOn_curl_affinePullback_iff A c isCompact_standardTriangle.measurableSet
    hPd hQd).mp hbase.1
  rw [affineMap_image_standardTriangle] at hi
  refine ⟨hi, ?_⟩
  have harea := integral_curl_affinePullback A c isCompact_standardTriangle.measurableSet hPd hQd
  rw [affineMap_image_standardTriangle, det_triangleCoordinates] at harea
  rw [← curveIntegral_segment_affineMap A.toContinuousLinearMap c 0 1 P Q,
    ← curveIntegral_segment_affineMap A.toContinuousLinearMap c 1 Complex.I P Q,
    ← curveIntegral_segment_affineMap A.toContinuousLinearMap c 0 Complex.I P Q, harea] at hbase
  have ht0 : affineMap A.toContinuousLinearMap c 0 = c := by
    rw [affineMap_apply, map_zero, zero_add]
  have ht1 : affineMap A.toContinuousLinearMap c 1 = p := by
    rw [affineMap_apply, ContinuousLinearEquiv.coe_coe, triangleCoordinates_one, sub_add_cancel]
  have htI : affineMap A.toContinuousLinearMap c Complex.I = q := by
    rw [affineMap_apply, ContinuousLinearEquiv.coe_coe, triangleCoordinates_I, sub_add_cancel]
  rw [ht0, ht1, htI] at hbase
  exact hbase.2

end TauCeti.Green
