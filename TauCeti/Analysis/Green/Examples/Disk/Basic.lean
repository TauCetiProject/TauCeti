/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
public import TauCeti.Analysis.Green.Examples.Disk.Boundary
public import TauCeti.Analysis.Green.Comparison.Loop
public import TauCeti.Geometry.Manifold.Orientation.ClosedBall

/-!
# Green's theorem on the actual closed-disk manifold

The disk's canonical orientation is normalized by its actual inclusion derivative. The circle
exponential gives a positive parametrization of its induced boundary, including the seam
coverage and actual derivative witnesses. Applying manifold Stokes and the area-image theorem
therefore gives the usual coordinate-area Green formula with no extra geometric premises.
-/

public section

noncomputable section

open Set Metric MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.Green

attribute [local instance] finrank_real_complex_fact'

local notation "D" => closedBall (0 : ℂ) 1
local notation "B" => ModelWithCorners.boundary (I := (𝓡∂ (1 + 1))) D
local notation "E₁" => EuclideanSpace ℝ (Fin 1)

local instance : IsManifold (𝓡 1) ω B := isManifold_boundary (n := 1) D (by simp)

/-- Green's formula on the actual closed-disk manifold and its counterclockwise induced
boundary. Both integrabilities follow from the global manifold comparison theorem. -/
theorem green_unitDisk (P Q : ℂ → ℝ) (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    IntegrableOn (curl P Q) (closedBall (0 : ℂ) 1) ∧
      CurveIntegrable (oneForm P Q)
        (unitDiskBoundaryLoop.map (continuous_subtype_val.comp continuous_subtype_val)) ∧
      (∫ z in closedBall (0 : ℂ) 1, curl P Q z) =
        curveIntegral (oneForm P Q)
          (unitDiskBoundaryLoop.map (continuous_subtype_val.comp continuous_subtype_val)) := by
  classical
  let o := Manifold.Orientation.closedBall (n := 2) Complex.basisOneI.orientation
  have hparam (z : E₁) : ∃ e : E₁ ≃L[ℝ] TangentSpace (𝓡 1)
      (unitDiskBoundaryLoop.extend (z 0)), ∀ hz : z 0 ∈ Ioo (0 : ℝ) 1,
      HasMFDerivAt (𝓡 1) (𝓡 1) (fun w : E₁ ↦ unitDiskBoundaryLoop.extend (w 0)) z
        (e.toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap) ∧
      Orientation.map (Fin 1) e.toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
        (boundaryOrientation o).orientationAt (unitDiskBoundaryLoop.extend (z 0)) := by
    by_cases hz : z 0 ∈ Ioo (0 : ℝ) 1
    · obtain ⟨e, hd, ho⟩ := exists_unitDiskBoundaryLoop_positive_tangentEquiv
        o (Manifold.Orientation.map_orientationAt_closedBall (n := 2)
          Complex.basisOneI.orientation) z hz
      exact ⟨e, fun _ ↦ ⟨hd, ho⟩⟩
    · exact ⟨(tangentSpaceCastModel (𝓡 1) (unitDiskBoundaryLoop.extend (z 0))).symm,
        fun h ↦ (hz h).elim⟩
  choose e he using hparam
  let F : D → EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
    fun x ↦ subtypeValClosedBallTangentEquiv (n := 2) x
  have hFo (x : D) : Orientation.map (Fin 2) (F x).toLinearEquiv
      -- The orientation comparison uses the fixed Euclidean model of each disk tangent fiber.
      (show Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) from
        o.orientationAt x) = Complex.orientation := by
    exact Manifold.Orientation.map_orientationAt_closedBall (n := 2) Complex.basisOneI.orientation x
  have h := integral_image_curl_eq_boundary_curveIntegral o (Subtype.val : D → ℂ)
    (contMDiff_subtypeVal_closedBall (n := 2) (k := 2))
    Subtype.val_injective F
    (fun x ↦ subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := 2) x)
    hFo P Q univ isOpen_univ (subset_univ _) hP.contDiffOn hQ.contDiffOn
    unitDiskBoundaryLoop unitDiskBoundaryLoop_image
    unitDiskBoundaryLoop_injOn e (fun z hz ↦ (he z hz).1) (fun z hz ↦ (he z hz).2)
  simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using h

/-- The area form on the actual counterclockwise disk boundary integrates to `π`. -/
theorem curveIntegral_unitDisk_area :
    curveIntegral (oneForm Examples.areaP Examples.areaQ)
      (unitDiskBoundaryLoop.map (continuous_subtype_val.comp continuous_subtype_val)) =
      Real.pi := by
  have h := (green_unitDisk Examples.areaP Examples.areaQ
    Examples.contDiff_areaP Examples.contDiff_areaQ).2.2.symm
  simpa [Examples.curl_area, Measure.real, Complex.volume_closedBall, Real.pi_pos.le] using h

end TauCeti.Green
