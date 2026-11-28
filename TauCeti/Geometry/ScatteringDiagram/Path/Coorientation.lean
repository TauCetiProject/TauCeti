/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Product
import TauCeti.Algebra.Group.Pow

/-!
# Changes of coorientation for wall transport

Positive rescaling of the normals preserves event, segment, and path transport.
Independent nonzero signed rescalings preserve transport when every normal's kernel
lies in its wall's affine-span direction and the labels are inverted at the negatively
rescaled indices. This includes several coincident walls at one crossing.
-/

public section

open Set

namespace TauCeti.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) =
    affineSpan ℝ (W j) → Commute (label i) (label j))

include hcomm in
/-- Inverting any subset of the labels preserves commutation for walls with equal affine spans. -/
theorem commute_coorientationLabels (r : ι → ℝ) (i j : ι)
    (h : affineSpan ℝ (W i) = affineSpan ℝ (W j)) :
    Commute (if 0 < r i then label i else (label i)⁻¹)
      (if 0 < r j then label j else (label j)⁻¹) := by
  split_ifs
  · exact hcomm i j h
  · exact (hcomm i j h).inv_right
  · exact (hcomm i j h).inv_left
  · exact (hcomm i j h).inv_inv

variable [Finite ι]

variable {x y : WallComplement W}

/-- Positive rescalings of the normals preserve the simultaneous event product. -/
@[simp]
theorem crossingEventProduct_smul_pos (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (e : x ⟶ y) (t : ℝ) :
    crossingEventProduct (fun i => r i • ν i) label hcomm e t =
      crossingEventProduct ν label hcomm e t := by
  rw [crossingEventProduct_eq_noncommProd _ _ _ e t
    (signedCrossingEvent_pairwise (fun i => r i • ν i) label hcomm e t),
    crossingEventProduct_eq_noncommProd ν label hcomm e t
      (signedCrossingEvent_pairwise ν label hcomm e t)]
  exact Finset.noncommProd_congr (signedCrossingEvent_smul ν r hr x y t) (fun _ _ => rfl) _

/-- Positive rescalings of the normals preserve segment transport. -/
@[simp]
theorem segmentPathProduct_smul_pos (r : ι → ℝ) (hr : ∀ i, 0 < r i) (e : x ⟶ y) :
    segmentPathProduct (fun i => r i • ν i) label hcomm e =
      segmentPathProduct ν label hcomm e := by
  simp only [segmentPathProduct_def]
  congr 1
  exact List.map_congr_left fun t _ => crossingEventProduct_smul_pos ν label hcomm r hr e t

/-- Independent nonzero rescalings preserve a simultaneous crossing product when the labels of
negatively rescaled walls are inverted and each normal's kernel lies in its wall's affine-span
direction. -/
@[simp]
theorem crossingEventProduct_smul_coorientation
    (hν : ∀ i, LinearMap.ker (ν i) ≤ (affineSpan ℝ (W i)).direction)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (e : x ⟶ y) (t : ℝ) :
    crossingEventProduct (fun i => r i • ν i) (fun i => if 0 < r i then label i else (label i)⁻¹)
        (commute_coorientationLabels label hcomm r) e t =
      crossingEventProduct ν label hcomm e t := by
  rw [crossingEventProduct_eq_crossingWalls
    (fun i => r i • ν i) (fun i => if 0 < r i then label i else (label i)⁻¹)
    (commute_coorientationLabels label hcomm r) e t,
    crossingEventProduct_eq_crossingWalls ν label hcomm e t]
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  have hv := e.down.apply_sub_ne_zero_of_mem_crossings
    ((mem_crossingWalls x y t i).mp hi) (hν i)
  simpa only [LinearMap.smul_apply, smul_eq_mul] using ite_inv_zpow_ite_mul_pos hv (hr i) (label i)

/-- Independent nonzero rescalings preserve segment transport when each negatively rescaled wall
carries the inverse label and each normal's kernel lies in its wall's affine-span direction. -/
@[simp]
theorem segmentPathProduct_smul_coorientation
    (hν : ∀ i, LinearMap.ker (ν i) ≤ (affineSpan ℝ (W i)).direction)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (e : x ⟶ y) :
    segmentPathProduct (fun i => r i • ν i) (fun i => if 0 < r i then label i else (label i)⁻¹)
        (commute_coorientationLabels label hcomm r) e =
      segmentPathProduct ν label hcomm e := by
  simp only [segmentPathProduct_def]
  congr 1
  exact List.map_congr_left fun t _ => crossingEventProduct_smul_coorientation ν label hcomm
    hν r hr e t

end TauCeti.WallComplement

namespace Quiver.Path

open TauCeti WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) =
    affineSpan ℝ (W j) → Commute (label i) (label j))
  {x y : WallComplement W}

/-- Positive rescaling of the individual normal representatives leaves polygonal wall
transport unchanged. -/
@[simp]
theorem wallPathProduct_smul_pos (r : ι → ℝ) (hr : ∀ i, 0 < r i) (p : AdmissiblePLPath x y) :
    p.wallPathProduct (fun i => r i • ν i) label hcomm = p.wallPathProduct ν label hcomm := by
  rw [wallPathProduct_eq_prod_signedCrossingEvents, wallPathProduct_eq_prod_signedCrossingEvents,
    signedCrossingEvents_smul _ _ hr]

/-- Independent nonzero rescalings preserve polygonal transport when the labels of negatively
rescaled walls are inverted and each normal's kernel lies in its wall's affine-span direction. -/
@[simp]
theorem wallPathProduct_smul_coorientation
    (hν : ∀ i, LinearMap.ker (ν i) ≤ (affineSpan ℝ (W i)).direction)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (p : AdmissiblePLPath x y) :
    p.wallPathProduct (fun i => r i • ν i) (fun i => if 0 < r i then label i else (label i)⁻¹)
        (commute_coorientationLabels label hcomm r) =
      p.wallPathProduct ν label hcomm := by
  induction p with
  | nil => simp
  | cons p e ih => simp only [wallPathProduct_cons, ih,
      segmentPathProduct_smul_coorientation ν label hcomm hν r hr]

end Quiver.Path
