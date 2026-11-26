/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Product

/-!
# Changes of coorientation for wall transport

Positive rescaling of the representative normal preserves transport. A negative rescaling
preserves it when the corresponding wall label is inverted. This applies independently to
each indexed wall, including several coincident walls at one crossing.
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
/-- Inverting any subset of the labels preserves commutation of labels on coplanar walls. -/
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

private theorem crossingEventProduct_eq_crossingWalls
    {x y : WallComplement W} (e : x ⟶ y) (t : ℝ) :
    ∃ h, crossingEventProduct ν label hcomm e t =
      (crossingWalls x y t).noncommProd
        (fun i => label i ^ (if 0 < ν i (y.val - x.val) then -1 else 1 : ℤ)) h := by
  classical
  let embed : ι ↪ ι × ℤ :=
    ⟨fun i => (i, if 0 < ν i (y.val - x.val) then -1 else 1), fun _ _ h => congrArg Prod.fst h⟩
  have hs : signedCrossingEvent ν x y t = (crossingWalls x y t).map embed := by
    rw [signedCrossingEvent_def, Finset.map_eq_image]
    rfl
  rw [crossingEventProduct_eq_noncommProd ν label hcomm e t
    (signedCrossingEvent_pairwise ν label hcomm e t)]
  exact ⟨_, (Finset.noncommProd_congr hs (fun _ _ => rfl) _).trans
    (Finset.noncommProd_map _ embed _ _)⟩

private theorem signedLabel_smul {v r : ℝ} (hv : v ≠ 0) (hr : r ≠ 0) (g : G) :
    (if 0 < r then g else g⁻¹) ^ (if 0 < r * v then -1 else 1 : ℤ) =
      g ^ (if 0 < v then -1 else 1 : ℤ) := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · rcases lt_or_gt_of_ne hv with hvneg | hvpos
    · simp [hneg.not_gt, hvneg.not_gt, mul_pos_of_neg_of_neg hneg hvneg]
    · simp [hneg.not_gt, hvpos, (mul_neg_of_neg_of_pos hneg hvpos).not_gt]
  · simp [hpos, mul_pos_iff_of_pos_left hpos]

variable {x y : WallComplement W}

/-- Independent nonzero rescalings preserve a simultaneous crossing product when labels
of the negatively rescaled walls are inverted. -/
theorem crossingEventProduct_smul_coorientation
    (hν : ∀ i, LinearMap.ker (ν i) ≤ (affineSpan ℝ (W i)).direction)
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (e : x ⟶ y) (t : ℝ) :
    crossingEventProduct (fun i => r i • ν i) (fun i => if 0 < r i then label i else (label i)⁻¹)
        (commute_coorientationLabels label hcomm r) e t =
      crossingEventProduct ν label hcomm e t := by
  obtain ⟨_, h₁⟩ := crossingEventProduct_eq_crossingWalls
    (fun i => r i • ν i) (fun i => if 0 < r i then label i else (label i)⁻¹)
      (commute_coorientationLabels label hcomm r) e t
  obtain ⟨_, h₂⟩ := crossingEventProduct_eq_crossingWalls ν label hcomm e t
  rw [h₁, h₂]
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  obtain ⟨ht, hm⟩ := (mem_crossings x y i t).mp ((mem_crossingWalls x y t i).mp hi)
  have hv : ν i (y.val - x.val) ≠ 0 := by
    intro hz
    apply e.down.transverse i ⟨t, ht, hm⟩
    exact hν i hz
  simpa only [LinearMap.smul_apply, smul_eq_mul] using signedLabel_smul hv (hr i) (label i)

/-- Independent changes of normal representative preserve segment transport when each
negatively rescaled wall carries the inverse label. -/
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
theorem wallPathProduct_smul_pos (r : ι → ℝ) (hr : ∀ i, 0 < r i) (p : AdmissiblePLPath x y) :
    p.wallPathProduct (fun i => r i • ν i) label hcomm = p.wallPathProduct ν label hcomm := by
  rw [wallPathProduct_eq_prod_signedCrossingEvents, wallPathProduct_eq_prod_signedCrossingEvents,
    signedCrossingEvents_smul _ _ hr]

/-- Any nonzero rescaling leaves transport unchanged if the labels of precisely the
negatively rescaled walls are inverted. -/
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
