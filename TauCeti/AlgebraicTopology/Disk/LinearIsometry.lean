/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.LinearAlgebra.OrthogonalGroup
import TauCeti.Topology.Algebra.OrthogonalGroup
import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# Orthogonal maps of the Euclidean disk

A linear isometry `g` of `ℝⁿ` maps the closed unit disk `TopCat.disk n` onto itself and its
boundary sphere `TopCat.diskBoundary n` onto itself. This file bundles these restrictions as
`TauCeti.TopCat.diskMap g` and `TauCeti.TopCat.diskBoundaryMap g`. The disk map is a map of pairs
`(D^n, ∂D^n) → (D^n, ∂D^n)`, and on the boundary sphere it is the boundary map.

When `g` preserves orientation, that is `det g = 1`, it is joined to the identity in the special
orthogonal group, so the disk map is homotopic to the identity through maps of pairs
(`TauCeti.TopCat.exists_homotopy_diskMap_id_of_det_eq_one`). Its boundary map is homotopic to the
identity of the sphere, and the composite of a map of pairs out of the disk with it is homotopic
to that map, keeping the boundary sphere where the map sends it
(`TauCeti.TopCat.exists_homotopy_diskMap_comp_of_det_eq_one`). This is how an orthogonal change
of parametrization of an attached cell is removed up to homotopy: the comparison of two Morse
charts at a critical point of index `λ` changes the characteristic map of the cell by the polar
factor of the transition, an orthogonal map of `ℝ^λ`.

In dimension `1` there are only two orthogonal maps. If `det g = 1` then `g` is the identity, so
its disk map is the identity (`TauCeti.TopCat.diskMap_eq_id_of_det_eq_one`); if `det g = -1` then
`g = -1`, and its boundary map swaps the two points of the sphere `∂D¹ = {-1, 1}`
(`TauCeti.TopCat.diskBoundaryMap_eq_diskBoundaryNeg`).

## Main declarations

* `TauCeti.TopCat.diskMap`, `TauCeti.TopCat.diskBoundaryMap`: the maps of the disk and of its
  boundary sphere induced by a linear isometry of `ℝⁿ`; the boundary map of `-1` is the antipodal
  map `TauCeti.diskBoundaryNeg` (`TauCeti.TopCat.diskBoundaryMap_neg`).
* `TauCeti.TopCat.exists_homotopy_diskMap_id_of_det_eq_one`: for `det g = 1`, the disk map is
  homotopic to the identity through maps of pairs.
* `TauCeti.TopCat.homotopic_diskBoundaryMap_id_of_det_eq_one`: for `det g = 1`, the boundary map
  is homotopic to the identity.
* `TauCeti.TopCat.exists_homotopy_diskMap_comp_of_det_eq_one`: for `det g = 1`, precomposing a map
  of pairs with the disk map does not change its homotopy class as a map of pairs.
* `TauCeti.TopCat.diskMap_eq_id_of_det_eq_one`, `TauCeti.TopCat.diskBoundaryMap_eq_diskBoundaryNeg`:
  the two orthogonal maps of `D¹`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Remark 3.3, where the cell attached at a critical point is determined up to such orthogonal
  changes of parametrization.
-/

public section

noncomputable section

open Set Metric CategoryTheory unitInterval

universe u

namespace TauCeti.TopCat

variable {n : ℕ} (g g' : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))

/-- The self-map `w ↦ g w` of the disk `TopCat.disk n` induced by a linear isometry `g` of `ℝⁿ`. -/
def diskMap : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n :=
  TopCat.ofHom
    { toFun w := ULift.up ⟨g w.down, mem_closedBall_zero_iff.2 <| (g.norm_map _).trans_le <|
        mem_closedBall_zero_iff.1 w.down.2⟩
      continuous_toFun := continuous_uliftUp.comp ((g.continuous.comp
        (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _) }

/-- The self-map `s ↦ g s` of the boundary sphere `TopCat.diskBoundary n` induced by a linear
isometry `g` of `ℝⁿ`. -/
def diskBoundaryMap : TopCat.diskBoundary.{u} n ⟶ TopCat.diskBoundary.{u} n :=
  TopCat.ofHom
    { toFun s := ULift.up ⟨g s.down, mem_sphere_zero_iff_norm.2 <| (g.norm_map _).trans <|
        mem_sphere_zero_iff_norm.1 s.down.2⟩
      continuous_toFun := continuous_uliftUp.comp ((g.continuous.comp
        (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _) }

@[simp]
theorem coe_diskMap_apply_down (w : TopCat.disk.{u} n) :
    ((diskMap g w).down : EuclideanSpace ℝ (Fin n)) = g w.down :=
  (rfl)

@[simp]
theorem coe_diskBoundaryMap_apply_down (s : TopCat.diskBoundary.{u} n) :
    ((diskBoundaryMap g s).down : EuclideanSpace ℝ (Fin n)) = g s.down :=
  (rfl)

/-- On the boundary sphere, the disk map of `g` is the boundary map of `g`. -/
@[reassoc]
theorem diskBoundaryMap_comp_diskBoundaryInclusion :
    diskBoundaryMap.{u} g ≫ TopCat.diskBoundaryInclusion n =
      TopCat.diskBoundaryInclusion n ≫ diskMap g := by
  ext s
  exact ULift.ext (Subtype.ext (by simp [coe_diskBoundaryInclusion_apply_down]))

/-- The pointwise form of `TauCeti.TopCat.diskBoundaryMap_comp_diskBoundaryInclusion`. -/
theorem diskMap_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} n) :
    diskMap g (TopCat.diskBoundaryInclusion n s) =
      TopCat.diskBoundaryInclusion n (diskBoundaryMap g s) :=
  (ConcreteCategory.congr_hom (diskBoundaryMap_comp_diskBoundaryInclusion g) s).symm

/-- The disk map of `g` is a map of pairs `(D^n, ∂D^n) → (D^n, ∂D^n)`. -/
theorem mapsTo_diskMap_range_diskBoundaryInclusion :
    MapsTo (diskMap.{u} g) (range (TopCat.diskBoundaryInclusion n))
      (range (TopCat.diskBoundaryInclusion n)) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨diskBoundaryMap g s, (diskMap_diskBoundaryInclusion g s).symm⟩

@[simp]
theorem diskMap_refl : diskMap.{u} (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) = 𝟙 _ :=
  (rfl)

@[simp]
theorem diskBoundaryMap_refl :
    diskBoundaryMap.{u} (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) = 𝟙 _ :=
  (rfl)

@[simp]
theorem diskMap_trans : diskMap.{u} (g.trans g') = diskMap g ≫ diskMap g' :=
  (rfl)

@[simp]
theorem diskBoundaryMap_trans :
    diskBoundaryMap.{u} (g.trans g') = diskBoundaryMap g ≫ diskBoundaryMap g' :=
  (rfl)

/-- The boundary map of `-1` is the antipodal map of the sphere. -/
@[simp]
theorem diskBoundaryMap_neg :
    diskBoundaryMap.{u} (LinearIsometryEquiv.neg ℝ) = diskBoundaryNeg n := by
  ext s
  exact ULift.ext (Subtype.ext (by simp))

section Rotation

/-- An orientation-preserving linear isometry of `ℝⁿ` is joined to the identity by a continuous
path of linear isometries, continuous in the operator-norm topology. -/
private theorem exists_path_linearIsometryEquiv (hg : LinearMap.det g.toLinearMap = 1) :
    ∃ γ : I → (EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
      Continuous (fun t ↦ ((γ t).toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∧
      γ 0 = g ∧ γ 1 = LinearIsometryEquiv.refl ℝ _ := by
  obtain ⟨A, rfl⟩ := orthogonalGroupToLinearIsometryEquiv_surjective g
  have hA : (A : Matrix (Fin n) (Fin n) ℝ).det = (1 : Matrix.orthogonalGroup (Fin n) ℝ).1.det := by
    rw [OneMemClass.coe_one, Matrix.det_one, ← det_orthogonalGroupToLinearIsometryEquiv]
    exact hg
  obtain ⟨p⟩ := Matrix.joined_orthogonalGroup_iff_det_eq.2 hA
  exact ⟨fun t ↦ orthogonalGroupToLinearIsometryEquiv (p t),
    continuous_orthogonalGroupToLinearIsometryEquiv.comp p.continuous,
    congrArg orthogonalGroupToLinearIsometryEquiv p.source,
    (congrArg orthogonalGroupToLinearIsometryEquiv p.target).trans (map_one _)⟩

variable {g}

/-- **An orientation-preserving orthogonal map of a disk is homotopic to the identity through maps
of pairs.** If `det g = 1`, there is a homotopy from the disk map of `g` to the identity of
`TopCat.disk n` which keeps the boundary sphere in itself at all times. The homotopy is
`(t, w) ↦ γ t w` for a path `γ` from `g` to the identity in the special orthogonal group. -/
theorem exists_homotopy_diskMap_id_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1) :
    ∃ H : (diskMap.{u} g).hom.Homotopy (ContinuousMap.id _),
      ∀ t (s : TopCat.diskBoundary.{u} n), H (t, TopCat.diskBoundaryInclusion n s) ∈
        range (TopCat.diskBoundaryInclusion n) := by
  obtain ⟨γ, hγ, h0, h1⟩ := exists_path_linearIsometryEquiv g hg
  let H : (diskMap.{u} g).hom.Homotopy (ContinuousMap.id _) :=
    { toFun p := ULift.up ⟨γ p.1 p.2.down, mem_closedBall_zero_iff.2 <|
        ((γ p.1).norm_map _).trans_le <| mem_closedBall_zero_iff.1 p.2.down.2⟩
      continuous_toFun := continuous_uliftUp.comp (((hγ.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))).subtype_mk _)
      map_zero_left w := ULift.ext (Subtype.ext (by simp [h0]))
      map_one_left w := ULift.ext (Subtype.ext (by simp [h1])) }
  have hH (p : I × TopCat.disk.{u} n) :
      ((H p).down : EuclideanSpace ℝ (Fin n)) = γ p.1 p.2.down :=
    (rfl)
  refine ⟨H, fun t s ↦ ?_⟩
  rw [mem_range_diskBoundaryInclusion_iff, hH, LinearIsometryEquiv.norm_map,
    coe_diskBoundaryInclusion_apply_down]
  exact mem_sphere_zero_iff_norm.1 s.down.2

/-- **An orientation-preserving orthogonal map of a sphere is homotopic to the identity.** If
`det g = 1`, the boundary map of `g` is homotopic to the identity of `TopCat.diskBoundary n`. -/
theorem homotopic_diskBoundaryMap_id_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1) :
    (diskBoundaryMap.{u} g).hom.Homotopic (ContinuousMap.id _) := by
  obtain ⟨γ, hγ, h0, h1⟩ := exists_path_linearIsometryEquiv g hg
  exact ⟨
    { toFun p := ULift.up ⟨γ p.1 p.2.down, mem_sphere_zero_iff_norm.2 <|
        ((γ p.1).norm_map _).trans <| mem_sphere_zero_iff_norm.1 p.2.down.2⟩
      continuous_toFun := continuous_uliftUp.comp (((hγ.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd))).subtype_mk _)
      map_zero_left s := ULift.ext (Subtype.ext (by simp [h0]))
      map_one_left s := ULift.ext (Subtype.ext (by simp [h1])) }⟩

/-- **Precomposing with an orientation-preserving orthogonal map does not change a map of pairs
up to homotopy.** If `det g = 1` and `χ : D^n → X` sends the boundary sphere into `S`, then the
composite of the disk map of `g` with `χ` is homotopic to `χ` by a homotopy which keeps the
boundary sphere in `S` at all times. -/
theorem exists_homotopy_diskMap_comp_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1)
    {X : TopCat.{u}} (χ : TopCat.disk.{u} n ⟶ X) {S : Set X}
    (hχ : ∀ s, χ (TopCat.diskBoundaryInclusion n s) ∈ S) :
    ∃ H : (diskMap g ≫ χ).hom.Homotopy χ.hom,
      ∀ t (s : TopCat.diskBoundary.{u} n), H (t, TopCat.diskBoundaryInclusion n s) ∈ S := by
  obtain ⟨H, hH⟩ := exists_homotopy_diskMap_id_of_det_eq_one hg
  refine ⟨
    { toFun p := χ (H p)
      continuous_toFun := χ.hom.continuous.comp H.continuous
      map_zero_left w := by simp
      map_one_left w := by simp }, fun t s ↦ ?_⟩
  obtain ⟨s', hs'⟩ := hH t s
  have h := hχ s'
  rw [hs'] at h
  exact h

end Rotation

section DimensionOne

variable {e : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)}

/-- **An orientation-preserving orthogonal map of `D¹` is the identity.** -/
theorem diskMap_eq_id_of_det_eq_one (he : LinearMap.det e.toLinearMap = 1) :
    diskMap.{u} e = 𝟙 _ := by
  rw [LinearIsometryEquiv.eq_refl_of_det_eq_one finrank_euclideanSpace_fin he, diskMap_refl]

/-- **An orientation-reversing orthogonal map of `D¹` swaps the two boundary points.** If
`det e = -1`, the boundary map of `e` is the antipodal map of the sphere `∂D¹ = {-1, 1}`. -/
theorem diskBoundaryMap_eq_diskBoundaryNeg (he : LinearMap.det e.toLinearMap = -1) :
    diskBoundaryMap.{u} e = diskBoundaryNeg 1 := by
  rw [LinearIsometryEquiv.eq_neg_of_det_eq_neg_one finrank_euclideanSpace_fin he,
    diskBoundaryMap_neg]

end DimensionOne

end TauCeti.TopCat
