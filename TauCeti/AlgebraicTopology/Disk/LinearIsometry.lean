/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Topology.Algebra.OrthogonalGroup
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Topology.Homotopy.LinearIsometryEquiv

/-!
# Orthogonal maps of the Euclidean disk

A linear isometry `g` of `ℝⁿ` maps the closed unit disk `TopCat.disk n` onto itself and its
boundary sphere `TopCat.diskBoundary n` onto itself. This file bundles these restrictions as
`LinearIsometryEquiv.diskMap g` and `LinearIsometryEquiv.diskBoundaryMap g`. The disk map is a map
of pairs `(D^n, ∂D^n) → (D^n, ∂D^n)`, and on the boundary sphere it is the boundary map.

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
(`TauCeti.TopCat.diskBoundaryMap_eq_diskBoundaryNeg_of_det_eq_neg_one`).

## Main declarations

* `LinearIsometryEquiv.diskMap`, `LinearIsometryEquiv.diskBoundaryMap`: the maps of the disk and of
  its boundary sphere induced by a linear isometry of `ℝⁿ`; the boundary map of `-1` is the
  antipodal map `TauCeti.diskBoundaryNeg` (`LinearIsometryEquiv.diskBoundaryMap_neg`).
* `TauCeti.TopCat.exists_homotopy_diskMap_id_of_det_eq_one`: for `det g = 1`, the disk map is
  homotopic to the identity through maps of pairs.
* `TauCeti.TopCat.homotopic_diskBoundaryMap_id_of_det_eq_one`: for `det g = 1`, the boundary map
  is homotopic to the identity.
* `TauCeti.TopCat.exists_homotopy_diskMap_comp_of_det_eq_one`: for `det g = 1`, precomposing a map
  of pairs with the disk map does not change its homotopy class as a map of pairs.
* `TauCeti.TopCat.diskMap_eq_id_of_det_eq_one`,
  `TauCeti.TopCat.diskBoundaryMap_eq_diskBoundaryNeg_of_det_eq_neg_one`: the two orthogonal maps
  of `D¹`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Remark 3.3.
-/

public section

noncomputable section

open Set Metric CategoryTheory unitInterval

universe u

namespace LinearIsometryEquiv

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
    ((g.diskMap w).down : EuclideanSpace ℝ (Fin n)) = g w.down :=
  (rfl)

@[simp]
theorem coe_diskBoundaryMap_apply_down (s : TopCat.diskBoundary.{u} n) :
    ((g.diskBoundaryMap s).down : EuclideanSpace ℝ (Fin n)) = g s.down :=
  (rfl)

/-- On the boundary sphere, the disk map of `g` is the boundary map of `g`. -/
@[reassoc]
theorem diskBoundaryMap_comp_diskBoundaryInclusion :
    diskBoundaryMap.{u} g ≫ TopCat.diskBoundaryInclusion n =
      TopCat.diskBoundaryInclusion n ≫ g.diskMap := by
  ext s
  exact ULift.ext (Subtype.ext (by simp [TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down]))

/-- The pointwise form of `LinearIsometryEquiv.diskBoundaryMap_comp_diskBoundaryInclusion`. -/
theorem diskMap_diskBoundaryInclusion (s : TopCat.diskBoundary.{u} n) :
    g.diskMap (TopCat.diskBoundaryInclusion n s) =
      TopCat.diskBoundaryInclusion n (g.diskBoundaryMap s) :=
  (ConcreteCategory.congr_hom (diskBoundaryMap_comp_diskBoundaryInclusion g) s).symm

/-- The disk map of `g` is a map of pairs `(D^n, ∂D^n) → (D^n, ∂D^n)`. -/
theorem mapsTo_diskMap_range_diskBoundaryInclusion :
    MapsTo (diskMap.{u} g) (range (TopCat.diskBoundaryInclusion n))
      (range (TopCat.diskBoundaryInclusion n)) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨g.diskBoundaryMap s, (diskMap_diskBoundaryInclusion g s).symm⟩

@[simp]
theorem diskMap_refl : diskMap.{u} (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) = 𝟙 _ :=
  (rfl)

@[simp]
theorem diskBoundaryMap_refl :
    diskBoundaryMap.{u} (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) = 𝟙 _ :=
  (rfl)

@[simp]
theorem diskMap_trans : diskMap.{u} (g.trans g') = g.diskMap ≫ g'.diskMap :=
  (rfl)

@[simp]
theorem diskBoundaryMap_trans :
    diskBoundaryMap.{u} (g.trans g') = g.diskBoundaryMap ≫ g'.diskBoundaryMap :=
  (rfl)

/-- The boundary map of `-1` is the antipodal map of the sphere. -/
@[simp]
theorem diskBoundaryMap_neg :
    diskBoundaryMap.{u} (LinearIsometryEquiv.neg ℝ) = TauCeti.diskBoundaryNeg n := by
  ext s
  exact ULift.ext (Subtype.ext (by simp))

end LinearIsometryEquiv

namespace TauCeti.TopCat

variable {n : ℕ}

section Rotation

variable {g : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)}

/-- **An orientation-preserving orthogonal map of a disk is homotopic to the identity through maps
of pairs.** If `det g = 1`, there is a homotopy from the disk map of `g` to the identity of
`TopCat.disk n` which keeps the boundary sphere in itself at all times. The homotopy is
`(t, w) ↦ γ t w` for a path `γ` from `g` to the identity in the special orthogonal group. -/
theorem exists_homotopy_diskMap_id_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1) :
    ∃ H : (LinearIsometryEquiv.diskMap.{u} g).hom.Homotopy (ContinuousMap.id _),
      ∀ t (s : TopCat.diskBoundary.{u} n), H (t, TopCat.diskBoundaryInclusion n s) ∈
        range (TopCat.diskBoundaryInclusion n) := by
  obtain ⟨γ, hγ, h0, h1⟩ :=
    exists_path_linearIsometryEquiv_of_det_eq (g' := .refl ℝ _) <| hg.trans LinearMap.det_id.symm
  refine ⟨linearIsometryEquivPathHomotopy (S := closedBall 0 1)
    (fun t x hx ↦ by simpa using hx) hγ (f₀ := (LinearIsometryEquiv.diskMap.{u} g).hom)
    (f₁ := ContinuousMap.id _)
    (fun w ↦ (LinearIsometryEquiv.coe_diskMap_apply_down g w).trans (by rw [h0]))
    (fun w ↦ by simp [h1]), fun t s ↦ ?_⟩
  rw [mem_range_diskBoundaryInclusion_iff]
  refine (congrArg norm (coe_linearIsometryEquivPathHomotopy_apply_down _ _ _ _ (t, _))).trans ?_
  rw [LinearIsometryEquiv.norm_map, coe_diskBoundaryInclusion_apply_down]
  exact mem_sphere_zero_iff_norm.1 s.down.2

/-- **An orientation-preserving orthogonal map of a sphere is homotopic to the identity.** If
`det g = 1`, the boundary map of `g` is homotopic to the identity of `TopCat.diskBoundary n`. -/
theorem homotopic_diskBoundaryMap_id_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1) :
    (LinearIsometryEquiv.diskBoundaryMap.{u} g).hom.Homotopic (ContinuousMap.id _) := by
  obtain ⟨γ, hγ, h0, h1⟩ :=
    exists_path_linearIsometryEquiv_of_det_eq (g' := .refl ℝ _) <| hg.trans LinearMap.det_id.symm
  exact ⟨linearIsometryEquivPathHomotopy (S := sphere 0 1) (fun t x hx ↦ by simpa using hx) hγ
    (f₀ := (LinearIsometryEquiv.diskBoundaryMap.{u} g).hom) (f₁ := ContinuousMap.id _)
    (fun s ↦ (LinearIsometryEquiv.coe_diskBoundaryMap_apply_down g s).trans (by rw [h0]))
    (fun s ↦ by simp [h1])⟩

/-- **Precomposing with an orientation-preserving orthogonal map does not change a map of pairs
up to homotopy.** If `det g = 1` and `χ : D^n → X` sends the boundary sphere into `S`, then the
composite of the disk map of `g` with `χ` is homotopic to `χ` by a homotopy which keeps the
boundary sphere in `S` at all times. -/
theorem exists_homotopy_diskMap_comp_of_det_eq_one (hg : LinearMap.det g.toLinearMap = 1)
    {X : TopCat.{u}} (χ : TopCat.disk.{u} n ⟶ X) {S : Set X}
    (hχ : ∀ s, χ (TopCat.diskBoundaryInclusion n s) ∈ S) :
    ∃ H : (g.diskMap ≫ χ).hom.Homotopy χ.hom,
      ∀ t (s : TopCat.diskBoundary.{u} n), H (t, TopCat.diskBoundaryInclusion n s) ∈ S := by
  obtain ⟨H, hH⟩ := exists_homotopy_diskMap_id_of_det_eq_one hg
  refine ⟨(ContinuousMap.Homotopy.refl χ.hom).comp H, fun t s ↦ ?_⟩
  obtain ⟨s', hs'⟩ := hH t s
  have h := hχ s'
  rw [hs'] at h
  exact h

end Rotation

section DimensionOne

variable {e : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1)}

/-- **An orientation-preserving orthogonal map of `D¹` is the identity.** -/
theorem diskMap_eq_id_of_det_eq_one (he : LinearMap.det e.toLinearMap = 1) :
    LinearIsometryEquiv.diskMap.{u} e = 𝟙 _ := by
  rw [LinearIsometryEquiv.eq_refl_of_det_eq_one finrank_euclideanSpace_fin he,
    LinearIsometryEquiv.diskMap_refl]

/-- **An orientation-reversing orthogonal map of `D¹` swaps the two boundary points.** If
`det e = -1`, the boundary map of `e` is the antipodal map of the sphere `∂D¹ = {-1, 1}`. -/
theorem diskBoundaryMap_eq_diskBoundaryNeg_of_det_eq_neg_one
    (he : LinearMap.det e.toLinearMap = -1) :
    LinearIsometryEquiv.diskBoundaryMap.{u} e = diskBoundaryNeg 1 := by
  rw [LinearIsometryEquiv.eq_neg_of_det_eq_neg_one finrank_euclideanSpace_fin he,
    LinearIsometryEquiv.diskBoundaryMap_neg]

end DimensionOne

end TauCeti.TopCat
