/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cube
public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# Orientations on unit cubes, affine cube images, and affine facets

`TauCeti.unitCubeOrientation` is the canonical orientation of `Icc (0 : ι → ℝ) 1` determined by
`Pi.basisFun ℝ ι`, and `ContinuousLinearMap.unitCubeImageOrientation` is the `s`-signed parameter
orientation on an injective affine cube `(fun u ↦ q₀ + M u) '' Icc 0 1`. On each `(j, b)`-facet of
`(fun w ↦ p + L w) '' Icc 0 1`, `ContinuousLinearEquiv.affineFacetOrientation` uses sign
`TauCeti.affineFacetSign`; when `0 < det L`, a facet tangent basis has this orientation iff
prepending `affineFacetOutward` gives a positive determinant
(`ContinuousLinearEquiv.orientation_eq_affineFacetOrientation_iff_det_pos`).

## Main declarations

* `TauCeti.unitCubeOrientation`, `TauCeti.map_orientationAt_unitCubeOrientation`.
* `ContinuousLinearMap.unitCubeImageOrientation`,
  `ContinuousLinearMap.map_orientationAt_unitCubeImageOrientation`.
* `ContinuousLinearEquiv.affineFacetOrientation`,
  `ContinuousLinearEquiv.orientation_eq_affineFacetOrientation_iff_det_pos`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 15–16.
-/

public section

noncomputable section

open Set Function
open scoped Manifold

namespace TauCeti

section UnitCubeOrientation

variable (ι : Type*) [Fintype ι]

/-- The canonical orientation lift on the closed unit cube `Icc (0 : ι → ℝ) 1`, with model
orientation `(Pi.basisFun ℝ ι).orientation` and chart sign `1`. -/
def unitCubeOrientationLift :
    Manifold.OrientationLift (modelWithCornersUnitCube ι) (Icc (0 : ι → ℝ) 1) ι :=
  open scoped Classical in
  Manifold.OrientationLift.ofHasGroupoid (Pi.basisFun ℝ ι).orientation (by simp)

/-- The canonical coordinate orientation of the closed unit cube `Icc (0 : ι → ℝ) 1`. -/
def unitCubeOrientation :
    Manifold.Orientation (modelWithCornersUnitCube ι) (Icc (0 : ι → ℝ) 1) ι :=
  Manifold.Orientation.mk (unitCubeOrientationLift ι)

theorem unitCubeOrientation_eq_mk :
    unitCubeOrientation ι = Manifold.Orientation.mk (unitCubeOrientationLift ι) := (rfl)

variable {ι}

@[simp]
theorem unitCubeOrientationLift_modelOrientation [DecidableEq ι] :
    (unitCubeOrientationLift ι).modelOrientation = (Pi.basisFun ℝ ι).orientation := by
  simp only [unitCubeOrientationLift, Manifold.OrientationLift.ofHasGroupoid_modelOrientation]
  congr!

@[simp]
theorem unitCubeOrientationLift_signAt (α x : Icc (0 : ι → ℝ) 1) :
    (unitCubeOrientationLift ι).signAt α x = 1 := by
  have hx : x ∈ (chartAt (Icc (0 : ι → ℝ) 1) α).source := by simp
  rw [Manifold.OrientationLift.signAt_of_mem _ hx, unitCubeOrientationLift,
    Manifold.OrientationLift.ofHasGroupoid_sign]

/-- At every point of the closed unit cube, including faces, edges, and corners, the canonical
tangent orientation read in the model space is `(Pi.basisFun ℝ ι).orientation`. -/
theorem map_orientationAt_unitCubeOrientation [DecidableEq ι] (x : Icc (0 : ι → ℝ) 1) :
    _root_.Orientation.map ι (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toLinearEquiv
      ((unitCubeOrientation ι).orientationAt x) = (Pi.basisFun ℝ ι).orientation := by
  have hsign : (unitCubeOrientationLift ι).sign x ⟨x, mem_chart_source _ x⟩ = 1 := by
    rw [unitCubeOrientationLift, Manifold.OrientationLift.ofHasGroupoid_sign]
  rw [unitCubeOrientation, Manifold.Orientation.map_tangentSpaceCastModel_orientationAt_mk, hsign,
    unitCubeOrientationLift_modelOrientation]
  simp

end UnitCubeOrientation

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] (M : (ι → ℝ) →L[ℝ] E)

/-- The `s`-signed parameter orientation lift on `(fun u ↦ q₀ + M u) '' Icc 0 1`, with model
orientation `(Pi.basisFun ℝ ι).orientation` and constant chart sign `s : ℤˣ`. -/
def unitCubeImageOrientationLift (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    Manifold.OrientationLift (modelWithCornersUnitCube ι)
      ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) ι :=
  letI := M.unitCubeImageChartedSpace hM q₀
  letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  letI := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  open scoped Classical in
  let l₀ := Manifold.OrientationLift.ofHasGroupoid (I := modelWithCornersUnitCube ι)
    (M := ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) (Pi.basisFun ℝ ι).orientation (by simp)
  if s = 1 then l₀ else (-l₀).flip

/-- The `s`-signed parameter orientation on `(fun u ↦ q₀ + M u) '' Icc 0 1`. -/
def unitCubeImageOrientation (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    Manifold.Orientation (modelWithCornersUnitCube ι) ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) ι :=
  letI := M.unitCubeImageChartedSpace hM q₀
  Manifold.Orientation.mk (M.unitCubeImageOrientationLift hM q₀ s)

theorem unitCubeImageOrientation_eq_mk (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    M.unitCubeImageOrientation hM q₀ s =
      Manifold.Orientation.mk (M.unitCubeImageOrientationLift hM q₀ s) := (rfl)

theorem unitCubeImageOrientationLift_modelOrientation [DecidableEq ι] (hM : Injective M) (q₀ : E)
    (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (M.unitCubeImageOrientationLift hM q₀ s).modelOrientation = (Pi.basisFun ℝ ι).orientation := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  dsimp only [unitCubeImageOrientationLift]
  split_ifs
  · simp only [Manifold.OrientationLift.ofHasGroupoid_modelOrientation]; congr!
  · simp only [Manifold.OrientationLift.flip_modelOrientation,
      Manifold.OrientationLift.neg_modelOrientation,
      Manifold.OrientationLift.ofHasGroupoid_modelOrientation]
    refine (_root_.neg_neg (G := _root_.Orientation ℝ (ι → ℝ) ι) _).trans ?_; congr!

theorem unitCubeImageOrientationLift_sign (hM : Injective M) (q₀ : E) (s : ℤˣ)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1))
    (x : (letI := M.unitCubeImageChartedSpace hM q₀; (chartAt (Icc (0 : ι → ℝ) 1) α).source)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (M.unitCubeImageOrientationLift hM q₀ s).sign α x = s := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  dsimp only [unitCubeImageOrientationLift]
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

theorem unitCubeImageOrientationLift_signAt (hM : Injective M) (q₀ : E) (s : ℤˣ)
    (α x : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (M.unitCubeImageOrientationLift hM q₀ s).signAt α x = s := by
  let := M.unitCubeImageChartedSpace hM q₀
  have hx : x ∈ (chartAt (Icc (0 : ι → ℝ) 1) α).source := by
    simp [M.chartAt_unitCubeImage_source hM q₀ α]
  exact (Manifold.OrientationLift.signAt_of_mem _ hx).trans
    (M.unitCubeImageOrientationLift_sign hM q₀ s α ⟨x, hx⟩)

theorem unitCubeImageOrientation_neg (hM : Injective M) (q₀ : E) (s : ℤˣ) :
    letI := M.unitCubeImageChartedSpace hM q₀
    M.unitCubeImageOrientation hM q₀ (-s) = -(M.unitCubeImageOrientation hM q₀ s) := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  let := M.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace hM q₀
  have h1 : M.unitCubeImageOrientation hM q₀ (-1) = -(M.unitCubeImageOrientation hM q₀ 1) := by
    dsimp only [unitCubeImageOrientation, unitCubeImageOrientationLift]
    have hn : (-1 : ℤˣ) ≠ 1 := by decide
    simp [hn, Manifold.Orientation.mk_eq_mk_iff (I := modelWithCornersUnitCube ι)]
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact h1
  · rw [_root_.neg_neg, h1, _root_.neg_neg]

/-- At every point of `(fun u ↦ q₀ + M u) '' Icc 0 1`, including faces, edges, and corners, the
tangent orientation of `M.unitCubeImageOrientation hM q₀ s` read in the model space `ι → ℝ` is
`(Pi.basisFun ℝ ι).orientation` when `s = 1` and its negation when `s = -1`. -/
theorem map_orientationAt_unitCubeImageOrientation [DecidableEq ι] (hM : Injective M) (q₀ : E)
    (s : ℤˣ) (x : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    letI := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
    _root_.Orientation.map ι (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toLinearEquiv
      ((M.unitCubeImageOrientation hM q₀ s).orientationAt x) =
      if s = 1 then (Pi.basisFun ℝ ι).orientation else -(Pi.basisFun ℝ ι).orientation := by
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  rw [unitCubeImageOrientation, Manifold.Orientation.map_tangentSpaceCastModel_orientationAt_mk,
    M.unitCubeImageOrientationLift_sign hM q₀ s x ⟨x, mem_chart_source _ x⟩,
    M.unitCubeImageOrientationLift_modelOrientation hM q₀ s]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open ContinuousLinearMap TauCeti

/-- The outward-signed orientation on the `(j, b)`-facet of `w ↦ p + L w`. When `E = Fin (n + 1) →
ℝ` and `0 < det L`, this is the geometric outward-first orientation
(`orientation_eq_affineFacetOrientation_iff_det_pos`). -/
def affineFacetOrientation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] E) (p : E) (j : Fin (n + 1)) (b : Bool) :
    letI := L.affineFacetChartedSpace p j b
    Manifold.Orientation (modelWithCornersUnitCube (Fin n))
      ↥((fun u : Fin n → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1) (Fin n) :=
  (L.toContinuousLinearMap.affineFacetLinearMap j).unitCubeImageOrientation
    (L.injective_affineFacetLinearMap j)
    (L.toContinuousLinearMap.affineFacetBase p j b) (affineFacetSign j b)

theorem affineFacetOrientation_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] E) (p : E) (j : Fin (n + 1)) (b : Bool) :
    L.affineFacetOrientation p j b =
      (L.toContinuousLinearMap.affineFacetLinearMap j).unitCubeImageOrientation
        (L.injective_affineFacetLinearMap j)
        (L.toContinuousLinearMap.affineFacetBase p j b) (affineFacetSign j b) := (rfl)

/-- **Outward-first geometric characterization of `affineFacetOrientation`.** When `0 < det L`, a
tangent basis `v` at any point `x` of the `(j, b)`-facet (including ridges and vertices) has the
facet orientation if and only if prepending the outward vector `affineFacetOutward L j b` to the
pushforward tangent frame produces a positive `(n + 1) × (n + 1)` determinant. -/
theorem orientation_eq_affineFacetOrientation_iff_det_pos {n : ℕ}
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (p : Fin (n + 1) → ℝ)
    (hL : 0 < LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ))
    (j : Fin (n + 1)) (b : Bool) :
    letI := L.affineFacetChartedSpace p j b
    letI := L.isManifold_affineFacetChartedSpace p j b 1
    ∀ (x : ↥((fun u : Fin n → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1))
      (v : Module.Basis (Fin n) ℝ (TangentSpace (modelWithCornersUnitCube (Fin n)) x)),
      v.orientation = (L.affineFacetOrientation p j b).orientationAt x ↔
        0 < (Matrix.of (Fin.cons (L.toContinuousLinearMap.affineFacetOutward j b)
          (fun r ↦ NormedSpace.fromTangentSpace x.val
            (mfderiv (modelWithCornersUnitCube (Fin n)) 𝓘(ℝ, Fin (n + 1) → ℝ)
              Subtype.val x (v r))))).det := by
  let M := L.toContinuousLinearMap.affineFacetLinearMap j
  let hM := L.injective_affineFacetLinearMap j
  let q₀ := L.toContinuousLinearMap.affineFacetBase p j b
  let := M.unitCubeImageChartedSpace hM q₀
  let := M.isManifold_unitCubeImageChartedSpace hM q₀ 1
  intro x v
  let e := (tangentSpaceCastModel (modelWithCornersUnitCube (Fin n)) x).toLinearEquiv
  let w : Module.Basis (Fin n) ℝ (Fin n → ℝ) := v.map e
  let b₀ := Pi.basisFun ℝ (Fin n)
  have hmf (r : Fin n) : NormedSpace.fromTangentSpace x.val
      (mfderiv (modelWithCornersUnitCube (Fin n)) 𝓘(ℝ, Fin (n + 1) → ℝ) Subtype.val x (v r)) =
      M (w r) := by rw [M.mfderiv_subtypeVal_unitCubeImage hM q₀ x]; simp [w, e]
  simp_rw [hmf]
  rw [L.toContinuousLinearMap.det_cons_affineFacetOutward_affineFacetLinearMap j b w,
    ← Pi.basisFun_det_apply]
  have hor : (v.orientation = (L.affineFacetOrientation p j b).orientationAt x) ↔
      w.orientation = if affineFacetSign j b = 1 then b₀.orientation else -b₀.orientation := by
    rw [← (_root_.Orientation.map (Fin n) e).injective.eq_iff, ← Module.Basis.orientation_map,
      affineFacetOrientation, M.map_orientationAt_unitCubeImageOrientation hM q₀]
  rw [hor]
  rcases Int.units_eq_one_or (affineFacetSign j b) with hs | hs <;> simp only [hs, ↓reduceIte]
  · rw [eq_comm, b₀.orientation_eq_iff_det_pos w]
    simp only [Units.val_one, Int.cast_one, one_mul]
    exact ⟨fun hw ↦ mul_pos hL hw, fun hpos ↦ pos_of_mul_pos_right hpos hL.le⟩
  · have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hne, ↓reduceIte, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      neg_one_mul]
    rw [← b₀.orientation_ne_iff_eq_neg, ne_comm, w.orientation_ne_iff_eq_neg,
      b₀.orientation_eq_neg_iff_det_neg w, neg_mul, neg_pos]
    exact ⟨mul_neg_of_pos_of_neg hL, fun hneg ↦ neg_of_mul_neg_right hneg hL.le⟩

end ContinuousLinearEquiv

end
