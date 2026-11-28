/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Orientation.OrientedAtlas
public import TauCeti.Topology.Homeomorph.CompactQuotient
import Mathlib.Order.Fin.Tuple

/-!
# The closed unit cube as a model with corners and affine cube and facet charts

For a finite index type `ι`, `TauCeti.modelWithCornersUnitCube` packages `Icc (0 : ι → ℝ) 1` as a
model with corners on `ι → ℝ` via coordinatewise `[0, 1]` clamp retraction. For an injective
continuous linear map `M : (ι → ℝ) →L[ℝ] E` and base point `q₀ : E`, the compact affine cube
`(fun u ↦ q₀ + M u) '' Icc 0 1` carries a single global chart
`ContinuousLinearMap.unitCubeImageChartedSpace` onto `Icc (0 : ι → ℝ) 1` whose ambient inclusion
`Subtype.val` has derivative `M` everywhere, including boundary and corner points.

Specializing `ι = Fin (n + 1)` equips each of the `2 (n + 1)` facets `(j : Fin (n + 1), b : Bool)`
of `(fun w ↦ p + L w) '' Icc 0 1` with its base corner `ContinuousLinearMap.affineFacetBase`,
tangent map `ContinuousLinearMap.affineFacetLinearMap`, outward edge vector
`ContinuousLinearMap.affineFacetOutward`, outward-first determinant identity
`ContinuousLinearMap.det_cons_affineFacetOutward_affineFacetLinearMap`, and global `n`-cube chart
`ContinuousLinearEquiv.affineFacetChartedSpace`.

## Main declarations

* `TauCeti.modelWithCornersUnitCube`, `TauCeti.instHasGroupoidOrientationPreservingUnitCube`.
* `ContinuousLinearMap.unitCubeImageHomeomorph`, `ContinuousLinearMap.unitCubeImageChartedSpace`,
  `ContinuousLinearMap.isManifold_unitCubeImageChartedSpace`,
  `ContinuousLinearMap.mfderiv_subtypeVal_unitCubeImage`.
* `TauCeti.affineFacetSign`, `ContinuousLinearMap.affineFacetBase`,
  `ContinuousLinearMap.affineFacetLinearMap`, `ContinuousLinearMap.affineFacetOutward`,
  `ContinuousLinearMap.det_cons_affineFacetOutward_affineFacetLinearMap`.
* `ContinuousLinearEquiv.affineFacetChartedSpace`,
  `ContinuousLinearEquiv.isManifold_affineFacetChartedSpace`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 16 (manifolds with corners).
-/

public section

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace TauCeti

section UnitCubeModel

variable (ι : Type*) [Fintype ι]

/-- The partial equivalence embedding the closed unit cube `Icc (0 : ι → ℝ) 1` into `ι → ℝ`, with
coordinatewise clamp `Set.projIcc 0 1 zero_le_one` as inverse on `Icc 0 1`. -/
private def unitCubePartialEquiv : PartialEquiv (Icc (0 : ι → ℝ) 1) (ι → ℝ) where
  toFun := Subtype.val
  invFun x := ⟨fun i ↦ Set.projIcc 0 1 zero_le_one (x i),
    ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (x i)).property.left,
      fun i ↦ (Set.projIcc 0 1 zero_le_one (x i)).property.right⟩⟩
  source := univ
  target := Icc 0 1
  map_source' x _ := x.property
  map_target' _ _ := mem_univ _
  left_inv' x _ := Subtype.ext <| funext fun i ↦
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨x.property.left i, x.property.right i⟩)
  right_inv' _ hx := funext fun i ↦
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hx.left i, hx.right i⟩)

/-- The closed unit cube `Icc (0 : ι → ℝ) 1` as a model with corners on `ι → ℝ`, constructed via
`ModelWithCorners.ofConvexRange` with coordinatewise `[0, 1]` clamp retraction. -/
def modelWithCornersUnitCube : ModelWithCorners ℝ (ι → ℝ) (Icc (0 : ι → ℝ) 1) :=
  ModelWithCorners.ofConvexRange (unitCubePartialEquiv ι) rfl (convex_Icc 0 1)
    continuous_subtypeVal
    (Continuous.subtype_mk
      (continuous_pi fun i ↦ continuous_subtypeVal.comp
        ((continuous_projIcc (h := (zero_le_one : (0 : ℝ) ≤ 1))).comp (continuous_apply i))) _)
    ⟨fun _ ↦ 1 / 2, mem_interior.mpr ⟨univ.pi fun _ ↦ Ioo (0 : ℝ) 1,
      fun _ hx ↦ ⟨fun i ↦ (hx i (mem_univ i)).left.le, fun i ↦ (hx i (mem_univ i)).right.le⟩,
      isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo,
      fun _ _ ↦ by norm_num⟩⟩

variable {ι}

@[simp] theorem modelWithCornersUnitCube_apply (x : Icc (0 : ι → ℝ) 1) :
    modelWithCornersUnitCube ι x = x.val := (rfl)

@[simp] theorem coe_modelWithCornersUnitCube :
    (modelWithCornersUnitCube ι : Icc (0 : ι → ℝ) 1 → ι → ℝ) = Subtype.val := (rfl)

@[simp] theorem coe_modelWithCornersUnitCube_symm_apply (x : ι → ℝ) (i : ι) :
    ((modelWithCornersUnitCube ι).symm x : ι → ℝ) i = Set.projIcc 0 1 zero_le_one (x i) := (rfl)

@[simp] theorem modelWithCornersUnitCube_symm_of_mem {x : ι → ℝ} (hx : x ∈ Icc (0 : ι → ℝ) 1) :
    ((modelWithCornersUnitCube ι).symm x : ι → ℝ) = x :=
  funext fun i ↦ congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hx.left i, hx.right i⟩)

@[simp] theorem modelWithCornersUnitCube_symm_coe (x : Icc (0 : ι → ℝ) 1) :
    (modelWithCornersUnitCube ι).symm x.val = x :=
  Subtype.ext (modelWithCornersUnitCube_symm_of_mem x.property)

theorem range_modelWithCornersUnitCube :
    range (modelWithCornersUnitCube ι) = Icc (0 : ι → ℝ) 1 := by ext x; simp

theorem target_modelWithCornersUnitCube :
    (modelWithCornersUnitCube ι).target = Icc (0 : ι → ℝ) 1 := (rfl)

theorem extChartAt_unitCube_source (α : Icc (0 : ι → ℝ) 1) :
    (extChartAt (modelWithCornersUnitCube ι) α).source = univ := by simp [extChartAt]

theorem extChartAt_unitCube_target (α : Icc (0 : ι → ℝ) 1) :
    (extChartAt (modelWithCornersUnitCube ι) α).target = Icc (0 : ι → ℝ) 1 := by
  ext x; simp [extChartAt]

theorem extChartAt_unitCube_apply (α x : Icc (0 : ι → ℝ) 1) :
    extChartAt (modelWithCornersUnitCube ι) α x = x.val := (rfl)

theorem coe_extChartAt_unitCube_symm_of_mem (α : Icc (0 : ι → ℝ) 1) {y : ι → ℝ}
    (hy : y ∈ Icc (0 : ι → ℝ) 1) :
    ((extChartAt (modelWithCornersUnitCube ι) α).symm y : ι → ℝ) = y := by
  simpa [extChartAt] using modelWithCornersUnitCube_symm_of_mem hy

/-- The coordinate inclusion of the closed unit cube into `ι → ℝ` is smooth of every order. -/
theorem contMDiff_subtypeVal_unitCube {n : ℕ∞ω} :
    ContMDiff (modelWithCornersUnitCube ι) 𝓘(ℝ, ι → ℝ) n
      (Subtype.val : Icc (0 : ι → ℝ) 1 → ι → ℝ) := fun x ↦
  contMDiffAt_iff.mpr ⟨continuous_subtypeVal.continuousAt,
    contDiffWithinAt_id.congr
      (fun _ hy ↦ coe_extChartAt_unitCube_symm_of_mem x
        (range_modelWithCornersUnitCube (ι := ι) ▸ hy))
      (coe_extChartAt_unitCube_symm_of_mem x x.property)⟩

/-- The manifold derivative of the coordinate inclusion of the closed unit cube is the identity at
every point, including boundary and corner points. -/
theorem mfderiv_subtypeVal_unitCube (x : Icc (0 : ι → ℝ) 1) :
    mfderiv (modelWithCornersUnitCube ι) 𝓘(ℝ, ι → ℝ) (Subtype.val : Icc (0 : ι → ℝ) 1 → ι → ℝ) x =
      (NormedSpace.fromTangentSpace x.val).symm.toContinuousLinearMap.comp
        (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toContinuousLinearMap :=
  HasMFDerivAt.mfderiv ⟨continuous_subtypeVal.continuousAt, by
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp, range_modelWithCornersUnitCube, extChartAt_unitCube_apply]
    exact (hasFDerivAt_id x.val).hasFDerivWithinAt.congr
      (fun _ hy ↦ coe_extChartAt_unitCube_symm_of_mem x hy)
      (coe_extChartAt_unitCube_symm_of_mem x x.property)⟩

/-- The identity atlas on the closed unit cube is orientation-preserving. -/
instance instHasGroupoidOrientationPreservingUnitCube :
    HasGroupoid (Icc (0 : ι → ℝ) 1)
      (orientationPreservingGroupoid (modelWithCornersUnitCube ι)) where
  compatible := by
    rintro _ _ ⟨rfl⟩ ⟨rfl⟩; simpa using ofSet_mem_orientationPreservingGroupoid isOpen_univ

end UnitCubeModel

/-- The outward orientation sign `(if b then 1 else -1) * (-1)^j` of the `(j, b)`-facet of the unit
cube `Icc (0 : Fin m → ℝ) 1`: `b = true` is the front facet `u j = 1` and `b = false` is the back
facet `u j = 0`. -/
def affineFacetSign {m : ℕ} (j : Fin m) (b : Bool) : ℤˣ :=
  (if b then 1 else -1) * (-1) ^ (j : ℕ)

theorem coe_affineFacetSign {m : ℕ} (j : Fin m) (b : Bool) :
    ((affineFacetSign j b : ℤ) : ℝ) = (if b then (1 : ℝ) else -1) * (-1 : ℝ) ^ (j : ℕ) := by
  rcases b with _ | _ <;> simp [affineFacetSign]

end TauCeti

namespace ContinuousLinearMap

open TauCeti

section Topological

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} (M : (ι → ℝ) →L[ℝ] E)

/-- The homeomorphism from an injective affine image `(fun u ↦ q₀ + M u) '' Icc 0 1` onto the
closed unit cube `Icc (0 : ι → ℝ) 1`. -/
def unitCubeImageHomeomorph (hM : Injective M) (q₀ : E) :
    ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) ≃ₜ Icc (0 : ι → ℝ) 1 :=
  (isCompact_Icc.imageHomeomorph (continuous_const.add M.continuous).continuousOn
    ((add_right_injective q₀).comp hM).injOn).symm

@[simp] theorem unitCubeImageHomeomorph_symm_apply (hM : Injective M) (q₀ : E)
    (u : Icc (0 : ι → ℝ) 1) :
    (M.unitCubeImageHomeomorph hM q₀).symm u = ⟨q₀ + M u.val, mem_image_of_mem _ u.property⟩ :=
  (isCompact_Icc.imageHomeomorph_apply (continuous_const.add M.continuous).continuousOn
    ((add_right_injective q₀).comp hM).injOn u)

theorem coe_unitCubeImageHomeomorph_symm_apply (hM : Injective M) (q₀ : E)
    (u : Icc (0 : ι → ℝ) 1) : ((M.unitCubeImageHomeomorph hM q₀).symm u : E) = q₀ + M u.val := by
  rw [unitCubeImageHomeomorph_symm_apply]

@[simp] theorem unitCubeImageHomeomorph_apply_mk (hM : Injective M) (q₀ : E) {u : ι → ℝ}
    (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    M.unitCubeImageHomeomorph hM q₀ ⟨q₀ + M u, mem_image_of_mem _ hu⟩ = ⟨u, hu⟩ :=
  (M.unitCubeImageHomeomorph hM q₀).symm.injective <| by
    rw [Homeomorph.symm_apply_apply, M.unitCubeImageHomeomorph_symm_apply]

/-- The single-chart `ChartedSpace` structure on an injective affine image of the unit cube,
modelled on `Icc (0 : ι → ℝ) 1`. -/
@[instance_reducible] def unitCubeImageChartedSpace (hM : Injective M) (q₀ : E) :
    ChartedSpace (Icc (0 : ι → ℝ) 1) ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) :=
  (M.unitCubeImageHomeomorph hM q₀).toOpenPartialHomeomorph.singletonChartedSpace rfl

theorem chartAt_unitCubeImage (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    chartAt (Icc (0 : ι → ℝ) 1) α = (M.unitCubeImageHomeomorph hM q₀).toOpenPartialHomeomorph := by
  let := M.unitCubeImageChartedSpace hM q₀
  exact (M.unitCubeImageHomeomorph hM q₀).toOpenPartialHomeomorph.singletonChartedSpace_chartAt_eq
    rfl

theorem chartAt_unitCubeImage_source (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀; (chartAt (Icc (0 : ι → ℝ) 1) α).source = univ := by
  let := M.unitCubeImageChartedSpace hM q₀; rw [M.chartAt_unitCubeImage hM q₀ α]; rfl

end Topological

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] (M : (ι → ℝ) →L[ℝ] E)

theorem extChartAt_unitCubeImage_source (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (extChartAt (modelWithCornersUnitCube ι) α).source = univ := by
  let := M.unitCubeImageChartedSpace hM q₀
  rw [extChartAt_source, M.chartAt_unitCubeImage_source hM q₀ α]

theorem extChartAt_unitCubeImage_target (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (extChartAt (modelWithCornersUnitCube ι) α).target = Icc (0 : ι → ℝ) 1 := by
  let := M.unitCubeImageChartedSpace hM q₀; ext u
  rw [extChartAt, M.chartAt_unitCubeImage hM q₀ α, OpenPartialHomeomorph.extend_target]; simp

theorem extChartAt_unitCubeImage_apply_mk (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) {u : ι → ℝ} (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    letI := M.unitCubeImageChartedSpace hM q₀
    extChartAt (modelWithCornersUnitCube ι) α ⟨q₀ + M u, mem_image_of_mem _ hu⟩ = u := by
  let := M.unitCubeImageChartedSpace hM q₀
  rw [extChartAt_coe, Function.comp_apply, M.chartAt_unitCubeImage hM q₀ α]
  simp [M.unitCubeImageHomeomorph_apply_mk hM q₀ hu]

theorem extChartAt_unitCubeImage_symm_of_mem (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) {u : ι → ℝ} (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (extChartAt (modelWithCornersUnitCube ι) α).symm u = ⟨q₀ + M u, mem_image_of_mem _ hu⟩ := by
  let := M.unitCubeImageChartedSpace hM q₀
  rw [extChartAt_coe_symm, Function.comp_apply, M.chartAt_unitCubeImage hM q₀ α]
  exact Subtype.ext (by simp [modelWithCornersUnitCube_symm_of_mem hu])

/-- With its global affine chart, an injective affine image of the unit cube is a `C^n` manifold
with corners for every `n`. -/
theorem isManifold_unitCubeImageChartedSpace (hM : Injective M) (q₀ : E) (n : ℕ∞ω) :
    letI := M.unitCubeImageChartedSpace hM q₀
    IsManifold (modelWithCornersUnitCube ι) n ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) :=
  (M.unitCubeImageHomeomorph hM q₀).toOpenPartialHomeomorph.isManifold_singleton rfl

/-- The singleton atlas of an injective affine image of the unit cube belongs to the
orientation-preserving groupoid. -/
theorem hasGroupoid_orientationPreserving_unitCubeImageChartedSpace (hM : Injective M) (q₀ : E) :
    letI := M.unitCubeImageChartedSpace hM q₀
    HasGroupoid ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)
      (orientationPreservingGroupoid (modelWithCornersUnitCube ι)) :=
  (M.unitCubeImageHomeomorph hM q₀).toOpenPartialHomeomorph.singleton_hasGroupoid rfl
    (orientationPreservingGroupoid (modelWithCornersUnitCube ι))

/-- The ambient inclusion `Subtype.val` of an injective affine cube image is smooth of every
order. -/
theorem contMDiff_subtypeVal_unitCubeImage (hM : Injective M) (q₀ : E) {n : ℕ∞ω} :
    letI := M.unitCubeImageChartedSpace hM q₀
    ContMDiff (modelWithCornersUnitCube ι) 𝓘(ℝ, E) n
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) := by
  let := M.unitCubeImageChartedSpace hM q₀
  intro x
  have haff : ContDiff ℝ n (fun u : ι → ℝ ↦ q₀ + M u) := contDiff_const.add M.contDiff
  refine contMDiffAt_iff.mpr ⟨continuous_subtypeVal.continuousAt,
    haff.contDiffWithinAt.congr (fun u hu ↦ ?_) ?_⟩
  · simpa only [Function.comp_apply, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using congrArg Subtype.val (M.extChartAt_unitCubeImage_symm_of_mem hM q₀ x
        (range_modelWithCornersUnitCube (ι := ι) ▸ hu))
  · obtain ⟨u₀, hu₀, hxu₀⟩ := x.property
    have hx : x = ⟨q₀ + M u₀, mem_image_of_mem _ hu₀⟩ := Subtype.ext hxu₀.symm
    simp only [Function.comp_apply, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq, hx,
      M.extChartAt_unitCubeImage_apply_mk hM q₀ _ hu₀,
      M.extChartAt_unitCubeImage_symm_of_mem hM q₀ _ hu₀]

/-- The inverse chart parametrization `u ↦ ⟨q₀ + M u, _⟩` from the closed unit cube onto its
injective affine image is smooth of every order. -/
theorem contMDiff_unitCubeImageHomeomorph_symm (hM : Injective M) (q₀ : E) {n : ℕ∞ω} :
    letI := M.unitCubeImageChartedSpace hM q₀
    ContMDiff (modelWithCornersUnitCube ι) (modelWithCornersUnitCube ι) n
      (M.unitCubeImageHomeomorph hM q₀).symm := by
  let := M.unitCubeImageChartedSpace hM q₀
  intro u
  refine contMDiffAt_iff.mpr ⟨(M.unitCubeImageHomeomorph hM q₀).symm.continuous.continuousAt,
    contDiffWithinAt_id.congr (fun v hv ↦ ?_) ?_⟩
  · have hv' : v ∈ Icc (0 : ι → ℝ) 1 := range_modelWithCornersUnitCube (ι := ι) ▸ hv
    have hs : (extChartAt (modelWithCornersUnitCube ι) u).symm v = ⟨v, hv'⟩ :=
      Subtype.ext (coe_extChartAt_unitCube_symm_of_mem u hv')
    simp only [Function.comp_apply, hs, id_eq, M.unitCubeImageHomeomorph_symm_apply hM q₀ ⟨v, hv'⟩,
      M.extChartAt_unitCubeImage_apply_mk hM q₀ _ hv']
  · have hs : (extChartAt (modelWithCornersUnitCube ι) u).symm u.val = u :=
      Subtype.ext (coe_extChartAt_unitCube_symm_of_mem u u.property)
    simp only [Function.comp_apply, extChartAt_unitCube_apply, hs, id_eq,
      M.unitCubeImageHomeomorph_symm_apply hM q₀ u,
      M.extChartAt_unitCubeImage_apply_mk hM q₀ _ u.property]

/-- At every point of an injective affine cube image, the manifold derivative of the ambient
inclusion `Subtype.val` is `M`, read through the model and ambient tangent identifications. -/
theorem mfderiv_subtypeVal_unitCubeImage (hM : Injective M) (q₀ : E)
    (x : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    mfderiv (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) x =
      ((NormedSpace.fromTangentSpace x.val).symm.toContinuousLinearMap.comp M).comp
        (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toContinuousLinearMap := by
  let := M.unitCubeImageChartedSpace hM q₀
  refine HasMFDerivAt.mfderiv ⟨continuous_subtypeVal.continuousAt, ?_⟩
  obtain ⟨u₀, hu₀, hxu₀⟩ := x.property
  have hx : x = ⟨q₀ + M u₀, mem_image_of_mem _ hu₀⟩ := Subtype.ext hxu₀.symm
  subst hx
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, range_modelWithCornersUnitCube,
    M.extChartAt_unitCubeImage_apply_mk hM q₀ _ hu₀]
  exact (((M.hasFDerivAt (x := u₀)).const_add q₀).hasFDerivWithinAt).congr
    (fun u hu ↦ congrArg Subtype.val (M.extChartAt_unitCubeImage_symm_of_mem hM q₀ _ hu))
    (congrArg Subtype.val (M.extChartAt_unitCubeImage_symm_of_mem hM q₀ _ hu₀))

end Smooth

section AffineFacet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (M : (Fin (n + 1) → ℝ) →L[ℝ] E)

/-- The base corner `p + M (j.insertNth (if b then 1 else 0) 0)` of the `(j, b)`-facet of the
affine cube `w ↦ p + M w`. -/
def affineFacetBase (p : E) (j : Fin (n + 1)) (b : Bool) : E :=
  p + M (j.insertNth (if b then 1 else 0) 0)

/-- The continuous linear map `u ↦ M (j.insertNth 0 u)` parametrizing the tangent directions of the
`j`-th facet pair of `w ↦ p + M w`. -/
def affineFacetLinearMap (j : Fin (n + 1)) : (Fin n → ℝ) →L[ℝ] E :=
  ∑ r : Fin n, (ContinuousLinearMap.proj r).smulRight (M (Pi.single (j.succAbove r) 1))

@[simp] theorem affineFacetLinearMap_apply (j : Fin (n + 1)) (u : Fin n → ℝ) :
    M.affineFacetLinearMap j u = M (j.insertNth 0 u) := by
  have hu : ∑ r : Fin n, u r • (Pi.single (j.succAbove r) 1 : Fin (n + 1) → ℝ) =
      j.insertNth 0 u := by
    ext k; rcases eq_or_ne j k with rfl | hk
    · simp
    · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hk.symm
      simp [Pi.single_apply, (Fin.succAbove_right_injective (p := j)).eq_iff]
  simp only [affineFacetLinearMap, sum_apply, smulRight_apply, proj_apply, ← map_smul, ← map_sum,
    hu]

/-- Evaluating `affineFacetLinearMap` on the `r`-th standard basis vector gives the
`(j.succAbove r)`-th edge vector of `M`. -/
theorem affineFacetLinearMap_single (j : Fin (n + 1)) (r : Fin n) :
    M.affineFacetLinearMap j (Pi.single r 1) = M (Pi.single (j.succAbove r) 1) := by
  rw [affineFacetLinearMap_apply]; congr 1; ext k; rcases eq_or_ne j k with rfl | hk
  · simp
  · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hk.symm
    simp [Pi.single_apply, (Fin.succAbove_right_injective (p := j)).eq_iff]

/-- The affine parametrization of the `(j, b)`-facet inserts `1` or `0` at coordinate `j`. -/
theorem affineFacetBase_add_affineFacetLinearMap (p : E) (j : Fin (n + 1)) (b : Bool)
    (u : Fin n → ℝ) :
    M.affineFacetBase p j b + M.affineFacetLinearMap j u =
      p + M (j.insertNth (if b then 1 else 0) u) := by
  rw [affineFacetBase, affineFacetLinearMap_apply, add_assoc, ← map_add]; congr 2; ext k
  rcases eq_or_ne j k with rfl | hk
  · simp
  · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hk.symm; simp

/-- Every `(j, b)`-facet of an affine `(n + 1)`-cube lies in that affine cube. -/
theorem affineFacet_subset_image (p : E) (j : Fin (n + 1)) (b : Bool) :
    ((fun u : Fin n → ℝ ↦ M.affineFacetBase p j b + M.affineFacetLinearMap j u) '' Icc 0 1) ⊆
      (fun w : Fin (n + 1) → ℝ ↦ p + M w) '' Icc 0 1 := by
  rintro _ ⟨u, hu, rfl⟩; dsimp only; rw [affineFacetBase_add_affineFacetLinearMap]
  refine mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨?_, hu⟩)
  rcases b with _ | _ <;> simp

/-- The outward-pointing edge vector `± M eⱼ` on the `(j, b)`-facet of `w ↦ p + M w`. -/
def affineFacetOutward (j : Fin (n + 1)) (b : Bool) : E :=
  (if b then (1 : ℝ) else -1) • M (Pi.single j 1)

end AffineFacet

/-- Prepending `affineFacetOutward L j b` to `r ↦ L.affineFacetLinearMap j (w r)` gives `(n + 1) ×
(n + 1)` determinant `affineFacetSign j b * det L * det w`. -/
theorem det_cons_affineFacetOutward_affineFacetLinearMap {n : ℕ}
    (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) (j : Fin (n + 1)) (b : Bool)
    (w : Fin n → Fin n → ℝ) :
    (Matrix.of (Fin.cons (L.affineFacetOutward j b)
      (fun r ↦ L.affineFacetLinearMap j (w r)))).det =
      ((affineFacetSign j b : ℤ) : ℝ) * LinearMap.det L.toLinearMap * (Matrix.of w).det := by
  let u₀ : Fin (n + 1) → ℝ := (if b then (1 : ℝ) else -1) • Pi.single j 1
  let u : Fin n → Fin (n + 1) → ℝ := fun r ↦ j.insertNth 0 (w r)
  have hcons : Fin.cons (L.affineFacetOutward j b) (fun r ↦ L.affineFacetLinearMap j (w r)) =
      L.toLinearMap ∘ Fin.cons u₀ u := funext <| Fin.cases
    (by rcases b <;> simp [u₀, affineFacetOutward])
    (fun r ↦ by simp [u, affineFacetLinearMap_apply])
  have hdet := (Pi.basisFun ℝ (Fin (n + 1))).det_comp L.toLinearMap (Fin.cons u₀ u)
  simp only [Pi.basisFun_det_apply] at hdet
  rw [hcons, hdet, Matrix.det_succ_row_zero]
  simp only [Matrix.of_apply, Fin.cons_zero, u₀, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hminor : (Matrix.of (Fin.cons u₀ u)).submatrix Fin.succ j.succAbove = Matrix.of w := by
    ext r c; simp [u]
  rw [hminor, coe_affineFacetSign]
  rcases b with _ | _ <;> simp <;> ring

end ContinuousLinearMap

namespace ContinuousLinearEquiv

open ContinuousLinearMap TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (L : (Fin (n + 1) → ℝ) ≃L[ℝ] E)

/-- Each facet tangent map of a continuous linear equivalence is injective. -/
theorem injective_affineFacetLinearMap (j : Fin (n + 1)) :
    Injective (L.toContinuousLinearMap.affineFacetLinearMap j) := by
  intro u₁ u₂ h
  simp only [affineFacetLinearMap_apply, ContinuousLinearEquiv.coe_coe] at h
  funext r; simpa using congrFun (L.injective h) (j.succAbove r)

/-- The single-chart `ChartedSpace` structure on the `(j, b)`-facet of `w ↦ p + L w`, modelled on
the closed unit `n`-cube `Icc (0 : Fin n → ℝ) 1`. -/
abbrev affineFacetChartedSpace (p : E) (j : Fin (n + 1)) (b : Bool) :
    ChartedSpace (Icc (0 : Fin n → ℝ) 1)
      ↥((fun u : Fin n → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1) :=
  (L.toContinuousLinearMap.affineFacetLinearMap j).unitCubeImageChartedSpace
    (L.injective_affineFacetLinearMap j) (L.toContinuousLinearMap.affineFacetBase p j b)

/-- Each `(j, b)`-facet of an invertible affine cube image is a `C^k` manifold with corners
modelled on the closed unit `n`-cube. -/
theorem isManifold_affineFacetChartedSpace (p : E) (j : Fin (n + 1)) (b : Bool) (k : ℕ∞ω) :
    letI := L.affineFacetChartedSpace p j b
    IsManifold (modelWithCornersUnitCube (Fin n)) k
      ↥((fun u : Fin n → ℝ ↦ L.toContinuousLinearMap.affineFacetBase p j b +
        L.toContinuousLinearMap.affineFacetLinearMap j u) '' Icc 0 1) :=
  (L.toContinuousLinearMap.affineFacetLinearMap j).isManifold_unitCubeImageChartedSpace
    (L.injective_affineFacetLinearMap j) (L.toContinuousLinearMap.affineFacetBase p j b) k

end ContinuousLinearEquiv

end
