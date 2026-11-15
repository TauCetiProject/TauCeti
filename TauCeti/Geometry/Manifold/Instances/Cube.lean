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

/-!
# The closed unit cube as a model with corners and affine cube charts

For a finite index type `ι`, the closed unit cube `Icc (0 : ι → ℝ) 1` is convex with nonempty
interior and admits the continuous coordinatewise clamp retraction `Set.projIcc 0 1 zero_le_one`.
`TauCeti.modelWithCornersUnitCube` packages this data via `ModelWithCorners.ofConvexRange` so that
`Icc (0 : ι → ℝ) 1` is a smooth manifold with corners modelled on `ι → ℝ` by a single global
identity chart.

More generally, for an injective continuous linear map `M : (ι → ℝ) →L[ℝ] E` and base point
`q₀ : E`, the compact affine cube `(fun u ↦ q₀ + M u) '' Icc 0 1` carries a single global affine
chart `ContinuousLinearMap.unitCubeImageChartedSpace` onto `Icc (0 : ι → ℝ) 1`, making it a smooth
oriented manifold with corners whose ambient inclusion `Subtype.val` has derivative `M` at every
point, including boundary and corner points.

## Main declarations

* `TauCeti.modelWithCornersUnitCube`: `Icc (0 : ι → ℝ) 1` as a `ModelWithCorners ℝ (ι → ℝ)`.
* `TauCeti.instHasGroupoidOrientationPreservingUnitCube`: the identity atlas on the closed unit
  cube is orientation-preserving.
* `ContinuousLinearMap.unitCubeImageHomeomorph`, `ContinuousLinearMap.unitCubeImageChartedSpace`:
  the global affine chart on `(fun u ↦ q₀ + M u) '' Icc 0 1`.
* `ContinuousLinearMap.isManifold_unitCubeImageChartedSpace`,
  `ContinuousLinearMap.hasGroupoid_orientationPreserving_unitCubeImageChartedSpace`: smooth and
  orientation-preserving manifold structure on an injective affine cube image.
* `ContinuousLinearMap.contMDiff_subtypeVal_unitCubeImage`,
  `ContinuousLinearMap.mfderiv_subtypeVal_unitCubeImage`: smoothness and manifold derivative of the
  ambient inclusion `Subtype.val`.

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
    ⟨fun i ↦ (Set.projIcc 0 1 zero_le_one (x i)).2.1,
      fun i ↦ (Set.projIcc 0 1 zero_le_one (x i)).2.2⟩⟩
  source := univ
  target := Icc 0 1
  map_source' x _ := x.2
  map_target' _ _ := mem_univ _
  left_inv' x _ := Subtype.ext <| funext fun i ↦
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨x.2.1 i, x.2.2 i⟩)
  right_inv' _ hx := funext fun i ↦
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hx.1 i, hx.2 i⟩)

/-- The closed unit cube `Icc (0 : ι → ℝ) 1` as a model with corners on `ι → ℝ`, constructed via
`ModelWithCorners.ofConvexRange` with coordinatewise `[0, 1]` clamp retraction. -/
def modelWithCornersUnitCube : ModelWithCorners ℝ (ι → ℝ) (Icc (0 : ι → ℝ) 1) :=
  ModelWithCorners.ofConvexRange (unitCubePartialEquiv ι) rfl (convex_Icc 0 1)
    continuous_subtype_val
    (Continuous.subtype_mk
      (continuous_pi fun i ↦ continuous_subtype_val.comp
        ((continuous_projIcc (h := (zero_le_one : (0 : ℝ) ≤ 1))).comp (continuous_apply i))) _)
    ⟨fun _ ↦ 1 / 2, mem_interior.mpr ⟨univ.pi fun _ ↦ Ioo (0 : ℝ) 1,
      fun _ hx ↦ ⟨fun i ↦ (hx i (mem_univ i)).1.le, fun i ↦ (hx i (mem_univ i)).2.le⟩,
      isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo,
      fun _ _ ↦ by norm_num⟩⟩

variable {ι}

@[simp]
theorem modelWithCornersUnitCube_apply (x : Icc (0 : ι → ℝ) 1) :
    modelWithCornersUnitCube ι x = x.1 :=
  (rfl)

@[simp]
theorem coe_modelWithCornersUnitCube :
    (modelWithCornersUnitCube ι : Icc (0 : ι → ℝ) 1 → ι → ℝ) = Subtype.val :=
  (rfl)

@[simp]
theorem coe_modelWithCornersUnitCube_symm_apply (x : ι → ℝ) (i : ι) :
    ((modelWithCornersUnitCube ι).symm x : ι → ℝ) i = Set.projIcc 0 1 zero_le_one (x i) :=
  (rfl)

@[simp]
theorem modelWithCornersUnitCube_symm_of_mem {x : ι → ℝ} (hx : x ∈ Icc (0 : ι → ℝ) 1) :
    ((modelWithCornersUnitCube ι).symm x : ι → ℝ) = x :=
  funext fun i ↦ congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hx.1 i, hx.2 i⟩)

@[simp]
theorem modelWithCornersUnitCube_symm_coe (x : Icc (0 : ι → ℝ) 1) :
    (modelWithCornersUnitCube ι).symm x.1 = x :=
  Subtype.ext (modelWithCornersUnitCube_symm_of_mem x.2)

theorem range_modelWithCornersUnitCube :
    range (modelWithCornersUnitCube ι) = Icc (0 : ι → ℝ) 1 := by
  ext x
  simp only [mem_range, modelWithCornersUnitCube_apply, Subtype.exists, exists_prop,
    exists_eq_right]

theorem target_modelWithCornersUnitCube :
    (modelWithCornersUnitCube ι).target = Icc (0 : ι → ℝ) 1 :=
  (rfl)

theorem extChartAt_unitCube_source (α : Icc (0 : ι → ℝ) 1) :
    (extChartAt (modelWithCornersUnitCube ι) α).source = univ := by
  simp [extChartAt]

theorem extChartAt_unitCube_target (α : Icc (0 : ι → ℝ) 1) :
    (extChartAt (modelWithCornersUnitCube ι) α).target = Icc (0 : ι → ℝ) 1 := by
  ext x
  simp [extChartAt]

theorem extChartAt_unitCube_apply (α x : Icc (0 : ι → ℝ) 1) :
    extChartAt (modelWithCornersUnitCube ι) α x = x.1 :=
  (rfl)

theorem coe_extChartAt_unitCube_symm_of_mem (α : Icc (0 : ι → ℝ) 1) {y : ι → ℝ}
    (hy : y ∈ Icc (0 : ι → ℝ) 1) :
    ((extChartAt (modelWithCornersUnitCube ι) α).symm y : ι → ℝ) = y := by
  simpa [extChartAt] using modelWithCornersUnitCube_symm_of_mem hy

/-- The coordinate inclusion of the closed unit cube into `ι → ℝ` is smooth of every order. -/
theorem contMDiff_subtypeVal_unitCube {n : ℕ∞ω} :
    ContMDiff (modelWithCornersUnitCube ι) 𝓘(ℝ, ι → ℝ) n
      (Subtype.val : Icc (0 : ι → ℝ) 1 → ι → ℝ) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  refine contDiffWithinAt_id.congr (fun y hy ↦ ?_) ?_
  · simp only [Function.comp_apply, id_eq]
    exact coe_extChartAt_unitCube_symm_of_mem x (range_modelWithCornersUnitCube (ι := ι) ▸ hy)
  · simp only [Function.comp_apply, id_eq, extChartAt_unitCube_apply]
    exact coe_extChartAt_unitCube_symm_of_mem x x.2

/-- The manifold derivative of the coordinate inclusion of the closed unit cube is the identity at
every point, including boundary and corner points. -/
theorem mfderiv_subtypeVal_unitCube (x : Icc (0 : ι → ℝ) 1) :
    mfderiv (modelWithCornersUnitCube ι) 𝓘(ℝ, ι → ℝ)
      (Subtype.val : Icc (0 : ι → ℝ) 1 → ι → ℝ) x =
      (NormedSpace.fromTangentSpace x.1).symm.toContinuousLinearMap.comp
        (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toContinuousLinearMap := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, range_modelWithCornersUnitCube, extChartAt_unitCube_apply]
  exact (hasFDerivAt_id x.1).hasFDerivWithinAt.congr
    (fun y hy ↦ coe_extChartAt_unitCube_symm_of_mem x hy)
    (coe_extChartAt_unitCube_symm_of_mem x x.2)

/-- The identity atlas on the closed unit cube is orientation-preserving. -/
instance instHasGroupoidOrientationPreservingUnitCube :
    HasGroupoid (Icc (0 : ι → ℝ) 1)
      (orientationPreservingGroupoid (modelWithCornersUnitCube ι)) where
  compatible := by
    rintro _ _ ⟨rfl⟩ ⟨rfl⟩
    simpa using ofSet_mem_orientationPreservingGroupoid isOpen_univ

end UnitCubeModel

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

@[simp]
theorem unitCubeImageHomeomorph_symm_apply (hM : Injective M) (q₀ : E) (u : Icc (0 : ι → ℝ) 1) :
    (M.unitCubeImageHomeomorph hM q₀).symm u = ⟨q₀ + M u.1, mem_image_of_mem _ u.2⟩ :=
  (isCompact_Icc.imageHomeomorph_apply (continuous_const.add M.continuous).continuousOn
    ((add_right_injective q₀).comp hM).injOn u)

theorem coe_unitCubeImageHomeomorph_symm_apply (hM : Injective M) (q₀ : E)
    (u : Icc (0 : ι → ℝ) 1) :
    ((M.unitCubeImageHomeomorph hM q₀).symm u : E) = q₀ + M u.1 := by
  rw [unitCubeImageHomeomorph_symm_apply]

@[simp]
theorem unitCubeImageHomeomorph_apply_mk (hM : Injective M) (q₀ : E) {u : ι → ℝ}
    (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    M.unitCubeImageHomeomorph hM q₀ ⟨q₀ + M u, mem_image_of_mem _ hu⟩ = ⟨u, hu⟩ :=
  (M.unitCubeImageHomeomorph hM q₀).symm.injective <| by
    rw [Homeomorph.symm_apply_apply, M.unitCubeImageHomeomorph_symm_apply]

/-- The single-chart `ChartedSpace` structure on an injective affine image of the unit cube,
modelled on `Icc (0 : ι → ℝ) 1`. -/
@[instance_reducible]
def unitCubeImageChartedSpace (hM : Injective M) (q₀ : E) :
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
    letI := M.unitCubeImageChartedSpace hM q₀
    (chartAt (Icc (0 : ι → ℝ) 1) α).source = univ := by
  let := M.unitCubeImageChartedSpace hM q₀
  rw [M.chartAt_unitCubeImage hM q₀ α]
  rfl

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
  let := M.unitCubeImageChartedSpace hM q₀
  ext u
  rw [extChartAt, M.chartAt_unitCubeImage hM q₀ α, OpenPartialHomeomorph.extend_target]
  simp

theorem extChartAt_unitCubeImage_apply_mk (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) {u : ι → ℝ} (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    letI := M.unitCubeImageChartedSpace hM q₀
    extChartAt (modelWithCornersUnitCube ι) α ⟨q₀ + M u, mem_image_of_mem _ hu⟩ = u := by
  let := M.unitCubeImageChartedSpace hM q₀
  rw [extChartAt_coe, Function.comp_apply, M.chartAt_unitCubeImage hM q₀ α]
  change modelWithCornersUnitCube ι
    (M.unitCubeImageHomeomorph hM q₀ ⟨q₀ + M u, mem_image_of_mem _ hu⟩) = u
  rw [M.unitCubeImageHomeomorph_apply_mk hM q₀ hu, modelWithCornersUnitCube_apply]

theorem extChartAt_unitCubeImage_symm_of_mem (hM : Injective M) (q₀ : E)
    (α : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) {u : ι → ℝ} (hu : u ∈ Icc (0 : ι → ℝ) 1) :
    letI := M.unitCubeImageChartedSpace hM q₀
    (extChartAt (modelWithCornersUnitCube ι) α).symm u =
      ⟨q₀ + M u, mem_image_of_mem _ hu⟩ := by
  let := M.unitCubeImageChartedSpace hM q₀
  rw [extChartAt, M.chartAt_unitCubeImage hM q₀ α]
  apply Subtype.ext
  change ((M.unitCubeImageHomeomorph hM q₀).symm ((modelWithCornersUnitCube ι).symm u) : E) =
    q₀ + M u
  rw [M.coe_unitCubeImageHomeomorph_symm_apply hM q₀, modelWithCornersUnitCube_symm_of_mem hu]

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
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have haff : ContDiff ℝ n (fun u : ι → ℝ ↦ q₀ + M u) := contDiff_const.add M.contDiff
  refine haff.contDiffWithinAt.congr (fun u hu ↦ ?_) ?_
  · have hu' : u ∈ Icc (0 : ι → ℝ) 1 := range_modelWithCornersUnitCube (ι := ι) ▸ hu
    simp only [Function.comp_apply, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
    rw [M.extChartAt_unitCubeImage_symm_of_mem hM q₀ x hu']
  · obtain ⟨u₀, hu₀, hxu₀⟩ := x.2
    have hx : x = ⟨q₀ + M u₀, mem_image_of_mem _ hu₀⟩ := Subtype.ext hxu₀.symm
    simp only [Function.comp_apply, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
    rw [hx, M.extChartAt_unitCubeImage_apply_mk hM q₀ _ hu₀,
      M.extChartAt_unitCubeImage_symm_of_mem hM q₀ _ hu₀]

/-- The inverse chart parametrization `u ↦ ⟨q₀ + M u, _⟩` from the closed unit cube onto its
injective affine image is smooth of every order. -/
theorem contMDiff_unitCubeImageHomeomorph_symm (hM : Injective M) (q₀ : E) {n : ℕ∞ω} :
    letI := M.unitCubeImageChartedSpace hM q₀
    ContMDiff (modelWithCornersUnitCube ι) (modelWithCornersUnitCube ι) n
      (M.unitCubeImageHomeomorph hM q₀).symm := by
  let := M.unitCubeImageChartedSpace hM q₀
  intro u
  rw [contMDiffAt_iff]
  refine ⟨(M.unitCubeImageHomeomorph hM q₀).symm.continuous.continuousAt, ?_⟩
  refine contDiffWithinAt_id.congr (fun v hv ↦ ?_) ?_
  · have hv' : v ∈ Icc (0 : ι → ℝ) 1 := range_modelWithCornersUnitCube (ι := ι) ▸ hv
    have hs : (extChartAt (modelWithCornersUnitCube ι) u).symm v = ⟨v, hv'⟩ :=
      Subtype.ext (coe_extChartAt_unitCube_symm_of_mem u hv')
    simp only [Function.comp_apply, hs, id_eq, M.unitCubeImageHomeomorph_symm_apply hM q₀ ⟨v, hv'⟩,
      M.extChartAt_unitCubeImage_apply_mk hM q₀ _ hv']
  · have hs : (extChartAt (modelWithCornersUnitCube ι) u).symm u.1 = u :=
      Subtype.ext (coe_extChartAt_unitCube_symm_of_mem u u.2)
    simp only [Function.comp_apply, extChartAt_unitCube_apply, hs, id_eq,
      M.unitCubeImageHomeomorph_symm_apply hM q₀ u,
      M.extChartAt_unitCubeImage_apply_mk hM q₀ _ u.2]

/-- At every point of an injective affine cube image, the manifold derivative of the ambient
inclusion `Subtype.val` is `M`, read through the model and ambient tangent identifications. -/
theorem mfderiv_subtypeVal_unitCubeImage (hM : Injective M) (q₀ : E)
    (x : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1)) :
    letI := M.unitCubeImageChartedSpace hM q₀
    mfderiv (modelWithCornersUnitCube ι) 𝓘(ℝ, E)
      (Subtype.val : ↥((fun u : ι → ℝ ↦ q₀ + M u) '' Icc 0 1) → E) x =
      ((NormedSpace.fromTangentSpace x.1).symm.toContinuousLinearMap.comp M).comp
        (tangentSpaceCastModel (modelWithCornersUnitCube ι) x).toContinuousLinearMap := by
  let := M.unitCubeImageChartedSpace hM q₀
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  obtain ⟨u₀, hu₀, hxu₀⟩ := x.2
  have hx : x = ⟨q₀ + M u₀, mem_image_of_mem _ hu₀⟩ := Subtype.ext hxu₀.symm
  subst hx
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, range_modelWithCornersUnitCube,
    M.extChartAt_unitCubeImage_apply_mk hM q₀ _ hu₀]
  have hd : HasFDerivWithinAt (fun u : ι → ℝ ↦ q₀ + M u) M (Icc (0 : ι → ℝ) 1) u₀ := by
    have hadd := ((hasFDerivAt_const q₀ u₀).add (M.hasFDerivAt (x := u₀))).hasFDerivWithinAt
      (s := Icc (0 : ι → ℝ) 1)
    rwa [zero_add] at hadd
  exact hd.congr
    (fun u hu ↦ by
      simp only [Function.comp_apply]
      rw [M.extChartAt_unitCubeImage_symm_of_mem hM q₀ _ hu])
    (by
      simp only [Function.comp_apply]
      rw [M.extChartAt_unitCubeImage_symm_of_mem hM q₀ _ hu₀])

end Smooth

end ContinuousLinearMap
