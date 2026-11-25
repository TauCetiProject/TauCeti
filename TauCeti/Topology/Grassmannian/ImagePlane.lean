/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.RangeProjection
public import TauCeti.Topology.Grassmannian.StarProjection.Basic
import TauCeti.Analysis.InnerProductSpace.PartialIsometry

/-!
# Image planes in the projection-form Grassmannian

A linear map `L : E → F` between finite-dimensional real inner product spaces moves the plane
`range P` of a point `P` of the Grassmannian `G(E, k)` (`Euclidean.grassmannian ℝ E k`) to the
subspace `L (range P)` of `F`. When `L` is injective on `range P`, though not necessarily on `E`,
this subspace is again a `k`-plane, and its orthogonal projection is a point of `G(F, k)`. This file
records that map on Grassmannians and its special case for linear isometries.

* `Euclidean.grassmannian.imagePlane E F k` sends a pair `(L, P)`, with `L` injective on the range
  of `P`, to the orthogonal projection onto `L (range P)`. It is a continuous map into `G(F, k)`,
  and its domain is open in `(E →L[ℝ] F) × G(E, k)`
  (`Euclidean.grassmannian.isOpen_setOf_injOn_range`). The continuity comes from the formula
  `Q A⁻¹ Q†` for this projection, where `Q = L P` and `A = Q† Q + (1 - P)`
  (`ContinuousLinearMap.starProjection_range_comp_eq`).
* For a linear isometry `U : E → F`, not necessarily surjective, `P ↦ U P U†` is a homeomorphism
  `LinearIsometry.grassmannianHomeomorph` of `G(E, k)` onto the subset of `G(F, k)` of projections
  whose range lies in `range U`, with inverse `Q ↦ U† Q U`. That subset is closed
  (`Euclidean.grassmannian.isClosed_setOf_range_le`), and `U P U†` is the projection onto
  `U (range P)` (`ContinuousLinearMap.comp_comp_adjoint_eq_starProjection_range_comp`).

These are the maps along which planes are carried when a measure on a space of planes is pushed
forward by a map whose differential is injective only on the planes concerned, or by an isometric
immersion (L. Simon, *Lectures on Geometric Measure Theory*, §38 and §39).

## Main definitions

* `Euclidean.grassmannian.imagePlane`: the continuous image-plane map `(L, P) ↦ P_{L (range P)}`.
* `LinearIsometry.grassmannianHomeomorph`: the homeomorphism `P ↦ U P U†` of `G(E, k)` onto the
  projections of `G(F, k)` with range in `range U`.

## Main results

* `Euclidean.grassmannian.finrank_range_comp`,
  `Euclidean.grassmannian.starProjection_range_comp_mem`: a linear map injective on a `k`-plane maps
  it onto a `k`-plane.
* `Euclidean.grassmannian.isOpen_setOf_injOn_range`: the domain of the image-plane map is open.
* `Euclidean.grassmannian.isClosed_setOf_range_le`: the points of `G(F, k)` whose plane lies in a
  given subspace form a closed set.
* `LinearIsometry.exists_comp_comp_adjoint_eq`: every point of `G(F, k)` whose plane lies in
  `range U` is `U P U†` for some `P ∈ G(E, k)`.
* `LinearIsometry.coe_grassmannianHomeomorph_apply_eq_imagePlane`: `U P U†` is the image-plane
  map at `(U, P)`, the projection onto `U (range P)`.
-/

public section

open Module ContinuousLinearMap

namespace Euclidean

namespace grassmannian

/-- A linear map `L` injective on the plane of a point `P` of `G(E, k)` maps it onto a `k`-plane:
the range of `L ∘L P`, which is `L (range P)`, has dimension `k`. -/
theorem finrank_range_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {P : E →L[ℝ] E}
    (hP : P ∈ grassmannian ℝ E k) {L : E →L[ℝ] F} (hL : Set.InjOn L (P.range : Set E)) :
    finrank ℝ (L ∘L P).range = k := by
  have hinj : Function.Injective ((L : E →ₗ[ℝ] F).domRestrict P.range) := by
    rw [LinearMap.injective_domRestrict_iff]
    exact LinearMap.disjoint_ker_iff_injOn.mpr hL
  have hrange : (L ∘L P).range = ((L : E →ₗ[ℝ] F).domRestrict P.range).range := by
    rw [LinearMap.range_domRestrict, ← LinearMap.range_comp]
    rfl
  rw [hrange, LinearMap.finrank_range_of_inj hinj, finrank_range hP]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {k : ℕ}

/-- If a linear map `L` is injective on the plane of a point `P` of `G(E, k)`, the orthogonal
projection onto the image `L (range P)` is a point of `G(F, k)`. -/
theorem starProjection_range_comp_mem {P : E →L[ℝ] E} (hP : P ∈ grassmannian ℝ E k)
    {L : E →L[ℝ] F} (hL : Set.InjOn L (P.range : Set E)) :
    (L ∘L P).range.starProjection ∈ grassmannian ℝ F k :=
  starProjection_mem (finrank_range_comp hP hL)

/-- A point of `G(E, k)`, seen as a star projection. -/
private def toStarProjection (P : grassmannian ℝ E k) : {P : E →L[ℝ] E // IsStarProjection P} :=
  ⟨P, isStarProjection P.property⟩

private theorem continuous_toStarProjection : Continuous (toStarProjection (E := E) (k := k)) :=
  continuous_subtypeVal.subtype_mk _

/-- The pairs `(L, P)` of a linear map `L : E → F` and a point `P` of `G(E, k)` such that `L` is
injective on the range of `P` form an open set. -/
theorem isOpen_setOf_injOn_range :
    IsOpen {x : (E →L[ℝ] F) × grassmannian ℝ E k |
      Set.InjOn x.1 ((x.2 : E →L[ℝ] E).range : Set E)} :=
  ContinuousLinearMap.isOpen_setOf_injOn_range.preimage
    (continuous_id.prodMap continuous_toStarProjection)

variable (E F k) in
/-- The **image-plane map** of Grassmannians: a pair `(L, P)` of a linear map `L : E → F` and a
point `P` of `G(E, k)` such that `L` is injective on the range of `P` goes to the orthogonal
projection onto `L (range P)`, a point of `G(F, k)`. It depends continuously on `(L, P)`. -/
noncomputable def imagePlane :
    C({x : (E →L[ℝ] F) × grassmannian ℝ E k // Set.InjOn x.1 ((x.2 : E →L[ℝ] E).range : Set E)},
      grassmannian ℝ F k) where
  toFun x := ⟨(x.val.1 ∘L (x.val.2 : E →L[ℝ] E)).range.starProjection,
    starProjection_range_comp_mem x.val.2.property x.property⟩
  continuous_toFun :=
    (continuousOn_starProjection_range_comp.comp_continuous
      ((continuous_id.prodMap continuous_toStarProjection).comp continuous_subtypeVal)
      fun x ↦ x.property).subtype_mk _

/-- The image-plane map at `(L, P)` is the orthogonal projection onto the range of `L ∘L P`. -/
@[simp]
theorem coe_imagePlane_apply (x : {x : (E →L[ℝ] F) × grassmannian ℝ E k //
      Set.InjOn x.1 ((x.2 : E →L[ℝ] E).range : Set E)}) :
    (imagePlane E F k x : F →L[ℝ] F) = (x.val.1 ∘L (x.val.2 : E →L[ℝ] E)).range.starProjection :=
  (rfl)

/-- The plane of the image-plane map at `(L, P)` is `L (range P)`. -/
theorem range_coe_imagePlane_apply (x : {x : (E →L[ℝ] F) × grassmannian ℝ E k //
      Set.InjOn x.1 ((x.2 : E →L[ℝ] E).range : Set E)}) :
    (imagePlane E F k x : F →L[ℝ] F).range =
      (x.val.2 : E →L[ℝ] E).range.map (x.val.1 : E →ₗ[ℝ] F) := by
  rw [coe_imagePlane_apply, Submodule.range_starProjection]
  exact LinearMap.range_comp _ _

/-- The points of `G(F, k)` whose plane lies in a given subspace `S` form a closed set. -/
theorem isClosed_setOf_range_le (S : Submodule ℝ F) :
    IsClosed {Q : grassmannian ℝ F k | (Q : F →L[ℝ] F).range ≤ S} := by
  simp_rw [← Submodule.starProjection_comp_eq_self_iff]
  exact isClosed_eq (continuous_const.clm_comp continuous_subtypeVal) continuous_subtypeVal

end grassmannian

end Euclidean

namespace LinearIsometry

open Euclidean

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {k : ℕ}
  (U : E →ₗᵢ[ℝ] F)

/-- Conjugation by a linear isometry `U` maps `G(E, k)` into `G(F, k)`: `U P U†` is the orthogonal
projection onto the `k`-plane `U (range P)`. -/
theorem comp_comp_adjoint_mem_grassmannian {P : E →L[ℝ] E} (hP : P ∈ grassmannian ℝ E k) :
    U.toContinuousLinearMap ∘L P ∘L adjoint U.toContinuousLinearMap ∈ grassmannian ℝ F k := by
  rw [comp_comp_adjoint_eq_starProjection_range_comp U.isometry (grassmannian.isStarProjection hP)]
  exact grassmannian.starProjection_range_comp_mem hP U.injective.injOn

/-- Every point `Q` of `G(F, k)` whose plane lies in the range of a linear isometry `U` is `U P U†`
for a point `P` of `G(E, k)`, namely the projection onto `U⁻¹ (range Q)`. -/
theorem exists_comp_comp_adjoint_eq {Q : F →L[ℝ] F} (hQ : Q ∈ grassmannian ℝ F k)
    (hQU : Q.range ≤ LinearMap.range U.toLinearMap) :
    ∃ P ∈ grassmannian ℝ E k,
      U.toContinuousLinearMap ∘L P ∘L adjoint U.toContinuousLinearMap = Q := by
  obtain ⟨S, hSdef⟩ : ∃ S : Submodule ℝ E, S = Q.range.comap U.toLinearMap := ⟨_, rfl⟩
  have hS : S.map U.toLinearMap = Q.range := hSdef ▸ Submodule.map_comap_eq_of_le hQU
  refine ⟨S.starProjection, grassmannian.starProjection_mem ?_, ?_⟩
  · rw [← grassmannian.finrank_range hQ, ← hS]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ U.injective S)
  have hrange : (U.toContinuousLinearMap ∘L S.starProjection).range = Q.range := by
    rw [← hS]
    exact (LinearMap.range_comp _ _).trans (congrArg _ (Submodule.range_starProjection S))
  obtain ⟨_, hQ'⟩ := grassmannian.eq_starProjection_range hQ
  rw [comp_comp_adjoint_eq_starProjection_range_comp U.isometry isStarProjection_starProjection]
  simp_rw [hrange]
  exact hQ'.symm

/-- Conjugation `Q ↦ U† Q U` by the adjoint of a linear isometry `U` maps the points of `G(F, k)`
whose plane lies in the range of `U` to `G(E, k)`. -/
theorem adjoint_comp_comp_mem_grassmannian {Q : F →L[ℝ] F} (hQ : Q ∈ grassmannian ℝ F k)
    (hQU : Q.range ≤ LinearMap.range U.toLinearMap) :
    adjoint U.toContinuousLinearMap ∘L Q ∘L U.toContinuousLinearMap ∈ grassmannian ℝ E k := by
  obtain ⟨P, hP, rfl⟩ := U.exists_comp_comp_adjoint_eq hQ hQU
  rwa [U.adjoint_comp_comp_comp_adjoint_comp]

variable (k) in
/-- For a linear isometry `U : E → F`, conjugation `P ↦ U P U†` is a homeomorphism from `G(E, k)`
onto the points of `G(F, k)` whose plane lies in the range of `U`, a closed subset of `G(F, k)`
(`Euclidean.grassmannian.isClosed_setOf_range_le`). Its inverse is `Q ↦ U† Q U`. The point `U P U†`
is the projection onto `U (range P)`. -/
noncomputable def grassmannianHomeomorph :
    grassmannian ℝ E k ≃ₜ
      {Q : grassmannian ℝ F k // (Q : F →L[ℝ] F).range ≤ LinearMap.range U.toLinearMap} where
  toFun P := ⟨⟨U.toContinuousLinearMap ∘L (P : E →L[ℝ] E) ∘L adjoint U.toContinuousLinearMap,
    U.comp_comp_adjoint_mem_grassmannian P.property⟩, LinearMap.range_comp_le_range _ _⟩
  invFun Q := ⟨adjoint U.toContinuousLinearMap ∘L (Q : F →L[ℝ] F) ∘L U.toContinuousLinearMap,
    U.adjoint_comp_comp_mem_grassmannian Q.val.property Q.property⟩
  left_inv P := Subtype.ext <| U.adjoint_comp_comp_comp_adjoint_comp P
  right_inv Q := by
    obtain ⟨P, -, hP⟩ := U.exists_comp_comp_adjoint_eq Q.val.property Q.property
    refine Subtype.ext <| Subtype.ext ?_
    dsimp only
    rw [← hP, U.adjoint_comp_comp_comp_adjoint_comp]
  continuous_toFun := (((continuous_const.clm_comp continuous_subtypeVal).clm_comp
    continuous_const).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_const.clm_comp
    (continuous_subtypeVal.comp continuous_subtypeVal)).clm_comp continuous_const).subtype_mk _

/-- `LinearIsometry.grassmannianHomeomorph` sends `P` to `U P U†`. -/
@[simp]
theorem coe_grassmannianHomeomorph_apply (P : grassmannian ℝ E k) :
    ((U.grassmannianHomeomorph k P : grassmannian ℝ F k) : F →L[ℝ] F) =
      U.toContinuousLinearMap ∘L (P : E →L[ℝ] E) ∘L adjoint U.toContinuousLinearMap :=
  (rfl)

/-- `LinearIsometry.grassmannianHomeomorph` agrees with the image-plane map at `(U, P)`: `U P U†`
is the orthogonal projection onto `U (range P)`. -/
theorem coe_grassmannianHomeomorph_apply_eq_imagePlane (P : grassmannian ℝ E k) :
    (U.grassmannianHomeomorph k P : grassmannian ℝ F k) =
      grassmannian.imagePlane E F k ⟨(U.toContinuousLinearMap, P), U.injective.injOn⟩ :=
  Subtype.ext <| comp_comp_adjoint_eq_starProjection_range_comp U.isometry
    (grassmannian.isStarProjection P.property)

/-- The plane of `LinearIsometry.grassmannianHomeomorph` at `P` is `U (range P)`. -/
theorem range_coe_grassmannianHomeomorph_apply (P : grassmannian ℝ E k) :
    ((U.grassmannianHomeomorph k P : grassmannian ℝ F k) : F →L[ℝ] F).range =
      (P : E →L[ℝ] E).range.map U.toLinearMap := by
  rw [coe_grassmannianHomeomorph_apply_eq_imagePlane]
  exact grassmannian.range_coe_imagePlane_apply _

/-- The inverse of `LinearIsometry.grassmannianHomeomorph` sends `Q` to `U† Q U`. -/
@[simp]
theorem coe_grassmannianHomeomorph_symm_apply
    (Q : {Q : grassmannian ℝ F k // (Q : F →L[ℝ] F).range ≤ LinearMap.range U.toLinearMap}) :
    ((U.grassmannianHomeomorph k).symm Q : E →L[ℝ] E) =
      adjoint U.toContinuousLinearMap ∘L (Q : F →L[ℝ] F) ∘L U.toContinuousLinearMap :=
  (rfl)

end LinearIsometry
