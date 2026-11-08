/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Boundary.Model

/-!
# The product collar of a Euclidean half-space

This file identifies the standard `(n + 1)`-dimensional Euclidean half-space with the product of
its `n`-dimensional boundary model and the one-dimensional Euclidean half-space.  It is the model
calculation behind collar charts: the last factor is the inward normal coordinate, and its zero
slice is exactly the boundary parametrization from `Boundary.Model`.

The equivalence is constructed first in the ambient Euclidean spaces by splitting off the zeroth
coordinate.  Restricting it to the half-spaces gives, with Mathlib's product model-with-corners
structure, a diffeomorphism.  The characteristic lemmas record both coordinate projections and
identify the zero slice, so later collar constructions do not need to unfold the coordinate
implementation.

This is the standard-model prerequisite for the collar-neighbourhood target in Layer 1 of the
GeometricTopology roadmap.  The global collar theorem requires patching these local product
coordinates on an arbitrary manifold and is not proved here.

## Main definitions

* `EuclideanHalfSpace.collarAmbientEquiv`: the ambient linear equivalence `ℝⁿ × ℝ¹ ≃ ℝⁿ⁺¹` putting
  the normal coordinate in coordinate zero.
* `EuclideanHalfSpace.collarDiffeomorph`: the same identification as a diffeomorphism of manifolds
  with corners.
* `EuclideanHalfSpace.collarModelChartedSpace`: the model half-space charted over the product,
  with that identification as its single chart.

## Main results

* `EuclideanHalfSpace.collarDiffeomorph_apply_zero_eq_boundaryParam`: the zero-normal slice is the
  boundary parametrization.
* `EuclideanHalfSpace.collarDiffeomorph_symm_apply_fst`: the inverse recovers the boundary
  projection.
* `EuclideanHalfSpace.collarDiffeomorph_apply_zero`: the inward normal is coordinate zero.
* `EuclideanHalfSpace.model_collarDiffeomorph`: read in the models with corners, the collar
  diffeomorphism is `collarAmbientEquiv`.
* `EuclideanHalfSpace.contMDiff_collarDiffeomorph_modelProd` and
  `EuclideanHalfSpace.contMDiff_collarDiffeomorph_symm_modelProd`: its smoothness for the product
  model charted over itself, the chart structure used by charts of product manifolds.
* `EuclideanHalfSpace.collarModelChartedSpace_chartAt` and
  `EuclideanHalfSpace.collarModelChartedSpace_atlas`: its preferred chart and its atlas.
* `EuclideanHalfSpace.exists_continuousLinearEquiv_image_range_prod`: the product model
  `ℝⁿ × [0, ∞)` and the half-space model are linearly equivalent, with matching ranges.

## Downstream target

The collar-neighbourhood theorem that these coordinates feed into is proved in M. Hirsch,
*Differential Topology*, Springer GTM 33 (1976), Theorem 6.1, and J. Lee, *Introduction to Smooth
Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.25.  That theorem is not proved here.
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- The ambient linear equivalence `ℝⁿ × ℝ¹ ≃ ℝⁿ⁺¹` underlying the collar identification: the
boundary coordinates go to the positive-index coordinates and the normal coordinate to coordinate
zero. -/
def collarAmbientEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
      ((EuclideanSpace.equiv (Fin 1) ℝ).trans
        (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ)))).trans
    (euclideanHalfSpaceBoundaryNormalEquiv n)

/-- The ambient collar equivalence sends the normal coordinate to coordinate zero. -/
@[simp]
theorem collarAmbientEquiv_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 1)) : collarAmbientEquiv n (x, t) 0 = t 0 := by
  simp [collarAmbientEquiv]

/-- The ambient collar equivalence sends the boundary coordinates to the positive-index
coordinates. -/
@[simp]
theorem collarAmbientEquiv_apply_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (t : EuclideanSpace ℝ (Fin 1)) (i : Fin n) :
    collarAmbientEquiv n (x, t) i.succ = x i := by
  simp [collarAmbientEquiv]

/-- At normal coordinate zero, the ambient collar equivalence is the boundary parametrization. -/
theorem collarAmbientEquiv_apply_zero_eq_boundaryParam (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    collarAmbientEquiv n (x, 0) = euclideanHalfSpaceBoundaryParam n x := by
  simp [collarAmbientEquiv]

/-- The boundary component of the inverse ambient collar equivalence is the boundary
projection. -/
@[simp]
theorem collarAmbientEquiv_symm_apply_fst (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ((collarAmbientEquiv n).symm y).1 = euclideanHalfSpaceBoundaryProj n y := by
  simp [collarAmbientEquiv]

/-- The inverse ambient collar equivalence recovers coordinate zero as the normal coordinate. -/
@[simp]
theorem collarAmbientEquiv_symm_apply_snd_apply_zero (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    ((collarAmbientEquiv n).symm y).2 0 = y 0 := by
  simp [collarAmbientEquiv]

/-- On the half-space, the normal coordinate recovered by the inverse ambient collar equivalence
is nonnegative. -/
theorem collarAmbientEquiv_symm_apply_snd_apply_zero_nonneg (n : ℕ)
    (y : EuclideanHalfSpace (n + 1)) :
    0 ≤ ((collarAmbientEquiv n).symm y.1).2 0 := by
  rw [collarAmbientEquiv_symm_apply_snd_apply_zero]
  exact y.2

private def collarEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) ≃ EuclideanHalfSpace (n + 1) where
  toFun p := ⟨collarAmbientEquiv n (p.1, p.2.1), by simpa using p.2.2⟩
  invFun y :=
    ((collarAmbientEquiv n).symm y.1 |>.1,
      ⟨(collarAmbientEquiv n).symm y.1 |>.2,
        collarAmbientEquiv_symm_apply_snd_apply_zero_nonneg n y⟩)
  left_inv p := by
    -- The anonymous proof that the recovered normal coordinate is nonnegative prevents `Prod.ext`
    -- from reducing the inverse application until the two subtype-valued components are exposed.
    change
      (((collarAmbientEquiv n).symm (collarAmbientEquiv n (p.1, p.2.1))).1,
        ⟨((collarAmbientEquiv n).symm (collarAmbientEquiv n (p.1, p.2.1))).2, _⟩) = p
    have h := (collarAmbientEquiv n).symm_apply_apply (p.1, p.2.1)
    have hfst : ((collarAmbientEquiv n).symm
        (collarAmbientEquiv n (p.1, p.2.1))).1 = p.1 :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦ q.1) h
    have hsnd : ((collarAmbientEquiv n).symm
        (collarAmbientEquiv n (p.1, p.2.1))).2 = p.2.1 :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1) ↦ q.2) h
    exact Prod.ext hfst (Subtype.ext hsnd)
  right_inv y := by
    apply Subtype.ext
    exact (collarAmbientEquiv n).apply_symm_apply y.1

/-- The product collar identification is smooth in both directions for Mathlib's standard models
with corners, at every finite or infinite regularity. -/
def collarDiffeomorph (n : ℕ) {k : WithTop ℕ∞} :
    Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) (EuclideanHalfSpace (n + 1)) k where
  toEquiv := collarEquiv n
  contMDiff_toFun := by
    rw [chartedSpaceSelf_prod]
    let I := (𝓡 n).prod (𝓡∂ 1)
    let J := 𝓡∂ (n + 1)
    have hcoord : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) k
        (collarAmbientEquiv n ∘ I) :=
      (collarAmbientEquiv n).contDiff.contMDiff.comp I.contMDiff
    have hrange : ∀ p, collarAmbientEquiv n (I p) ∈ range J := by
      intro p
      rw [range_modelWithCornersEuclideanHalfSpace]
      dsimp [I]
      rw [collarAmbientEquiv_apply_zero]
      simpa using p.2.2
    refine (J.contMDiffOn_symm.comp_contMDiff hcoord hrange).congr ?_
    intro p
    apply Subtype.ext
    -- Expand the model inverse explicitly so its half-space coercion can be rewritten by its API.
    change collarAmbientEquiv n (p.1, p.2.1) =
      ((𝓡∂ (n + 1)).symm (collarAmbientEquiv n (p.1, p.2.1))).1
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le]
    simpa only [collarAmbientEquiv_apply_zero] using p.2.2
  contMDiff_invFun := by
    rw [chartedSpaceSelf_prod]
    let I := (𝓡 n).prod (𝓡∂ 1)
    let J := 𝓡∂ (n + 1)
    have hcoord : ContMDiff J 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) k
        ((collarAmbientEquiv n).symm ∘ J) :=
      (collarAmbientEquiv n).symm.contDiff.contMDiff.comp J.contMDiff
    have hrange : ∀ y, (collarAmbientEquiv n).symm (J y) ∈ range I := by
      intro y
      rw [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
      refine ⟨mem_range_self _, ?_⟩
      dsimp [J]
      exact collarAmbientEquiv_symm_apply_snd_apply_zero_nonneg n y
    refine (I.contMDiffOn_symm.comp_contMDiff hcoord hrange).congr ?_
    intro y
    apply I.injective
    simp only [Function.comp_apply]
    rw [I.right_inv (hrange y)]
    rw [modelWithCorners_prod_coe]
    rw [modelWithCornersEuclideanHalfSpace_apply]
    rfl

/-- Read in the ambient Euclidean spaces, the collar diffeomorphism is the linear equivalence
`collarAmbientEquiv`. -/
theorem coe_collarDiffeomorph_apply (n : ℕ) {k : WithTop ℕ∞}
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (collarDiffeomorph (k := k) n p).1 = collarAmbientEquiv n (p.1, p.2.1) :=
  (rfl)

/-- Read in the ambient Euclidean spaces, the inverse collar diffeomorphism is the inverse of the
linear equivalence `collarAmbientEquiv`. -/
theorem collarDiffeomorph_symm_apply_coe (n : ℕ) {k : WithTop ℕ∞}
    (y : EuclideanHalfSpace (n + 1)) :
    (((collarDiffeomorph (k := k) n).symm y).1, ((collarDiffeomorph (k := k) n).symm y).2.1) =
      (collarAmbientEquiv n).symm y.1 :=
  (rfl)

/-- The collar diffeomorphism is smooth from the product model `ModelProd` charted over itself,
the chart structure of charts of manifolds modelled on `(𝓡 n).prod (𝓡∂ 1)`. -/
theorem contMDiff_collarDiffeomorph_modelProd (n : ℕ) {k : WithTop ℕ∞} :
    ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (fun p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1) ↦
        collarDiffeomorph (k := ⊤) n p) := by
  have h := (collarDiffeomorph (k := k) n).contMDiff
  -- Restate `h` for `collarEquiv`, whose type, unlike that of the diffeomorphism, does not mention
  -- the product charted space, so that the charted space can be rewritten.
  change ContMDiff _ _ _ (collarEquiv n) at h
  rw [chartedSpaceSelf_prod] at h
  exact h

/-- The inverse collar diffeomorphism is smooth to the product model `ModelProd` charted over
itself, the chart structure of charts of manifolds modelled on `(𝓡 n).prod (𝓡∂ 1)`. -/
theorem contMDiff_collarDiffeomorph_symm_modelProd (n : ℕ) {k : WithTop ℕ∞} :
    ContMDiff (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1))
      (M' := ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) k
      (fun y ↦ (collarDiffeomorph (k := ⊤) n).symm y) := by
  have h := (collarDiffeomorph (k := k) n).symm.contMDiff
  -- As above, restate `h` for `collarEquiv` so that the charted space can be rewritten.
  change ContMDiff _ _ _ (collarEquiv n).symm at h
  rw [chartedSpaceSelf_prod] at h
  exact h

/-- The collar diffeomorphism intertwines the models with corners: read through the model of the
half-space and the product model of `ℝⁿ × [0, ∞)`, it is the linear equivalence
`collarAmbientEquiv`. -/
theorem model_collarDiffeomorph (n : ℕ) {k : WithTop ℕ∞}
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (𝓡∂ (n + 1)) (collarDiffeomorph (k := k) n p) =
      collarAmbientEquiv n (((𝓡 n).prod (𝓡∂ 1)) p) := by
  simp only [modelWithCornersEuclideanHalfSpace_apply, coe_collarDiffeomorph_apply,
    modelWithCorners_prod_coe, modelWithCornersSelf_coe, Prod.map_apply', id_eq]

/-- The collar diffeomorphism sends the inward normal coordinate to coordinate zero. -/
@[simp]
theorem collarDiffeomorph_apply_zero (n : ℕ) {k : WithTop ℕ∞}
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) :
    (collarDiffeomorph (k := k) n p).1 0 = p.2.1 0 := by
  exact collarAmbientEquiv_apply_zero n p.1 p.2.1

/-- The collar diffeomorphism sends the boundary coordinates to the positive-index coordinates. -/
@[simp]
theorem collarDiffeomorph_apply_succ (n : ℕ) {k : WithTop ℕ∞}
    (p : EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) (i : Fin n) :
    (collarDiffeomorph (k := k) n p).1 i.succ = p.1 i := by
  exact collarAmbientEquiv_apply_succ n p.1 p.2.1 i

/-- The boundary component of the inverse collar diffeomorphism is the boundary projection. -/
@[simp]
theorem collarDiffeomorph_symm_apply_fst (n : ℕ) {k : WithTop ℕ∞}
    (y : EuclideanHalfSpace (n + 1)) :
    ((collarDiffeomorph (k := k) n).symm y).1 = boundaryProj n y := by
  rw [boundaryProj_coe]
  exact collarAmbientEquiv_symm_apply_fst n y.1

/-- The inverse collar diffeomorphism recovers the inward normal coordinate at zero. -/
@[simp]
theorem collarDiffeomorph_symm_apply_snd_apply_zero (n : ℕ) {k : WithTop ℕ∞}
    (y : EuclideanHalfSpace (n + 1)) :
    ((collarDiffeomorph (k := k) n).symm y).2.1 0 = y.1 0 := by
  exact collarAmbientEquiv_symm_apply_snd_apply_zero n y.1

/-- At normal coordinate zero, the collar diffeomorphism is the boundary parametrization. -/
@[simp]
theorem collarDiffeomorph_apply_zero_eq_boundaryParam (n : ℕ) {k : WithTop ℕ∞}
    (x : EuclideanSpace ℝ (Fin n)) :
    collarDiffeomorph (k := k) n (x, (0 : EuclideanHalfSpace 1)) = boundaryParam n x := by
  apply Subtype.ext
  rw [boundaryParam_coe]
  exact collarAmbientEquiv_apply_zero_eq_boundaryParam n x

/-- The model half-space as a charted space over the product, with the collar identification as
its single chart.

Deliberately not an instance: `EuclideanHalfSpace (n + 1)` already carries the charted space
structure over itself, and a second one found by instance search would make every statement
about its charts ambiguous. Use it explicitly with `letI`. -/
@[instance_reducible]
noncomputable def collarModelChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)
      (EuclideanHalfSpace (n + 1)) :=
  (collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph
    |>.singletonChartedSpace (by simp)

/-- The preferred chart of `collarModelChartedSpace` at every point is the collar
identification. -/
@[simp]
theorem collarModelChartedSpace_chartAt (n : ℕ) (y : EuclideanHalfSpace (n + 1)) :
    @chartAt (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) _ (EuclideanHalfSpace (n + 1)) _
        (collarModelChartedSpace n) y =
      (collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph :=
  OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq _ _

/-- The atlas of `collarModelChartedSpace` is the collar identification alone. -/
@[simp]
theorem collarModelChartedSpace_atlas (n : ℕ) :
    @atlas (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) _ (EuclideanHalfSpace (n + 1)) _
        (collarModelChartedSpace n) =
      {(collarDiffeomorph (k := ⊤) n).symm.toHomeomorph.toOpenPartialHomeomorph} :=
  (rfl)

/-- The product model `ℝⁿ × [0, ∞)` is linearly the half-space model of dimension `n + 1`: a
continuous linear equivalence of the ambient spaces carries the range of `(𝓡 n).prod (𝓡∂ 1)` onto
the range `{y | 0 ≤ y 0}` of `𝓡∂ (n + 1)`. -/
theorem exists_continuousLinearEquiv_image_range_prod (n : ℕ) :
    ∃ A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)), A '' range ((𝓡 n).prod (𝓡∂ 1)) = range (𝓡∂ (n + 1)) := by
  refine ⟨collarAmbientEquiv n, ?_⟩
  ext y
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, mem_preimage, ModelWithCorners.range_prod,
    range_modelWithCornersEuclideanHalfSpace, range_modelWithCornersEuclideanHalfSpace]
  simp [collarAmbientEquiv_symm_apply_snd_apply_zero]

end TauCeti.EuclideanHalfSpace
