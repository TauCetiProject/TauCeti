/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Geometry.Manifold.Boundary.Model

/-!
# A product half-space model

The closed half-space in `E × ℝ`, with the last coordinate nonnegative, is a model with
corners. Its inverse clips the last coordinate at zero. Keeping the tangential space
explicit allows polyhedral boundary charts to use product coordinates directly. The range of
the model is a convex polyhedron
(`TauCeti.isConvexPolyhedron_range_modelWithCornersHalfSpace`), which is what results on PL
manifolds modelled on it, such as the PL inverse theorem `TauCeti.IsPLMap.symm`, require.

Restricted to the points of positive height, the model is an open partial homeomorphism
onto the open half-space in `E × ℝ`. Its inverse turns a chart with values of positive last
coordinate into a half-space chart missing the boundary.

For `E = Fin n → ℝ` the product half-space is homeomorphic to Mathlib's half-space
`EuclideanHalfSpace (n + 1)`, by moving the height to coordinate `0`
(`TauCeti.halfSpaceHomeomorphEuclideanHalfSpace`). Read in the model vector spaces this
homeomorphism is the restriction of a continuous linear equivalence, so it identifies the two
models in every regularity class that is invariant under linear changes of coordinates.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1.
-/

public section

open Set

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The half-space model with tangential space `E` and nonnegative last coordinate. -/
noncomputable def modelWithCornersHalfSpace :
    ModelWithCorners ℝ (E × ℝ) {q : E × ℝ | 0 ≤ q.2} := by
  let φ : PartialEquiv {q : E × ℝ | 0 ≤ q.2} (E × ℝ) := {
    toFun := Subtype.val
    invFun := fun q => ⟨(q.1, max q.2 0), by exact le_max_right q.2 (0 : ℝ)⟩
    source := univ
    target := {q | 0 ≤ q.2}
    map_source' := fun q _ => q.2
    map_target' := fun _ _ => mem_univ _
    left_inv' := fun q _ => Subtype.ext (Prod.ext rfl (max_eq_left q.2))
    right_inv' := fun q hq => Prod.ext rfl (max_eq_left hq) }
  apply ModelWithCorners.ofConvexRange φ rfl
    (convex_halfSpace_ge (LinearMap.snd ℝ E ℝ).isLinear 0) continuous_subtype_val
    ((continuous_fst.prodMk (continuous_snd.max continuous_const)).subtype_mk _)
  refine ⟨(0, 1), mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset
    ((isOpen_lt (continuous_const (y := (0 : ℝ))) continuous_snd).mem_nhds (by norm_num))
    (fun q hq => hq.le)

/-- The half-space model embeds by the subtype inclusion. -/
@[simp] theorem modelWithCornersHalfSpace_apply (q : {q : E × ℝ | 0 ≤ q.2}) :
    modelWithCornersHalfSpace E q = q.1 := (rfl)

/-- The inverse clips negative heights to zero. -/
theorem modelWithCornersHalfSpace_symm_apply (q : E × ℝ) :
    (modelWithCornersHalfSpace E).symm q = ⟨(q.1, max q.2 0),
      by exact le_max_right q.2 (0 : ℝ)⟩ := (rfl)

/-- On the half-space, the model inverse leaves the ambient coordinates unchanged. -/
theorem coe_modelWithCornersHalfSpace_symm_apply {q : E × ℝ} (hq : 0 ≤ q.2) :
    ((modelWithCornersHalfSpace E).symm q).1 = q := by
  simp [modelWithCornersHalfSpace_symm_apply, max_eq_left hq]

/-- The range of the model is the closed half-space. -/
@[simp] theorem range_modelWithCornersHalfSpace :
    range (modelWithCornersHalfSpace E) = {q : E × ℝ | 0 ≤ q.2} :=
  Subtype.range_val

/-- The range of the model, the closed half-space, is a convex polyhedron: it is cut out by the
single inequality `-q.2 ≤ 0`. -/
theorem isConvexPolyhedron_range_modelWithCornersHalfSpace :
    IsConvexPolyhedron (range (modelWithCornersHalfSpace E)) := by
  rw [range_modelWithCornersHalfSpace]
  convert isConvexPolyhedron_setOf_le (-(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
    using 1
  ext q
  simp

/-- The model of the half-space, restricted to the points of positive height: an open partial
homeomorphism onto the open half-space `{q | 0 < q.2}` in `E × ℝ`. -/
noncomputable def halfSpaceInteriorChart :
    OpenPartialHomeomorph {q : E × ℝ | 0 ≤ q.2} (E × ℝ) where
  toFun := modelWithCornersHalfSpace E
  invFun := (modelWithCornersHalfSpace E).symm
  source := {q | 0 < q.1.2}
  target := {q | 0 < q.2}
  map_source' _ hq := hq
  map_target' q hq := by
    rw [mem_ofPred_eq] at hq ⊢
    rwa [coe_modelWithCornersHalfSpace_symm_apply E hq.le]
  left_inv' q _ := (modelWithCornersHalfSpace E).left_inv q
  right_inv' q hq := coe_modelWithCornersHalfSpace_symm_apply E (le_of_lt hq)
  open_source := isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)
  open_target := isOpen_lt continuous_const continuous_snd
  continuousOn_toFun := (modelWithCornersHalfSpace E).continuous.continuousOn
  continuousOn_invFun := (modelWithCornersHalfSpace E).continuous_symm.continuousOn

/-- The interior chart is the inclusion of the half-space. -/
@[simp, mfld_simps] theorem halfSpaceInteriorChart_apply (q : {q : E × ℝ | 0 ≤ q.2}) :
    halfSpaceInteriorChart E q = q.1 := (rfl)

/-- The inverse of the interior chart is the inverse of the model. -/
@[simp, mfld_simps] theorem halfSpaceInteriorChart_symm_apply (q : E × ℝ) :
    (halfSpaceInteriorChart E).symm q = (modelWithCornersHalfSpace E).symm q := (rfl)

/-- The interior chart is defined at the points of positive height. -/
@[simp, mfld_simps] theorem halfSpaceInteriorChart_source :
    (halfSpaceInteriorChart E).source = {q | 0 < q.1.2} := (rfl)

/-- The interior chart takes values in the open half-space. -/
@[simp, mfld_simps] theorem halfSpaceInteriorChart_target :
    (halfSpaceInteriorChart E).target = {q | 0 < q.2} := (rfl)

/-! ### Comparison with `EuclideanHalfSpace` -/

/-- The product half-space `{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}` is homeomorphic to Mathlib's
half-space `EuclideanHalfSpace (n + 1)`: the height `q.2` becomes coordinate `0` and the
tangential coordinates `q.1` become coordinates `1, …, n`. It is the restriction of the
continuous linear equivalence `q ↦ TauCeti.euclideanFinConsEquiv rfl (q.2, q.1)`. -/
noncomputable def halfSpaceHomeomorphEuclideanHalfSpace (n : ℕ) :
    {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} ≃ₜ EuclideanHalfSpace (n + 1) :=
  ((ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans
    (euclideanFinConsEquiv rfl)).toHomeomorph.subtype fun q => by simp

variable {n : ℕ}

/-- In ambient coordinates, `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` is
`q ↦ TauCeti.euclideanFinConsEquiv rfl (q.2, q.1)`. -/
theorem coe_halfSpaceHomeomorphEuclideanHalfSpace (q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}) :
    (halfSpaceHomeomorphEuclideanHalfSpace n q).1 = euclideanFinConsEquiv rfl (q.1.2, q.1.1) :=
  (rfl)

/-- In ambient coordinates, the inverse of `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` is
`y ↦ ((TauCeti.euclideanFinConsEquiv rfl).symm y).swap`. -/
theorem coe_halfSpaceHomeomorphEuclideanHalfSpace_symm (y : EuclideanHalfSpace (n + 1)) :
    ((halfSpaceHomeomorphEuclideanHalfSpace n).symm y).1 =
      ((euclideanFinConsEquiv rfl).symm y.1).swap := (rfl)

/-- `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` puts the height in coordinate `0`. -/
@[simp]
theorem halfSpaceHomeomorphEuclideanHalfSpace_apply_zero
    (q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}) :
    (halfSpaceHomeomorphEuclideanHalfSpace n q).1 0 = q.1.2 := by
  simp [coe_halfSpaceHomeomorphEuclideanHalfSpace]

/-- `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` puts the tangential coordinates in
coordinates `1, …, n`. -/
@[simp]
theorem halfSpaceHomeomorphEuclideanHalfSpace_apply_succ
    (q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}) (i : Fin n) :
    (halfSpaceHomeomorphEuclideanHalfSpace n q).1 i.succ = q.1.1 i := by
  simp [coe_halfSpaceHomeomorphEuclideanHalfSpace]

/-- The inverse of `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` reads the tangential
coordinates from coordinates `1, …, n`. -/
@[simp]
theorem halfSpaceHomeomorphEuclideanHalfSpace_symm_apply_fst (y : EuclideanHalfSpace (n + 1))
    (i : Fin n) :
    ((halfSpaceHomeomorphEuclideanHalfSpace n).symm y).1.1 i = y.1 i.succ := by
  simp [coe_halfSpaceHomeomorphEuclideanHalfSpace_symm]

/-- The inverse of `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` reads the height from
coordinate `0`. -/
@[simp]
theorem halfSpaceHomeomorphEuclideanHalfSpace_symm_apply_snd (y : EuclideanHalfSpace (n + 1)) :
    ((halfSpaceHomeomorphEuclideanHalfSpace n).symm y).1.2 = y.1 0 := by
  simp [coe_halfSpaceHomeomorphEuclideanHalfSpace_symm]

end TauCeti
