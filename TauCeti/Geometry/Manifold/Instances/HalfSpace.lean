/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# A product half-space model

The closed half-space in `E × ℝ`, with the last coordinate nonnegative, is a model with
corners. Its inverse clips the last coordinate at zero. Keeping the tangential space
explicit allows polyhedral boundary charts to use product coordinates directly.

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

end TauCeti
