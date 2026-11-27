/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Topology.Algebra.Support

/-!
# Extension by zero of test functions from an open subset

An open subset `U` of a manifold `G` is a manifold with the induced charts, so it has its own
test functions `LieTestFunction I U`. Extending such a test function by zero outside `U` gives a
test function on `G` when `G` is Hausdorff: the support closure is a compact subset of `U`, so the
extension vanishes near every point outside `U`. Conversely, a test function on `G` whose support
closure lies in `U` restricts to a test function on `U`, and the two operations are inverse.

## Main definitions

* `TauCeti.LieTestFunction.extendByZero U`: the `ℂ`-linear extension by zero
  `LieTestFunction I U → LieTestFunction I G`.
* `TauCeti.LieTestFunction.restrict a h`: the restriction to `U` of a test function `a` with
  `tsupport a ⊆ U`.

## Main results

* `TauCeti.LieTestFunction.tsupport_extendByZero`: the support closure of `extendByZero U a` is
  the image of that of `a`.
* `TauCeti.LieTestFunction.extendByZero_restrict`, `restrict_extendByZero`: extension by zero and
  restriction are inverse to each other.
-/

public section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace LieTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] (U : Opens G)

section ExtendByZero

variable [T2Space G]

/-- Extension by zero of test functions on an open subset `U` of `G`:
`extendByZero U a x = a x` for `x ∈ U`, and `0` otherwise. -/
noncomputable def extendByZero : LieTestFunction I U →ₗ[ℂ] LieTestFunction I G where
  toFun a := ⟨Subtype.val.extend a 0, a.contMDiff.extend_zero a.hasCompactSupport,
    a.hasCompactSupport.extend_zero continuous_subtypeVal⟩
  map_add' a b := DFunLike.coe_injective <| by
    simpa using extend_add Subtype.val (⇑a) (⇑b) (0 : G → ℂ) 0
  map_smul' c a := DFunLike.coe_injective <| by
    simpa using extend_smul c Subtype.val (⇑a) (0 : G → ℂ)

theorem coe_extendByZero (a : LieTestFunction I U) :
    ⇑(extendByZero U a) = Subtype.val.extend a 0 :=
  (rfl)

@[simp]
theorem extendByZero_apply_coe (a : LieTestFunction I U) (x : U) : extendByZero U a x = a x :=
  Function.extend_val_apply x.property

theorem extendByZero_apply_of_notMem (a : LieTestFunction I U) {x : G} (hx : x ∉ U) :
    extendByZero U a x = 0 :=
  Function.extend_val_apply' hx

@[simp]
theorem support_extendByZero (a : LieTestFunction I U) :
    support (extendByZero U a) = (↑) '' support a := by
  rw [coe_extendByZero, support_extend_zero Subtype.val_injective]

@[simp]
theorem tsupport_extendByZero (a : LieTestFunction I U) :
    tsupport (extendByZero U a) = (↑) '' tsupport a := by
  rw [coe_extendByZero,
    a.hasCompactSupport.tsupport_extend_zero continuous_subtypeVal Subtype.val_injective]

theorem tsupport_extendByZero_subset (a : LieTestFunction I U) :
    tsupport (extendByZero U a) ⊆ U := by
  rw [tsupport_extendByZero]
  exact Subtype.coe_image_subset _ _

theorem extendByZero_injective : Injective (extendByZero (I := I) U) :=
  fun a b h ↦ ext fun x ↦ by simpa using congr($h x)

end ExtendByZero

section Restrict

variable {U}

/-- The restriction to an open subset `U` of a test function `a` with `tsupport a ⊆ U`. -/
def restrict (a : LieTestFunction I G) (h : tsupport a ⊆ U) : LieTestFunction I U :=
  ⟨fun x ↦ a x, a.contMDiff.comp contMDiff_subtypeVal, a.hasCompactSupport.comp_subtypeVal h⟩

@[simp]
theorem restrict_apply (a : LieTestFunction I G) (h : tsupport a ⊆ U) (x : U) :
    restrict a h x = a x :=
  (rfl)

@[simp]
theorem support_restrict (a : LieTestFunction I G) (h : tsupport a ⊆ U) :
    support (restrict a h) = (↑) ⁻¹' support a := by
  ext
  simp

@[simp]
theorem tsupport_restrict (a : LieTestFunction I G) (h : tsupport a ⊆ U) :
    tsupport (restrict a h) = (↑) ⁻¹' tsupport a := by
  rw [tsupport, support_restrict]
  exact (U.isOpen.isOpenMap_subtypeVal.preimage_closure_eq_closure_preimage
    continuous_subtypeVal _).symm

theorem restrict_add (a b : LieTestFunction I G) (ha : tsupport a ⊆ U) (hb : tsupport b ⊆ U) :
    restrict (a + b) ((tsupport_add a b).trans (union_subset ha hb)) =
      restrict a ha + restrict b hb :=
  (rfl)

theorem restrict_smul (c : ℂ) (a : LieTestFunction I G) (ha : tsupport a ⊆ U) :
    restrict (c • a) ((tsupport_smul_subset_right (fun _ ↦ c) a).trans ha) =
      c • restrict a ha :=
  (rfl)

variable [T2Space G]

@[simp]
theorem extendByZero_restrict (a : LieTestFunction I G) (h : tsupport a ⊆ U) :
    extendByZero U (restrict a h) = a :=
  ext fun x ↦ by
    by_cases hx : x ∈ U
    · lift x to U using hx
      simp
    · rw [extendByZero_apply_of_notMem U _ hx,
        image_eq_zero_of_notMem_tsupport fun h' ↦ hx (h h')]

@[simp]
theorem restrict_extendByZero (a : LieTestFunction I U) :
    restrict (extendByZero U a) (tsupport_extendByZero_subset U a) = a :=
  ext fun x ↦ by simp

end Restrict

end LieTestFunction

end TauCeti
