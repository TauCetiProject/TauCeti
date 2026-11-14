/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import TauCeti.CategoryTheory.Adjunction.Additive
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic

/-!
# Additive closures under dualities

An object `X` lies in the additive closure `add M` exactly when the identity of `X` is a finite sum
of composites `X ⟶ M ⟶ X` (`TauCeti.additiveClosure_iff_exists_sum_comp_eq_id`). This form of
membership mentions no biproducts, so it reverses under passing to the opposite category: an
additive, fully faithful functor `F : Cᵒᵖ ⥤ D` carries `X ∈ add M` to `F (op X) ∈ add (F (op M))`
and back (`CategoryTheory.Functor.additiveClosure_obj_op_iff`). In particular a duality
`e : Cᵒᵖ ≌ D`, which is automatically additive, carries `X ∈ add M` to `e (op X) ∈ add (e (op M))`
and back (`CategoryTheory.Equivalence.additiveClosure_functor_obj_op_iff`). This is how a statement
about additive closures of projective objects is dualized to one about injective objects.

## Main results

* `CategoryTheory.Functor.additiveClosure_obj_op_iff`: an additive, fully faithful functor
  `Cᵒᵖ ⥤ D` preserves and reflects membership in additive closures.
* `CategoryTheory.Equivalence.additiveClosure_functor_obj_op_iff`: a duality `Cᵒᵖ ≌ D` preserves
  and reflects membership in additive closures.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TauCeti

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]

/-- **Additive closures under a contravariant fully faithful functor**: for an additive, fully
faithful functor `F : Cᵒᵖ ⥤ D`, `F (op X)` lies in `add (F (op M))` exactly when `X` lies in
`add M`. Sums of composites `X ⟶ M ⟶ X` and `F (op X) ⟶ F (op M) ⟶ F (op X)` correspond under `F`
with the order of composition reversed. -/
theorem CategoryTheory.Functor.additiveClosure_obj_op_iff (F : Cᵒᵖ ⥤ D) [F.Full] [F.Faithful]
    [F.Additive] {M X : C} :
    additiveClosure (F.obj (op M)) (F.obj (op X)) ↔ additiveClosure M X := by
  simp only [additiveClosure_iff_exists_sum_comp_eq_id]
  refine ⟨fun ⟨n, a, b, h⟩ ↦ ⟨n, fun j ↦ (F.preimage (b j)).unop,
    fun j ↦ (F.preimage (a j)).unop, ?_⟩, fun ⟨n, a, b, h⟩ ↦
      ⟨n, fun j ↦ F.map (b j).op, fun j ↦ F.map (a j).op, ?_⟩⟩
  · refine Quiver.Hom.op_inj (F.map_injective ?_)
    simp [← unop_comp, ← h]
  · simp only [← Functor.map_comp, ← op_comp]
    rw [← Functor.map_sum, ← op_sum, h, op_id, F.map_id]

/-- **Additive closures under a duality**: for an equivalence `e : Cᵒᵖ ≌ D`, `e (op X)` lies in
`add (e (op M))` exactly when `X` lies in `add M`. The functor of `e` is additive, as a right
adjoint between preadditive categories. -/
theorem CategoryTheory.Equivalence.additiveClosure_functor_obj_op_iff (e : Cᵒᵖ ≌ D) {M X : C} :
    additiveClosure (e.functor.obj (Opposite.op M)) (e.functor.obj (Opposite.op X)) ↔
      additiveClosure M X :=
  e.functor.additiveClosure_obj_op_iff
