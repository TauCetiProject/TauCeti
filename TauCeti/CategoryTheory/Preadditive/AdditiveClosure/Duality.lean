/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure

/-!
# Additive closures under dualities

An object `X` lies in the additive closure `add M` exactly when the identity of `X` is a finite sum
of composites `X ⟶ M ⟶ X` (`TauCeti.additiveClosure_iff_exists_sum_comp_eq_id`). This form of
membership mentions no biproducts, so it reverses under passing to the opposite category: a
duality `Cᵒᵖ ≌ D` carries `X ∈ add M` to `D X ∈ add (D M)` and back
(`TauCeti.additiveClosure_functor_obj_op_iff`). This is how a statement about additive closures of
projective objects is dualized to one about injective objects.

## Main results

* `TauCeti.additiveClosure_iff_exists_sum_comp_eq_id`: `X ∈ add M` exactly when `𝟙 X` is a finite
  sum of composites `X ⟶ M ⟶ X`.
* `TauCeti.additiveClosure_le_of_retract`: `add M ≤ add N` when `M` is a direct summand of `N`.
* `TauCeti.additiveClosure_functor_obj_op_iff`: a duality `Cᵒᵖ ≌ D` preserves and reflects
  membership in additive closures.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- **Additive closures through sums of composites**: `X` lies in `add M` exactly when the identity
of `X` is a finite sum of composites `X ⟶ M ⟶ X`. -/
theorem additiveClosure_iff_exists_sum_comp_eq_id {M X : C} :
    additiveClosure M X ↔
      ∃ (n : ℕ) (a : Fin n → (X ⟶ M)) (b : Fin n → (M ⟶ X)), ∑ j, a j ≫ b j = 𝟙 X := by
  rw [additiveClosure_iff]
  refine ⟨fun ⟨n, ⟨h⟩⟩ ↦ ⟨n, fun j ↦ h.i ≫ biproduct.π (fun _ : Fin n ↦ M) j,
    fun j ↦ biproduct.ι (fun _ : Fin n ↦ M) j ≫ h.r, ?_⟩, fun ⟨n, a, b, h⟩ ↦
      ⟨n, ⟨⟨biproduct.lift a, biproduct.desc b, by rw [biproduct.lift_desc, h]⟩⟩⟩⟩
  have hs : ∑ j, (h.i ≫ biproduct.π (fun _ : Fin n ↦ M) j) ≫
      biproduct.ι (fun _ : Fin n ↦ M) j ≫ h.r =
      h.i ≫ (∑ j, biproduct.π (fun _ : Fin n ↦ M) j ≫ biproduct.ι (fun _ : Fin n ↦ M) j) ≫
        h.r := by
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  rw [hs, biproduct.total, Category.id_comp, h.retract]

/-- **Additive closures grow along retracts**: if `M` is a direct summand of `N`, then
`add M ≤ add N`. -/
theorem additiveClosure_le_of_retract {M N : C} (h : Retract M N) :
    additiveClosure M ≤ additiveClosure N :=
  additiveClosure_le_iff.2 ((additiveClosure N).prop_of_retract h (additiveClosure_self N))

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]

/-- **Additive closures under a duality**: for an equivalence `e : Cᵒᵖ ≌ D`, `e (op X)` lies in
`add (e (op M))` exactly when `X` lies in `add M`. Sums of composites `X ⟶ M ⟶ X` and
`e (op X) ⟶ e (op M) ⟶ e (op X)` correspond under `e` with the order of composition reversed;
`e` is additive, as it preserves binary products. -/
theorem additiveClosure_functor_obj_op_iff (e : Cᵒᵖ ≌ D) {M X : C} :
    additiveClosure (e.functor.obj (op M)) (e.functor.obj (op X)) ↔ additiveClosure M X := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  simp only [additiveClosure_iff_exists_sum_comp_eq_id]
  constructor
  · rintro ⟨n, a, b, h⟩
    let a' : Fin n → (op X ⟶ op M) := fun j ↦
      e.unitIso.hom.app (op X) ≫ e.inverse.map (a j) ≫ e.unitIso.inv.app (op M)
    let b' : Fin n → (op M ⟶ op X) := fun j ↦
      e.unitIso.hom.app (op M) ≫ e.inverse.map (b j) ≫ e.unitIso.inv.app (op X)
    refine ⟨n, fun j ↦ (b' j).unop, fun j ↦ (a' j).unop, ?_⟩
    have h' : ∑ j, a' j ≫ b' j = 𝟙 (op X) := by
      calc ∑ j, a' j ≫ b' j
          = e.unitIso.hom.app (op X) ≫ e.inverse.map (∑ j, a j ≫ b j) ≫
              e.unitIso.inv.app (op X) := by
            simp only [a', b', Functor.map_sum, Functor.map_comp, Preadditive.comp_sum,
              Preadditive.sum_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
        _ = 𝟙 (op X) := by simp [h]
    have h'' := congrArg Quiver.Hom.unop h'
    rw [unop_sum, unop_id] at h''
    simpa only [unop_comp] using h''
  · rintro ⟨n, a, b, h⟩
    refine ⟨n, fun j ↦ e.functor.map (b j).op, fun j ↦ e.functor.map (a j).op, ?_⟩
    simp only [← Functor.map_comp, ← op_comp]
    rw [← Functor.map_sum, ← op_sum, h, op_id, e.functor.map_id]

end TauCeti
