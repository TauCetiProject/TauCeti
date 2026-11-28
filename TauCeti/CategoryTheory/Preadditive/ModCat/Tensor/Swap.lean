/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Opposite
public import TauCeti.CategoryTheory.Preadditive.ModCat.Tensor.Basic

/-!
# Swapping the factors of the tensor product over a preadditive category

The tensor product over `C` agrees with the tensor product over `Cᵒᵖ` in the reverse order.
The comparison is natural in both modules and exchanges the entries of a pure tensor.
It follows from the balanced presentation of the tensor product in B. Mitchell,
*Rings with several objects*, Adv. Math. 8 (1972), 1–161, §6, pp. 26–27.
-/

public section

open CategoryTheory Opposite

universe w v u

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{w} C]

private noncomputable def tensorSwapHom (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) :
    tensorObj G F ⟶ tensorObj ((opOpEquiv C).functor.obj F) G :=
  tensorDesc (G := G) (F := F)
    (fun X ↦ (tmulLinear (G := (opOpEquiv C).functor.obj F) (F := G) (op X)).flip)
    fun _ _ f x y ↦ (tmul_balance (G := (opOpEquiv C).functor.obj F) (F := G) f.op y x).symm

private noncomputable def tensorSwapInv (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) :
    tensorObj ((opOpEquiv C).functor.obj F) G ⟶ tensorObj G F :=
  tensorDesc (G := (opOpEquiv C).functor.obj F) (F := G)
    (fun X ↦ (tmulLinear (G := G) (F := F) X.unop).flip)
    fun _ _ f y x ↦ (tmul_balance (G := G) (F := F) f.unop x y).symm

private lemma tensorSwapHom_tmul (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tensorSwapHom G F (tmul X x y) = tmul (op X) y x :=
  tensorDesc_tmul (G := G) (F := F) _ _ X x y

private lemma tensorSwapInv_tmul (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (X : Cᵒᵖ)
    (y : ((opOpEquiv C).functor.obj F).obj.obj (op (op X))) (x : G.obj.obj (op X)) :
    tensorSwapInv G F (tmul X y x) = tmul X.unop x y :=
  tensorDesc_tmul (G := (opOpEquiv C).functor.obj F) (F := G) _ _ X y x

/-- Swap the factors of the tensor product, changing the base category to its opposite. -/
noncomputable def tensorObjSwapIso (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) :
    tensorObj G F ≅ tensorObj ((opOpEquiv C).functor.obj F) G where
  hom := tensorSwapHom G F
  inv := tensorSwapInv G F
  hom_inv_id := by
    apply tensorObj_hom_ext
    intro X x y
    rw [AddCommGrpCat.comp_apply, tensorSwapHom_tmul]
    exact tensorSwapInv_tmul G F (op X) y x
  inv_hom_id := by
    apply tensorObj_hom_ext
    intro X y x
    rw [AddCommGrpCat.comp_apply, tensorSwapInv_tmul G F X y x,
      tensorSwapHom_tmul G F X.unop x y]
    rfl

/-- The tensor swap exchanges the entries of a pure tensor at `X`. -/
@[simp]
lemma tensorObjSwapIso_hom_tmul (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    (tensorObjSwapIso G F).hom (tmul X x y) = tmul (op X) y x :=
  tensorSwapHom_tmul G F X x y

/-- The inverse tensor swap exchanges the entries of a pure tensor at `X`. -/
@[simp]
lemma tensorObjSwapIso_inv_tmul (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (X : Cᵒᵖ)
    (y : ((opOpEquiv C).functor.obj F).obj.obj (op (op X))) (x : G.obj.obj (op X)) :
    (tensorObjSwapIso G F).inv (tmul X y x) = tmul X.unop x y :=
  tensorSwapInv_tmul G F X y x

/-- Swapping the factors is natural in the right and left module. -/
noncomputable def tensorSwapIso :
    tensor (C := C) ≅ ((opOpEquiv C).functor ⋙ tensor (C := Cᵒᵖ)).flip := by
  refine NatIso.ofComponents (fun G ↦ NatIso.ofComponents (tensorObjSwapIso G) ?_) ?_
  · intro F F' f
    apply tensorObj_hom_ext
    intro X x y
    simp only [Functor.flip_obj_map, Functor.comp_map, AddCommGrpCat.comp_apply,
      tensor_obj_map_tmul]
    rw [tensorObjSwapIso_hom_tmul, tensorObjSwapIso_hom_tmul]
    exact (tensor_map_app_tmul ((opOpEquiv C).functor.map f) G (op X) y x).symm
  · intro G G' g
    apply NatTrans.ext
    funext F
    apply tensorObj_hom_ext
    intro X x y
    simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Functor.flip_map_app,
      Functor.comp_obj, AddCommGrpCat.comp_apply, tensor_map_app_tmul]
    rw [tensorObjSwapIso_hom_tmul, tensorObjSwapIso_hom_tmul]
    exact (tensor_obj_map_tmul ((opOpEquiv C).functor.obj F) g (op X) y x).symm

/-- The component of the bifunctor comparison is the tensor swap at the given modules. -/
@[simp]
lemma tensorSwapIso_app_app (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) :
    ((tensorSwapIso (C := C)).app G).app F = tensorObjSwapIso G F :=
  (rfl)

end TauCeti.ModCat
