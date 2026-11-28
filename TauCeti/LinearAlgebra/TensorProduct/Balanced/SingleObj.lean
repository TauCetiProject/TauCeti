/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.SingleObj
public import TauCeti.CategoryTheory.Preadditive.ModCat.Tensor
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# The balanced tensor product as a one-object coend

The left and right modules over a ring `A` give a contravariant and a covariant additive
functor on `SingleObj Aᵐᵒᵖ`. Their coend tensor is isomorphic to the balanced tensor
product over `A` formed over `ℤ`. The isomorphism is natural in both factors and
identifies the two classes of a pure tensor.

The presentation of the tensor product of functors by balancing along morphisms is due
to Mitchell, *Rings with several objects*, §6, pp. 26–27. For the one-object category,
the two actions in those relations are the two module actions given by
`moduleCatMulOppositeEquivModCatOp` and `moduleCatEquivModCat`.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.BalancedTensorProduct

variable {A : Type u} [Ring A] [Small.{v} A]
  {M M' : ModuleCat.{v} Aᵐᵒᵖ} {N N' : ModuleCat.{v} A}

private abbrev rightFunctor (M : ModuleCat.{v} Aᵐᵒᵖ) :=
  (moduleCatMulOppositeEquivModCatOp A).functor.obj M

private abbrev leftFunctor (N : ModuleCat.{v} A) :=
  (moduleCatEquivModCat A).functor.obj N

private noncomputable def fromCoend :
    ModCat.tensorObj (rightFunctor M) (leftFunctor N) ⟶
      AddCommGrpCat.of (BalancedTensorProduct ℤ A M N) :=
  ModCat.tensorDesc (fun _ ↦ mk ℤ A (M := M) (N := N)) fun {_ _} f m n ↦ by
    rw [moduleCatMulOppositeEquivModCatOp_functor_obj_obj_map,
      moduleCatEquivModCat_functor_obj_obj_map]
    let x : M := m
    let y : N := n
    have h := balance ℤ A (MulOpposite.unop f) x y
    rw [MulOpposite.op_unop, ← mk_apply, ← mk_apply] at h
    exact h

private noncomputable def toCoend :
    AddCommGrpCat.of (BalancedTensorProduct ℤ A M N) ⟶
      ModCat.tensorObj (rightFunctor M) (leftFunctor N) := by
  let b : M →ₗ[ℤ] N →ₗ[ℤ] ModCat.tensorObj (rightFunctor M) (leftFunctor N) :=
    ModCat.tmulLinear (G := rightFunctor M) (F := leftFunctor N) (SingleObj.star Aᵐᵒᵖ)
  refine AddCommGrpCat.ofHom (lift b (fun a m n ↦ ?_)).toAddMonoidHom
  have h := ModCat.tmul_balance (G := rightFunctor M) (F := leftFunctor N)
    (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a) m n
  rw [moduleCatMulOppositeEquivModCatOp_functor_obj_obj_map,
    moduleCatEquivModCat_functor_obj_obj_map] at h
  exact h

private theorem fromCoend_tmul (X : SingleObj Aᵐᵒᵖ) (m : M) (n : N) :
    fromCoend (ModCat.tmul X m n) = tmul ℤ A m n := by
  unfold fromCoend
  -- Match the descent equation across the module values and their underlying groups.
  erw [ModCat.tensorDesc_tmul]
  exact mk_apply ℤ A m n

private theorem toCoend_tmul (m : M) (n : N) :
    toCoend (tmul ℤ A m n) = ModCat.tmul (SingleObj.star Aᵐᵒᵖ) m n := by
  unfold toCoend
  exact lift_tmul _ _ m n

/-- The tensor over a one-object category is the balanced tensor product of the
corresponding right and left modules over the ring, with ground ring `ℤ`. -/
noncomputable def tensorObjSingleObjIso (M : ModuleCat.{v} Aᵐᵒᵖ) (N : ModuleCat.{v} A) :
    ModCat.tensorObj ((moduleCatMulOppositeEquivModCatOp A).functor.obj M)
        ((moduleCatEquivModCat A).functor.obj N) ≅
      AddCommGrpCat.of (BalancedTensorProduct ℤ A M N) where
  hom := fromCoend
  inv := toCoend
  hom_inv_id := ModCat.tensorObj_hom_ext fun X m n ↦ by
    obtain rfl : X = SingleObj.star Aᵐᵒᵖ := Subsingleton.elim _ _
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply]
    exact (congrArg (fun z ↦ toCoend (M := M) (N := N) z)
      (fromCoend_tmul (SingleObj.star Aᵐᵒᵖ) (m : M) (n : N))).trans (toCoend_tmul m n)
  inv_hom_id := by
    apply AddCommGrpCat.ext
    intro z
    induction z using induction_on with
    | ht m n =>
      rw [AddCommGrpCat.comp_apply, toCoend_tmul, fromCoend_tmul, AddCommGrpCat.id_apply]
    | ha z w hz hw => simp only [map_add, hz, hw]

-- Apply the pure-tensor rules before simplifying the bundled group-morphism applications.
/-- The comparison sends a coend pure tensor to the balanced pure tensor. -/
@[simp↓]
theorem tensorObjSingleObjIso_hom_tmul (X : SingleObj Aᵐᵒᵖ) (m : M) (n : N) :
    (tensorObjSingleObjIso M N).hom (ModCat.tmul X m n) = tmul ℤ A m n :=
  fromCoend_tmul X m n

/-- The inverse comparison sends a balanced pure tensor to the coend pure tensor at the
unique object. -/
@[simp↓]
theorem tensorObjSingleObjIso_inv_tmul (m : M) (n : N) :
    (tensorObjSingleObjIso M N).inv (tmul ℤ A m n) =
      ModCat.tmul (SingleObj.star Aᵐᵒᵖ) m n :=
  toCoend_tmul m n

/-- Comparing the tensor products commutes with applying module maps in both factors. -/
theorem tensorObjSingleObjIso_naturality (f : M ⟶ M') (g : N ⟶ N') :
    (ModCat.tensor.map ((moduleCatMulOppositeEquivModCatOp A).functor.map f)).app
        ((moduleCatEquivModCat A).functor.obj N) ≫
      (ModCat.tensor.obj ((moduleCatMulOppositeEquivModCatOp A).functor.obj M')).map
        ((moduleCatEquivModCat A).functor.map g) ≫
      (tensorObjSingleObjIso M' N').hom =
    (tensorObjSingleObjIso M N).hom ≫ AddCommGrpCat.ofHom
      (map (f.hom.restrictScalars ℤ) (g.hom.restrictScalars ℤ)
        (fun a m ↦ by simpa only [LinearMap.restrictScalars_apply] using
          f.hom.map_smul (MulOpposite.op a) m)
        (fun a n ↦ by simpa only [LinearMap.restrictScalars_apply] using
          g.hom.map_smul a n)).toAddMonoidHom := by
  apply ModCat.tensorObj_hom_ext
  intro X m n
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
    ModCat.tensor_map_app_tmul, ModCat.tensor_obj_map_tmul,
    moduleCatMulOppositeEquivModCatOp_functor_map_hom_app,
    moduleCatEquivModCat_functor_map_hom_app]
  -- The component group maps are the underlying maps of `f` and `g`.
  erw [tensorObjSingleObjIso_hom_tmul X (f.hom (m : M)) (g.hom (n : N)),
    tensorObjSingleObjIso_hom_tmul X (m : M) (n : N)]
  exact (map_tmul (A := A) (f.hom.restrictScalars ℤ) (g.hom.restrictScalars ℤ)
    _ _ (m : M) (n : N)).symm

end TauCeti.BalancedTensorProduct
