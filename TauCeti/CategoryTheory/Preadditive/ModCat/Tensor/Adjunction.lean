/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import TauCeti.CategoryTheory.Preadditive.ModCat.Tensor.Basic

/-!
# Tensor–Hom adjunctions for modules over a preadditive category

In each variable, tensoring over a preadditive category is left adjoint to the pointwise
Hom functor. Precomposition gives the Hom module its action, and the adjunction evaluates
on classes of pure tensors. In particular, both partial tensor functors preserve colimits.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §6, equation (2), p. 26.
-/

public section

open CategoryTheory CategoryTheory.Functor Opposite Limits

universe w v u

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Pointwise Hom from a right module into an abelian group, with its left module structure
given by precomposition. -/
@[expose] noncomputable def tensorHomRight :
    (ModCat.{w} Cᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{w} ⥤ ModCat.{w} C :=
  curry.obj (ObjectProperty.lift _
    (uncurry.obj ((additiveFunctor _ _).ι.op ⋙
      (leftOpRightOpEquiv (C := Cᵒᵖ) (D := AddCommGrpCat.{w})).functor ⋙
      whiskeringLeft _ _ _ ⋙ (whiskeringLeft _ _ _).obj preadditiveYoneda))
    fun ⟨G, A⟩ ↦ (additiveFunctor_iff _).mpr
      (inferInstanceAs (G.unop.obj.rightOp ⋙ preadditiveYoneda.obj A).Additive))

/-- Pointwise Hom from a left module into an abelian group, with its right module structure
given by precomposition. -/
@[expose] noncomputable def tensorHomLeft :
    (ModCat.{w} C)ᵒᵖ ⥤ AddCommGrpCat.{w} ⥤ ModCat.{w} Cᵒᵖ :=
  curry.obj (ObjectProperty.lift _
    (uncurry.obj ((additiveFunctor _ _).ι.op ⋙
      (opUnopEquiv (C := Cᵒᵖ) (D := AddCommGrpCat.{w})).functor ⋙
      whiskeringLeft _ _ _ ⋙ (whiskeringLeft _ _ _).obj preadditiveYoneda))
    fun ⟨F, A⟩ ↦ (additiveFunctor_iff _).mpr
      (inferInstanceAs (F.unop.obj.op ⋙ preadditiveYoneda.obj A).Additive))

section HomActions

variable {G G' : ModCat.{w} Cᵒᵖ} {F F' : ModCat.{w} C} {A B : AddCommGrpCat.{w}}

/-- The value of the Hom module from a right module is the group of maps out of its value. -/
@[simp]
lemma tensorHomRight_obj_obj_obj (X : Cᵒᵖ) :
    ((tensorHomRight.obj (op G)).obj A).obj.obj X =
      AddCommGrpCat.of (G.obj.obj (op X) ⟶ A) := (rfl)

/-- The value of the Hom module from a left module is the group of maps out of its value. -/
@[simp]
lemma tensorHomLeft_obj_obj_obj (X : Cᵒᵖᵒᵖ) :
    ((tensorHomLeft.obj (op F)).obj A).obj.obj X =
      AddCommGrpCat.of (F.obj.obj X.unop ⟶ A) := (rfl)

/-- The left module structure on Hom from a right module is precomposition. -/
@[simp]
lemma tensorHomRight_obj_obj_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (g : G.obj.obj (op X) ⟶ A) :
    ((tensorHomRight.obj (op G)).obj A).obj.map f g = G.obj.map f.op ≫ g := (rfl)

/-- A map in the target group acts by postcomposition on Hom from a right module. -/
@[simp]
lemma tensorHomRight_obj_map_app_apply (a : A ⟶ B) (X : Cᵒᵖ)
    (g : G.obj.obj (op X) ⟶ A) :
    ((tensorHomRight.obj (op G)).map a).hom.app X g = g ≫ a := (rfl)

/-- A map between right modules acts by precomposition on their Hom modules. -/
@[simp]
lemma tensorHomRight_map_app_app_apply (a : G ⟶ G') (X : Cᵒᵖ)
    (g : G'.obj.obj (op X) ⟶ A) :
    ((tensorHomRight.map a.op).app A).hom.app X g = a.hom.app (op X) ≫ g := (rfl)

/-- The right module structure on Hom from a left module is precomposition. -/
@[simp]
lemma tensorHomLeft_obj_obj_map_apply {X Y : Cᵒᵖᵒᵖ} (f : X ⟶ Y)
    (g : F.obj.obj X.unop ⟶ A) :
    ((tensorHomLeft.obj (op F)).obj A).obj.map f g = F.obj.map f.unop ≫ g := (rfl)

/-- A map in the target group acts by postcomposition on Hom from a left module. -/
@[simp]
lemma tensorHomLeft_obj_map_app_apply (a : A ⟶ B) (X : Cᵒᵖᵒᵖ)
    (g : F.obj.obj X.unop ⟶ A) :
    ((tensorHomLeft.obj (op F)).map a).hom.app X g = g ≫ a := (rfl)

/-- A map between left modules acts by precomposition on their Hom modules. -/
@[simp]
lemma tensorHomLeft_map_app_app_apply (a : F ⟶ F') (X : Cᵒᵖᵒᵖ)
    (g : F'.obj.obj X.unop ⟶ A) :
    ((tensorHomLeft.map a.op).app A).hom.app X g = a.hom.app X.unop ≫ g := (rfl)

end HomActions

/-- Identify the values of the pointwise Hom modules with `ℤ`-linear maps for tensor descent. -/
private def tensorHomValueLinearEquiv (P A : AddCommGrpCat.{w}) :
    (P ⟶ A) ≃ₗ[ℤ] (P →ₗ[ℤ] A) :=
  AddCommGrpCat.homAddEquiv.toIntLinearEquiv.trans (addMonoidHomLequivInt ℤ)

section Adjunction

variable [EssentiallySmall.{w} C]
variable {G : ModCat.{w} Cᵒᵖ} {F : ModCat.{w} C} {A : AddCommGrpCat.{w}}

private noncomputable def tensorHomRightEquiv :
    (tensorObj G F ⟶ A) ≃ (F ⟶ (tensorHomRight.obj (op G)).obj A) where
  toFun h := ObjectProperty.homMk
    { app := fun X ↦ AddCommGrpCat.ofHom
        (((tensorHomValueLinearEquiv _ _).symm.toLinearMap ∘ₗ
          ((tmulLinear X.unop).flip.compr₂ h.hom.toIntLinearMap)).toAddMonoidHom)
      naturality := fun X Y f ↦ AddCommGrpCat.ext fun y ↦ AddCommGrpCat.ext fun x ↦
        congrArg (fun z : tensorObj G F ↦ h z) (tmul_balance f.unop x y).symm }
  invFun h := tensorDesc
    (fun X ↦ ((tensorHomValueLinearEquiv _ _).toLinearMap ∘ₗ
      (h.hom.app (op X)).hom.toIntLinearMap).flip)
    (fun X Y f x y ↦
      congrArg (fun k : G.obj.obj (op (op X)) ⟶ A ↦ k x)
        (ConcreteCategory.congr_hom (h.hom.naturality f.op) y).symm)
  left_inv h := by
    apply tensorObj_hom_ext
    intro X x y
    exact (tensorDesc_tmul _ _ X x y).trans rfl
  right_inv h := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply AddCommGrpCat.ext
    intro y
    apply AddCommGrpCat.ext
    intro x
    exact tensorDesc_tmul _ _ X.unop x y

private noncomputable def tensorHomLeftEquiv :
    (tensorObj G F ⟶ A) ≃ (G ⟶ (tensorHomLeft.obj (op F)).obj A) where
  toFun h := ObjectProperty.homMk
    { app := fun X ↦ AddCommGrpCat.ofHom
        (((tensorHomValueLinearEquiv _ _).symm.toLinearMap ∘ₗ
          (tmulLinear X.unop.unop).compr₂ h.hom.toIntLinearMap).toAddMonoidHom)
      naturality := fun X Y f ↦ AddCommGrpCat.ext fun x ↦ AddCommGrpCat.ext fun y ↦
        congrArg (fun z : tensorObj G F ↦ h z) (tmul_balance f.unop.unop x y) }
  invFun h := tensorDesc
    (fun X ↦ (tensorHomValueLinearEquiv _ _).toLinearMap ∘ₗ
      (h.hom.app (op (op X))).hom.toIntLinearMap)
    (fun X Y f x y ↦
      congrArg (fun k : F.obj.obj (op Y) ⟶ A ↦ k y)
        (ConcreteCategory.congr_hom (h.hom.naturality f.op.op) x))
  left_inv h := by
    apply tensorObj_hom_ext
    intro X x y
    exact (tensorDesc_tmul _ _ X x y).trans rfl
  right_inv h := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply AddCommGrpCat.ext
    intro x
    apply AddCommGrpCat.ext
    intro y
    exact tensorDesc_tmul _ _ X.unop.unop x y

private noncomputable def tensorRightCore (G : ModCat.{w} Cᵒᵖ) :
    Adjunction.CoreHomEquiv (tensor.obj G) (tensorHomRight.obj (op G)) where
  homEquiv _ _ := tensorHomRightEquiv
  homEquiv_naturality_left_symm {F' F A} f h := by
    apply tensorObj_hom_ext
    intro X x y
    calc
      _ = AddCommGrpCat.Hom.hom (X := G.obj.obj (op (op X))) (Y := A)
          (h.hom.app (op X) (f.hom.app (op X) y)) x := tensorDesc_tmul _ _ X x y
      _ = _ := by
        rw [AddCommGrpCat.comp_apply, tensor_obj_map_tmul]
        symm
        exact tensorDesc_tmul _ _ X x _
  homEquiv_naturality_right f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact AddCommGrpCat.ext fun y ↦ AddCommGrpCat.ext fun x ↦ rfl

private noncomputable def tensorLeftCore (F : ModCat.{w} C) :
    Adjunction.CoreHomEquiv (tensor.flip.obj F) (tensorHomLeft.obj (op F)) where
  homEquiv _ _ := tensorHomLeftEquiv
  homEquiv_naturality_left_symm {G' G A} f h := by
    apply tensorObj_hom_ext
    intro X x y
    calc
      _ = AddCommGrpCat.Hom.hom (X := F.obj.obj (op X)) (Y := A)
          (h.hom.app (op (op X)) (f.hom.app (op (op X)) x)) y := tensorDesc_tmul _ _ X x y
      _ = _ := by
        rw [AddCommGrpCat.comp_apply, flip_obj_map, tensor_map_app_tmul]
        symm
        exact tensorDesc_tmul _ _ X _ y
  homEquiv_naturality_right f g := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    exact AddCommGrpCat.ext fun x ↦ AddCommGrpCat.ext fun y ↦ rfl

/-- Tensoring with a right module is left adjoint to Hom from that module. The adjunction
is natural in the right module as well as in the left module and the target group. -/
noncomputable def tensorHomRightAdjunction : tensor (C := C) ⊣₂ tensorHomRight :=
  ParametrizedAdjunction.mk' (fun G ↦ Adjunction.mkOfHomEquiv (tensorRightCore G))
    (fun {_ _} f {_} {_} h ↦ by
      simp only [Adjunction.mkOfHomEquiv_homEquiv]
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      apply AddCommGrpCat.ext
      intro y
      apply AddCommGrpCat.ext
      intro x
      exact congrArg h (tensor_map_app_tmul f _ X.unop x y))

/-- Tensoring with a left module is left adjoint to Hom from that module. The adjunction
is natural in the left module as well as in the right module and the target group. -/
noncomputable def tensorHomLeftAdjunction : (tensor (C := C)).flip ⊣₂ tensorHomLeft :=
  ParametrizedAdjunction.mk' (fun F ↦ Adjunction.mkOfHomEquiv (tensorLeftCore F))
    (fun {_ _} f {_} {_} h ↦ by
      simp only [Adjunction.mkOfHomEquiv_homEquiv]
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      apply AddCommGrpCat.ext
      intro x
      apply AddCommGrpCat.ext
      intro y
      exact congrArg h (tensor_obj_map_tmul _ f X.unop.unop x y))

/-- Currying in the left module turns evaluation on a pure tensor into iterated evaluation. -/
@[simp]
lemma tensorHomRightAdjunction_homEquiv_apply (h : tensorObj G F ⟶ A) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    AddCommGrpCat.Hom.hom (X := G.obj.obj (op (op X))) (Y := A)
      ((tensorHomRightAdjunction.homEquiv h).hom.app (op X) y) x = h (tmul X x y) := by
  simp only [ParametrizedAdjunction.homEquiv_eq, tensorHomRightAdjunction,
    ParametrizedAdjunction.mk'_adj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Uncurrying in the left module evaluates the resulting map on a pure tensor. -/
@[simp]
lemma tensorHomRightAdjunction_homEquiv_symm_tmul
    (h : F ⟶ (tensorHomRight.obj (op G)).obj A) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tensorHomRightAdjunction.homEquiv.symm h (tmul X x y) =
      AddCommGrpCat.Hom.hom (X := G.obj.obj (op (op X))) (Y := A) (h.hom.app (op X) y) x := by
  simp only [ParametrizedAdjunction.homEquiv_eq, tensorHomRightAdjunction,
    ParametrizedAdjunction.mk'_adj, Adjunction.mkOfHomEquiv_homEquiv]
  exact tensorDesc_tmul _ _ X x y

/-- Currying in the right module turns evaluation on a pure tensor into iterated evaluation. -/
@[simp↓]
lemma tensorHomLeftAdjunction_homEquiv_apply (h : tensorObj G F ⟶ A) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    AddCommGrpCat.Hom.hom (X := F.obj.obj (op X)) (Y := A)
      ((tensorHomLeftAdjunction.homEquiv h).hom.app (op (op X)) x) y = h (tmul X x y) := by
  simp only [ParametrizedAdjunction.homEquiv_eq, tensorHomLeftAdjunction,
    ParametrizedAdjunction.mk'_adj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Uncurrying in the right module evaluates the resulting map on a pure tensor. -/
@[simp↓]
lemma tensorHomLeftAdjunction_homEquiv_symm_tmul
    (h : G ⟶ (tensorHomLeft.obj (op F)).obj A) (X : C)
    (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    tensorHomLeftAdjunction.homEquiv.symm h (tmul X x y) =
      AddCommGrpCat.Hom.hom (X := F.obj.obj (op X)) (Y := A) (h.hom.app (op (op X)) x) y := by
  simp only [ParametrizedAdjunction.homEquiv_eq, tensorHomLeftAdjunction,
    ParametrizedAdjunction.mk'_adj, Adjunction.mkOfHomEquiv_homEquiv]
  exact tensorDesc_tmul _ _ X x y

/-- Tensoring with a fixed right module is a left adjoint. -/
instance (G : ModCat.{w} Cᵒᵖ) : (tensor.obj G).IsLeftAdjoint :=
  (tensorHomRightAdjunction.adj G).isLeftAdjoint

/-- Tensoring with a fixed left module is a left adjoint. -/
instance (F : ModCat.{w} C) : (tensor.flip.obj F).IsLeftAdjoint :=
  (tensorHomLeftAdjunction.adj F).isLeftAdjoint

end Adjunction

end TauCeti.ModCat
