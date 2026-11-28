/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Linear
public import TauCeti.CategoryTheory.Preadditive.ModCat.Tensor.Basic

/-!
# Scalar-linear tensor products of modules over a linear category

For an `R`-linear category `C`, a scalar acts on `G ⊗_C F` by applying the tensor functor to
the corresponding scalar endomorphism of `F`. Balancing at the scalar identity of each
object shows that the endomorphism of `G` gives the same action. The resulting tensor functor
takes values in `ModuleCat R` and is `R)-linear in both module variables when `R` is commutative.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), §6, pp. 26–27 (balanced
  tensor product), and §11, pp. 50–51 (the scalar action from the center on additive functors).
-/

public section

open CategoryTheory Opposite
open CategoryTheory.AdditiveFunctor (smulEnd)

universe u v w

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C] [EssentiallySmall.{w} C]
variable (R : Type*) [Ring R] [Linear R C]

attribute [local instance] AdditiveFunctor.sourceLinear

/-- The two scalar endomorphisms induce the same endomorphism of the coend tensor product. -/
theorem tensor_map_app_smulEnd (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (r : R) :
    (tensor.map (smulEnd R r G)).app F = (tensor.obj G).map (smulEnd R r F) := by
  apply tensorObj_hom_ext
  intro X x y
  simpa only [tensor_map_app_tmul, tensor_obj_map_tmul, AdditiveFunctor.smulEnd_hom_app,
    Linear.op_smul, op_id] using tmul_balance (G := G) (F := F) (r • 𝟙 X) x y

/-- The tensor product over an `R`-linear category, with values in `R`-modules. The lift keeps
the underlying abelian groups and maps of `tensor`. -/
@[expose]
noncomputable def linearTensor : ModCat.{w} Cᵒᵖ ⥤ ModCat.{w} C ⥤ ModuleCat.{w} R :=
  (additiveFunctor (ModCat.{w} C) AddCommGrpCat.{w}).lift tensor
      (fun G ↦ (additiveFunctor_iff (tensor.obj G)).2 inferInstance) ⋙
    AdditiveFunctor.liftToModuleCatFunctor (ModCat.{w} C) R

/-- Scalars act on the tensor product through the scalar endomorphism of the second factor. -/
theorem linearTensor_smul (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (r : R)
    (z : ((linearTensor R).obj G).obj F) :
    r • z = (tensor.obj G).map (smulEnd R r F) z := by
  have h : r • 𝟙 F = smulEnd R r F := by
    simp [AdditiveFunctor.sourceLinear_smul_eq_comp_smulEnd]
  exact (AdditiveFunctor.liftToModuleCat_smul R (.of (tensor.obj G)) F r z).trans
    (ConcreteCategory.congr_hom (congrArg (tensor.obj G).map h) z)

/-- On pure tensors, the scalar acts on the second entry. -/
@[simp]
theorem linearTensor_smul_tmul (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (r : R)
    (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    HSMul.hSMul (β := ↑(((linearTensor R).obj G).obj F)) r (tmul X x y) =
      tmul X x (F.obj.map (r • 𝟙 (op X)) y) := by
  simpa only [tensor_obj_map_tmul, AdditiveFunctor.smulEnd_hom_app] using
    linearTensor_smul R G F r (tmul X x y)

/-- On pure tensors, the scalar can equally act on the first entry. -/
theorem linearTensor_smul_tmul_left (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C) (r : R)
    (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    HSMul.hSMul (β := ↑(((linearTensor R).obj G).obj F)) r (tmul X x y) =
      tmul X (G.obj.map (r • 𝟙 (op (op X))) x) y := by
  simpa only [← tensor_map_app_smulEnd, tensor_map_app_tmul,
    AdditiveFunctor.smulEnd_hom_app] using linearTensor_smul R G F r (tmul X x y)

instance (G : ModCat.{w} Cᵒᵖ) : ((linearTensor R).obj G).Additive :=
  inferInstanceAs ((AdditiveFunctor.of (tensor.obj G)).liftToModuleCat R).Additive

instance (F : ModCat.{w} C) : ((linearTensor R).flip.obj F).Additive where
  map_add := by
    intro G G' α β
    exact (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map_injective
      ((tensor.flip.obj F).map_add (f := α) (g := β))

instance : (linearTensor R (C := C)).Additive where
  map_add := by
    intro G G' α β
    apply NatTrans.ext
    funext F
    exact ((linearTensor R).flip.obj F).map_add

/-- Forgetting the scalars in both variables recovers the abelian-group-valued tensor
bifunctor. -/
noncomputable def linearTensorForgetIso :
    linearTensor R (C := C) ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ≅
        tensor :=
  NatIso.ofComponents
    (fun G ↦ (AdditiveFunctor.of (tensor.obj G)).liftToModuleCatForgetIso R) (by
      intro G G' α
      ext F z
      -- The whiskered maps evaluate to the underlying additive tensor maps.
      exact (AdditiveFunctor.liftToModuleCatForgetIso_hom_app_apply R (.of (tensor.obj G')) F
        ((tensor.map α).app F z)).trans
        (congrArg ((tensor.map α).app F)
          (AdditiveFunctor.liftToModuleCatForgetIso_hom_app_apply R (.of (tensor.obj G)) F z)).symm)

/-- The forgetful comparison acts as the identity on each tensor product. -/
@[simp↓]
theorem linearTensorForgetIso_hom_app_app_apply (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C)
    (z : tensorObj G F) :
    ((linearTensorForgetIso R).hom.app G).app F z = z :=
  AdditiveFunctor.liftToModuleCatForgetIso_hom_app_apply R (.of (tensor.obj G)) F z

/-- The inverse forgetful comparison acts as the identity on each tensor product. -/
@[simp↓]
theorem linearTensorForgetIso_inv_app_app_apply (G : ModCat.{w} Cᵒᵖ) (F : ModCat.{w} C)
    (z : tensorObj G F) :
    ((linearTensorForgetIso R).inv.app G).app F z = z :=
  AdditiveFunctor.liftToModuleCatForgetIso_inv_app_apply R (.of (tensor.obj G)) F z

variable {G : ModCat.{w} Cᵒᵖ} {F : ModCat.{w} C} in
/-- Linear maps out of the tensor product are determined by their values on pure tensors. -/
@[ext]
theorem linearTensor_hom_ext {M : ModuleCat.{w} R} {p q : ((linearTensor R).obj G).obj F ⟶ M}
    (h : ∀ (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)),
      p (tmul X x y) = q (tmul X x y)) : p = q :=
  (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).map_injective (tensorObj_hom_ext h)

section CommRing

variable (S : Type*) [CommRing S] [Linear S C]

/-- The tensor functor in the second variable is linear for the scalar action induced by
`C` on its modules. -/
instance (G : ModCat.{w} Cᵒᵖ) : ((linearTensor S).obj G).Linear S :=
  (inferInstance : ((AdditiveFunctor.of (tensor.obj G)).liftToModuleCat S).Linear S)

/-- The tensor functor in the first variable is linear for the scalar action induced by
`C` on its right modules. -/
instance (F : ModCat.{w} C) : ((linearTensor S).flip.obj F).Linear S :=
  (Functor.linear_iff S _).2 fun G r ↦ by
    apply ModuleCat.hom_ext
    ext z
    have h : r • 𝟙 G = smulEnd S r G := by
      simp [AdditiveFunctor.sourceLinear_smul_eq_comp_smulEnd]
    change (tensor.map (r • 𝟙 G)).app F z = r • z
    rw [h, tensor_map_app_smulEnd]
    exact (linearTensor_smul S G F r z).symm

/-- The curried tensor bifunctor is linear for the scalar action induced by `C` on its
right modules. -/
instance : (linearTensor S (C := C)).Linear S where
  map_smul α r := by
    apply NatTrans.ext
    funext F
    exact ((linearTensor S).flip.obj F).map_smul r α

variable {G : ModCat.{w} Cᵒᵖ} {F : ModCat.{w} C} {M : ModuleCat.{w} S}

/-- The pure-tensor pairing on each pair of module values is bilinear over the scalar ring. -/
noncomputable def linearTmulLinear (X : C) :
    G.moduleObj S (op (op X)) →ₗ[S] F.moduleObj S (op X) →ₗ[S] ((linearTensor S).obj G).obj F :=
  LinearMap.mk₂ S (tmul (G := G) (F := F) X)
    (fun x x' y ↦ add_tmul X x x' y)
    (fun r x y ↦
      (congrArg (fun x' ↦ tmul (G := G) (F := F) X x' y)
        (G.moduleObj_smul S (op (op X)) r x)).trans
        (linearTensor_smul_tmul_left S G F r X x y).symm)
    (fun x y y' ↦ tmul_add X x y y')
    (fun r x y ↦
      (congrArg (tmul (G := G) (F := F) X x) (F.moduleObj_smul S (op X) r y)).trans
        (linearTensor_smul_tmul S G F r X x y).symm)

/-- The bilinear pairing sends a pair of elements to their pure tensor. -/
@[simp]
theorem linearTmulLinear_apply (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    linearTmulLinear S X x y = tmul X x y := (rfl)

private def restrictPairing
    (b : ∀ X : C, G.moduleObj S (op (op X)) →ₗ[S] F.moduleObj S (op X) →ₗ[S] M)
    (X : C) : G.obj.obj (op (op X)) →ₗ[ℤ] F.obj.obj (op X) →ₗ[ℤ] M :=
  (LinearMap.restrictScalarsₗ ℤ S (F.moduleObj S (op X)) M ℤ).comp ((b X).restrictScalars ℤ)

/-- A balanced family of bilinear maps on the module values induces a linear map from the
tensor product. -/
noncomputable def linearTensorDesc
    (b : ∀ X : C, G.moduleObj S (op (op X)) →ₗ[S] F.moduleObj S (op X) →ₗ[S] M)
    (hb : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op Y)),
      b Y (G.obj.map f.op.op x) y = b X x (F.obj.map f.op y)) :
    ((linearTensor S).obj G).obj F ⟶ M :=
  let f := tensorDesc (A := (forget₂ (ModuleCat.{w} S) AddCommGrpCat.{w}).obj M)
    (restrictPairing S b) (fun _ _ g x y ↦ hb g x y)
  ModuleCat.ofHom (X := ↑(((linearTensor S).obj G).obj F)) (Y := ↑M)
    { f.hom with
      map_smul' := fun r z ↦ by
        let targetSmul := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom M r)
        have he := tensorDesc_tmul (A := (forget₂ (ModuleCat.{w} S) AddCommGrpCat.{w}).obj M)
          (restrictPairing S b) (fun _ _ g x y ↦ hb g x y)
        have h : (tensor.obj G).map (smulEnd S r F) ≫ f = f ≫ targetSmul := by
          apply tensorObj_hom_ext
          intro X x y
          simp only [ConcreteCategory.comp_apply, tensor_obj_map_tmul,
            AdditiveFunctor.smulEnd_hom_app]
          calc
            _ = b X x (F.obj.map (r • 𝟙 (op X)) y) := he X x _
            _ = r • b X x y := (congrArg (b X x) (F.moduleObj_smul S (op X) r y).symm).trans
              ((b X x).map_smul r y)
            _ = _ := congrArg (r • ·) (he X x y).symm
        exact (congrArg f.hom (linearTensor_smul S G F r z)).trans
          (ConcreteCategory.congr_hom h z) }

/-- The linear map induced by a balanced family evaluates on each pure tensor as that family. -/
@[simp]
theorem linearTensorDesc_tmul
    (b : ∀ X : C, G.moduleObj S (op (op X)) →ₗ[S] F.moduleObj S (op X) →ₗ[S] M)
    (hb : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op Y)),
      b Y (G.obj.map f.op.op x) y = b X x (F.obj.map f.op y))
    (X : C) (x : G.obj.obj (op (op X))) (y : F.obj.obj (op X)) :
    linearTensorDesc S b hb (tmul X x y) = b X x y :=
  tensorDesc_tmul (A := (forget₂ (ModuleCat.{w} S) AddCommGrpCat.{w}).obj M)
    (restrictPairing S b) (fun _ _ g x y ↦ hb g x y) X x y

end CommRing

end TauCeti.ModCat
