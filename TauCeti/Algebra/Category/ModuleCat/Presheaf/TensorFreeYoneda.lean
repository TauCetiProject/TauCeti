/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Free
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.FreeYoneda
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Morphisms out of the tensor product with a free presheaf on a representable

Let `R` be a presheaf of commutative rings on a category `C`, let `M` and `N` be presheaves of
`R`-modules, and let `U` be an object of `C`. This file establishes the restriction--extension
correspondence: morphisms `M ⊗ freeYoneda R U ⟶ N` out of the tensor product with the free
presheaf of modules `TauCeti.PresheafOfModules.freeYoneda R U` on the presheaf represented by `U`
are the same as morphisms of restrictions `M|_U ⟶ N|_U` on the slice over `U`, where restriction
to the slice is `PresheafOfModulesOfCommRing.pushforward₀ (Over.forget U) R`.

A morphism `ψ` out of the tensor product restricts to the map sending a section `m` over
`g : V ⟶ U` to `ψ (m ⊗ g)`; conversely a morphism of restrictions `φ` extends to the map sending
a pure tensor `m ⊗ g` to the value of the component of `φ` at `g` on `m`. The correspondence is
natural in both arguments. Combined with the tensor--Hom adjunction it computes the sections of
the internal Hom of presheaves of modules, in
`TauCeti.Algebra.Category.ModuleCat.Presheaf.InternalHom`.

## Main declarations

* `TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda` and
  `TauCeti.PresheafOfModules.tensorFreeYonedaOfRestrict`: the two directions of the
  correspondence, characterized by
  `TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda_app_apply` and
  `TauCeti.PresheafOfModules.tensorFreeYonedaOfRestrict_app_tmul_freeMk`;
* `TauCeti.PresheafOfModules.tensorFreeYonedaHomEquiv`: the correspondence
  `(M ⊗ freeYoneda R U ⟶ N) ≃ (M|_U ⟶ N|_U)`, natural in the target by
  `TauCeti.PresheafOfModules.tensorFreeYonedaHomEquiv_comp` and in the source by
  `TauCeti.PresheafOfModules.tensorFreeYonedaHomEquiv_whiskerRight_comp`.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe v u

noncomputable section

namespace TauCeti

namespace PresheafOfModules

open _root_.PresheafOfModules PresheafOfModulesOfCommRing

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{v}}
variable (U : C) (M N : PresheafOfModulesOfCommRing.{v} R)

/-- The morphism of restrictions to the slice over `U` induced by a morphism out of the tensor
product with the free presheaf represented by `U`: over `g : V ⟶ U`, it tensors a section with
the basis element indexed by `g`. -/
def restrictOfTensorFreeYoneda (ψ : M ⊗ freeYoneda R U ⟶ N) :
    (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N :=
  homMk (fun X ↦ ModuleCat.ofHom ((ψ.app' (op X.unop.left)).hom ∘ₗ
      (TensorProduct.mk (R.obj (op X.unop.left)) (M.obj (op X.unop.left))
        ((freeYoneda R U).obj (op X.unop.left))).flip (ModuleCat.freeMk X.unop.hom)))
    (fun {X Y} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op X.unop.left)) ↦ ?_)
      have h := PresheafOfModulesOfCommRing.naturality_apply ψ f.unop.left.op
        (m ⊗ₜ (ModuleCat.freeMk X.unop.hom : (freeYoneda R U).obj (op X.unop.left)))
      have h' : (M.map f.unop.left.op m : M.obj (op Y.unop.left)) ⊗ₜ[R.obj (op Y.unop.left)]
          ((freeYoneda R U).map f.unop.left.op (ModuleCat.freeMk X.unop.hom) :
            (freeYoneda R U).obj (op Y.unop.left)) =
          (M.map f.unop.left.op m : M.obj (op Y.unop.left)) ⊗ₜ[R.obj (op Y.unop.left)]
            (ModuleCat.freeMk Y.unop.hom : (freeYoneda R U).obj (op Y.unop.left)) := by
        rw [freeObj_yoneda_map_freeMk, Quiver.Hom.unop_op, Over.w]
        rfl
      exact (congrArg (ConcreteCategory.hom (ψ.app' (op Y.unop.left))) h').symm.trans h)

/-- The component at `X : Over U` of the morphism of restrictions induced by `ψ` sends a section
`m` over `X.left` to `ψ (m ⊗ X.hom)`.

The section is taken in the domain of the component, the restriction of `M` to the slice
evaluated at `X`, so that the lemma rewrites goals about components of morphisms of restrictions;
a section of `M` over `X.left` may be passed as well, since the two modules are definitionally
equal.

This is not a simp lemma: the component is a morphism of modules over the ring of the slice
presheaf `(Over.forget U).op ⋙ R` at `X`, and simp rewrites that ring to `R.obj (op X.left)`
inside the implicit arguments of the coercion, so the left-hand side has no simp normal form. -/
theorem restrictOfTensorFreeYoneda_app_apply (ψ : M ⊗ freeYoneda R U ⟶ N) (X : Over U)
    (m : ((pushforward₀ (Over.forget U) R).obj M).obj (op X)) :
    (restrictOfTensorFreeYoneda U M N ψ).app' (op X) m =
      ψ.app' (op X.left) (m ⊗ₜ ModuleCat.freeMk X.hom) := by
  -- Expose the component as a composite of linear maps; both sides then agree definitionally,
  -- but the unifier does not find this reduction on its own.
  change (ψ.app' (op X.left)).hom ((TensorProduct.mk (R.obj (op X.left)) (M.obj (op X.left))
    ((freeYoneda R U).obj (op X.left))).flip (ModuleCat.freeMk X.hom) m) = _
  rfl

/-- The component at `g : V ⟶ U` of a morphism of restrictions to the slice over `U`, as a
linear map over the ring of sections over `V`. -/
private def componentLinearMap
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N)
    {V : C} (g : V ⟶ U) : M.obj (op V) →ₗ[R.obj (op V)] N.obj (op V) where
  toFun m := φ.app' (op (Over.mk g)) m
  map_add' m m' := map_add (φ.app' (op (Over.mk g))).hom m m'
  map_smul' r m := map_smul (φ.app' (op (Over.mk g))).hom r m

/-- The morphism out of the tensor product with the free presheaf represented by `U` induced by
a morphism of restrictions to the slice over `U`: a pure tensor of a section over `V` with the
basis element indexed by `g : V ⟶ U` is sent to the value of the component at `g`. -/
def tensorFreeYonedaOfRestrict
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    M ⊗ freeYoneda R U ⟶ N :=
  homMk (fun V ↦ ModuleCat.ofHom (TensorProduct.lift
      (ModuleCat.freeDesc (M := ModuleCat.of (R.obj V) (M.obj V →ₗ[R.obj V] N.obj V))
        (↾fun g : V.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom.flip))
    (fun {V W} f ↦ by
      -- On the pure tensor `m ⊗ g`, both sides are the component of `φ` at `f.unop ≫ g` applied
      -- to the restriction of `m`, respectively the restriction of the component at `g` applied
      -- to `m`; `h` is the naturality of `φ` along `f.unop`, viewed as a morphism of the slice.
      refine ModuleCat.tensor_free_hom_ext fun m g ↦ ?_
      have h := PresheafOfModulesOfCommRing.naturality_apply φ (Over.homMk f.unop :
        Over.mk (f.unop ≫ g) ⟶ Over.mk g).op m
      have e₁ : (ModuleCat.freeDesc (M := ModuleCat.of (R.obj W) (M.obj W →ₗ[R.obj W] N.obj W))
          (↾fun g : W.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom
            ((freeYoneda R U).map f (ModuleCat.freeMk g) : (freeYoneda R U).obj W) =
          componentLinearMap U M N φ (f.unop ≫ g) :=
        (congrArg (fun x : (freeYoneda R U).obj W ↦ (ModuleCat.freeDesc
          (M := ModuleCat.of (R.obj W) (M.obj W →ₗ[R.obj W] N.obj W))
          (↾fun g : W.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom x)
          (freeObj_yoneda_map_freeMk f g)).trans (ModuleCat.freeDesc_apply _ _)
      have e₂ : (ModuleCat.freeDesc (M := ModuleCat.of (R.obj V) (M.obj V →ₗ[R.obj V] N.obj V))
          (↾fun g : V.unop ⟶ U ↦ componentLinearMap U M N φ g)).hom (ModuleCat.freeMk g) =
          componentLinearMap U M N φ g :=
        ModuleCat.freeDesc_apply _ _
      exact (congrArg (fun L ↦ L (M.map f m)) e₁).trans
        (h.trans (congrArg (N.map f) (congrArg (fun L ↦ L m) e₂).symm)))

/-- The morphism out of the tensor product induced by a morphism of restrictions `φ` sends the
pure tensor of a section `m` over `V` with the basis element indexed by `g : V ⟶ U` to the value
of the component of `φ` at `g` on `m`. -/
@[simp]
theorem tensorFreeYonedaOfRestrict_app_tmul_freeMk
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N)
    {V : C} (m : M.obj (op V)) (g : V ⟶ U) :
    (tensorFreeYonedaOfRestrict U M N φ).app' (op V) (m ⊗ₜ ModuleCat.freeMk g) =
      φ.app' (op (Over.mk g)) m :=
  congrArg (fun L : M.obj (op V) →ₗ[R.obj (op V)] N.obj (op V) ↦ L m)
    (ModuleCat.freeDesc_apply (M := ModuleCat.of (R.obj (op V))
      (M.obj (op V) →ₗ[R.obj (op V)] N.obj (op V)))
      (↾fun g : V ⟶ U ↦ componentLinearMap U M N φ g) g)

/-- Restricting to the slice over `U` and tensoring with the free presheaf represented by `U`
are inverse: morphisms `M ⊗ freeYoneda R U ⟶ N` correspond to morphisms of restrictions
`M|_U ⟶ N|_U`. -/
def tensorFreeYonedaHomEquiv :
    (M ⊗ freeYoneda R U ⟶ N) ≃
      ((pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) where
  toFun := restrictOfTensorFreeYoneda U M N
  invFun := tensorFreeYonedaOfRestrict U M N
  left_inv ψ := by
    refine hom_ext fun ⟨V⟩ ↦ ModuleCat.tensor_free_hom_ext fun m g ↦ ?_
    -- Both characteristic formulas apply at the slice object `Over.mk g`, whose underlying
    -- object is `V` and whose structure morphism is `g`.
    exact (tensorFreeYonedaOfRestrict_app_tmul_freeMk U M N _ m g).trans
      (restrictOfTensorFreeYoneda_app_apply U M N ψ (Over.mk g) m)
  right_inv φ := by
    refine hom_ext fun ⟨X⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    rw [restrictOfTensorFreeYoneda_app_apply]
    -- The characteristic formula of the extension applies at `X.hom`, and `Over.mk X.hom` is `X`.
    exact tensorFreeYonedaOfRestrict_app_tmul_freeMk U M N φ m X.hom

/-- The forward direction of the restriction--extension correspondence is
`TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda`. -/
@[simp]
theorem tensorFreeYonedaHomEquiv_apply (ψ : M ⊗ freeYoneda R U ⟶ N) :
    tensorFreeYonedaHomEquiv U M N ψ = restrictOfTensorFreeYoneda U M N ψ := by
  rfl

/-- The inverse direction of the restriction--extension correspondence is
`TauCeti.PresheafOfModules.tensorFreeYonedaOfRestrict`. -/
@[simp]
theorem tensorFreeYonedaHomEquiv_symm_apply
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    (tensorFreeYonedaHomEquiv U M N).symm φ = tensorFreeYonedaOfRestrict U M N φ := by
  rfl

/-- The restriction--extension correspondence is natural in the target. -/
theorem tensorFreeYonedaHomEquiv_comp {N' : PresheafOfModulesOfCommRing.{v} R}
    (ψ : M ⊗ freeYoneda R U ⟶ N) (α : N ⟶ N') :
    tensorFreeYonedaHomEquiv U M N' (ψ ≫ α) =
      tensorFreeYonedaHomEquiv U M N ψ ≫ (pushforward₀ (Over.forget U) R).map α := by
  refine hom_ext fun ⟨X⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  -- The right-hand side is `α (ψ (m ⊗ X.hom))`: the pushforward of `α` has the components of
  -- `α`, and the restriction of `ψ` is given by the characteristic formula.
  rw [tensorFreeYonedaHomEquiv_apply, tensorFreeYonedaHomEquiv_apply, comp_app,
    ModuleCat.comp_apply, pushforward₀_map_app_apply, restrictOfTensorFreeYoneda_app_apply,
    restrictOfTensorFreeYoneda_app_apply]
  -- The left-hand side is `(ψ ≫ α) (m ⊗ X.hom) = α (ψ (m ⊗ X.hom))` as well.
  exact (congrArg (fun φ ↦ φ (m ⊗ₜ ModuleCat.freeMk X.hom)) (comp_app ψ α (op X.left))).trans
    (ModuleCat.comp_apply _ _ _)

/-- The restriction--extension correspondence is natural in the source. -/
theorem tensorFreeYonedaHomEquiv_whiskerRight_comp {M' : PresheafOfModulesOfCommRing.{v} R}
    (β : M' ⟶ M) (ψ : M ⊗ freeYoneda R U ⟶ N) :
    tensorFreeYonedaHomEquiv U M' N (β ▷ freeYoneda R U ≫ ψ) =
      (pushforward₀ (Over.forget U) R).map β ≫ tensorFreeYonedaHomEquiv U M N ψ := by
  refine hom_ext fun ⟨X⟩ ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  -- The right-hand side is `ψ (β m ⊗ X.hom)`: the restriction of `ψ` is given by the
  -- characteristic formula, and the pushforward of `β` has the components of `β`.
  rw [tensorFreeYonedaHomEquiv_apply, tensorFreeYonedaHomEquiv_apply, comp_app,
    ModuleCat.comp_apply, restrictOfTensorFreeYoneda_app_apply,
    restrictOfTensorFreeYoneda_app_apply, pushforward₀_map_app_apply]
  -- The left-hand side is `(β ▷ _ ≫ ψ) (m ⊗ X.hom) = ψ ((β ▷ _) (m ⊗ X.hom)) = ψ (β m ⊗ X.hom)`.
  exact ((congrArg (fun φ ↦ φ (m ⊗ₜ ModuleCat.freeMk X.hom))
      (comp_app (β ▷ freeYoneda R U) ψ (op X.left))).trans (ModuleCat.comp_apply _ _ _)).trans
    (congrArg (ψ.app' (op X.left))
      ((congrArg (fun φ ↦ φ (m ⊗ₜ ModuleCat.freeMk X.hom))
        (PresheafOfModulesOfCommRing.whiskerRight_app β (freeYoneda R U) (op X.left))).trans
        (ModuleCat.MonoidalCategory.whiskerRight_apply (β.app' (op X.left))
          ((freeYoneda R U).obj (op X.left)) m (ModuleCat.freeMk X.hom))))

end PresheafOfModules

end TauCeti

end
