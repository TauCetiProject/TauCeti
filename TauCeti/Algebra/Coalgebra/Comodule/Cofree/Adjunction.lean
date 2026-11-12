/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The cofree comodule adjunction

Tensoring a module with a coalgebra defines a functor right adjoint to the forgetful
functor from comodules. Its unit is the coaction, and its counit applies the coalgebra
counit to the tensor factor. This packages `Comodule.Hom.cofreeEquiv` as a categorical
adjunction, so that preservation of limits and injectivity can be used categorically.

The construction uses the cofree universal property from Sweedler, *Hopf Algebras*,
Chapter 2, and Mathlib's `Adjunction.mkOfHomEquiv`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.ComoduleCat

universe u v w

variable (R : Type u) (C : Type v) [CommRing R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

attribute [local instance] Comodule.cofree

/-- The cofree functor sends `M` to `M ⊗ C` and a linear map `f` to `f ⊗ id`. -/
-- Expose the functor so its tensor-product carrier can occur in downstream signatures.
@[expose] noncomputable def cofreeFunctor :
    ModuleCat.{max v w} R ⥤ ComoduleCat.{u, v, max v w} R C where
  obj M := cofree R C M
  map f := Comodule.Hom.cofreeMap f.hom
  map_id M := by
    exact Comodule.Hom.cofreeMap_id
  map_comp f g := by
    exact Comodule.Hom.cofreeMap_comp g.hom f.hom

/-- The objects of the cofree functor are the existing bundled cofree comodules. -/
@[simp]
theorem cofreeFunctor_obj (M : ModuleCat.{max v w} R) :
    (cofreeFunctor R C).obj M = cofree R C M :=
  (rfl)

/-- On underlying linear maps, the cofree functor tensors with the identity. -/
@[simp]
theorem cofreeFunctor_map_toLinearMap {M N : ModuleCat.{max v w} R} (f : M ⟶ N) :
    ((cofreeFunctor R C).map f).toLinearMap = f.hom.rTensor C :=
  (rfl)

/-- Forgetting a comodule is left adjoint to forming the cofree comodule. -/
noncomputable def cofreeAdjunction :
    forget₂ (ComoduleCat.{u, v, max v w} R C) (ModuleCat.{max v w} R) ⊣
      cofreeFunctor R C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        { toFun := fun f ↦ Comodule.Hom.cofreeLift (R := R) (C := C) (P := M) f.hom
          invFun := fun g ↦ (ModuleCat.homLinearEquiv (S := R)).symm (Comodule.Hom.cofreeEquiv
            (R := R) (C := C) (M := N) (P := M) g)
          left_inv := fun f ↦ ModuleCat.hom_ext <|
            (Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := N) (P := M)).apply_symm_apply
              f.hom
          right_inv := fun g ↦
            (Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := N) (P := M)).symm_apply_apply g }
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        let g' : Comodule.Hom R C M' (N ⊗[R] C) := g
        apply ModuleCat.hom_ext
        -- Identify the forgotten module with the original comodule's underlying module.
        change Comodule.Hom.cofreeEquiv (Comodule.Hom.comp g' f) =
          Comodule.Hom.cofreeEquiv g' ∘ₗ f.toLinearMap
        simp only [Comodule.Hom.cofreeEquiv_apply, Comodule.Hom.comp_toLinearMap,
          LinearMap.comp_assoc]
      homEquiv_naturality_right := by
        intro M N N' f g
        let f' : M →ₗ[R] N := f.hom
        -- Unpack the categorical maps to use the existing cofree-lift naturality law.
        change Comodule.Hom.cofreeLift (R := R) (C := C) (P := M) (g.hom ∘ₗ f') =
          Comodule.Hom.comp (Comodule.Hom.cofreeMap g.hom)
            (Comodule.Hom.cofreeLift (R := R) (C := C) (P := M) f')
        exact (Comodule.Hom.cofreeMap_comp_cofreeLift g.hom f').symm }

/-- The adjunction sends a linear map to its cofree lift. -/
@[simp]
theorem cofreeAdjunction_homEquiv_apply (M : ComoduleCat.{u, v, max v w} R C)
    (N : ModuleCat.{max v w} R)
    (f : M →ₗ[R] N) :
    (cofreeAdjunction R C).homEquiv M N ((ModuleCat.homLinearEquiv (S := R)).symm f) =
      Comodule.Hom.cofreeLift (R := R) (C := C) (P := M) f := by
  rw [cofreeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The inverse adjunction map extracts the counit component of a comodule morphism. -/
@[simp]
theorem cofreeAdjunction_homEquiv_symm_apply_hom
    (M : ComoduleCat.{u, v, max v w} R C) (N : ModuleCat.{max v w} R)
    (g : M ⟶ (cofreeFunctor R C).obj N) :
    (((cofreeAdjunction R C).homEquiv M N).symm g).hom =
      Comodule.Hom.cofreeEquiv (R := R) (C := C) (M := N) (P := M) g :=
  (rfl)

/-- The unit of the cofree adjunction is the original coaction. -/
@[simp]
theorem cofreeAdjunction_unit_app_toLinearMap (M : ComoduleCat.{u, v, max v w} R C) :
    ((cofreeAdjunction R C).unit.app M).toLinearMap =
      Comodule.coact (R := R) (C := C) (M := M) := by
  -- The unit is the cofree lift of the identity of the forgotten module.
  change (Comodule.Hom.cofreeLift (R := R) (C := C) (P := M) LinearMap.id).toLinearMap = _
  simp

/-- The counit of the cofree adjunction evaluates the coalgebra factor by its counit. -/
@[simp]
theorem cofreeAdjunction_counit_app_hom (M : ModuleCat.{max v w} R) :
    ((cofreeAdjunction R C).counit.app M).hom =
      (TensorProduct.rid R M).toLinearMap ∘ₗ Coalgebra.counit.lTensor M := by
  -- The counit is the counit component of the identity of the cofree comodule.
  change Comodule.Hom.cofreeEquiv (Comodule.Hom.id R C (M ⊗[R] C)) = _
  simp [Comodule.Hom.cofreeEquiv_apply]

end TauCeti.ComoduleCat
