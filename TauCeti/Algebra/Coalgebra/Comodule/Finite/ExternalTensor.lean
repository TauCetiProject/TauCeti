/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.ExternalTensor
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# External tensor products of finite comodules

The external tensor product is a bifunctor from finite `B`-comodules and finite `C`-comodules
to finite `B ⊗[R] C`-comodules. Composing it with corestriction along a coalgebra map
`f : B ⊗[R] C →ₗc[R] D` gives `D`-coactions on the tensor products of the underlying modules,
natural in both comodule maps. The coaction is characterized by
`TauCeti.Comodule.externalTensor_coact`, `of_coact`, and the `corestrict_obj_coact` formula from
`TauCeti.Algebra.Coalgebra.Comodule.Finite.Corestrict.Basic`; the underlying maps are ordinary
tensor products.

This construction needs neither multiplication on the coalgebras nor a field assumption.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v w x

variable (R : Type u) [CommSemiring R]
variable (B : Type v) (C : Type w)
variable [AddCommMonoid B] [Module R B] [Coalgebra R B]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

attribute [local instance] Comodule.externalTensor

/-- The external tensor product of finite comodules over two coefficient coalgebras. -/
noncomputable abbrev externalTensor
    (M : FGComoduleCat.{u, v, x} R B) (N : FGComoduleCat.{u, w, x} R C) :
    FGComoduleCat.{u, max v w, x} R (B ⊗[R] C) :=
  of (R := R) (C := B ⊗[R] C) (M ⊗[R] N)

variable {R B C}

/-- The carrier of the external tensor product is the ordinary tensor-product module. -/
@[simp]
theorem externalTensor_coe
    (M : FGComoduleCat.{u, v, x} R B) (N : FGComoduleCat.{u, w, x} R C) :
    (externalTensor R B C M N : Type x) = M ⊗[R] N :=
  (rfl)

variable {M M' M'' : FGComoduleCat.{u, v, x} R B}
variable {N N' N'' : FGComoduleCat.{u, w, x} R C}

/-- The external tensor product of two finite-comodule morphisms. -/
noncomputable abbrev externalTensorMap (f : M ⟶ M') (g : N ⟶ N') :
    externalTensor R B C M N ⟶ externalTensor R B C M' N' :=
  ofHom (Comodule.Hom.externalTensorMap f.hom g.hom)

/-- The external tensor product of morphisms acts componentwise on simple tensors. -/
@[simp]
theorem externalTensorMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    externalTensorMap f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n := by
  rw [ofHom_apply]
  rw [Comodule.Hom.externalTensorMap_apply, TensorProduct.map_tmul]
  rfl

/-- The external tensor product preserves identities. -/
@[simp]
theorem externalTensorMap_id (M : FGComoduleCat.{u, v, x} R B)
    (N : FGComoduleCat.{u, w, x} R C) :
    externalTensorMap (𝟙 M) (𝟙 N) = 𝟙 (externalTensor R B C M N) := by
  apply ObjectProperty.hom_ext
  apply Comodule.Hom.toLinearMap_injective
  simp

/-- The external tensor product preserves composition in both variables. -/
@[simp]
theorem externalTensorMap_comp (f : M ⟶ M') (f' : M' ⟶ M'')
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    externalTensorMap (f ≫ f') (g ≫ g') = externalTensorMap f g ≫ externalTensorMap f' g' := by
  apply ObjectProperty.hom_ext
  apply Comodule.Hom.toLinearMap_injective
  simp [TensorProduct.map_comp]

variable (R B C)

/-- External tensor product as a bifunctor on finite comodules.

For a coalgebra map `f : B ⊗[R] C →ₗc[R] D`, composing with `corestrict f` gives natural
`D`-coactions on every tensor product of a finite `B`-comodule and a finite `C`-comodule. -/
@[expose]
noncomputable def externalTensorBifunctor :
    FGComoduleCat.{u, v, x} R B × FGComoduleCat.{u, w, x} R C ⥤
      FGComoduleCat.{u, max v w, x} R (B ⊗[R] C) where
  obj P := externalTensor R B C P.1 P.2
  map fg := externalTensorMap fg.1 fg.2
  map_id P := externalTensorMap_id P.1 P.2
  map_comp f g := externalTensorMap_comp f.1 g.1 f.2 g.2

/-- The object part of the external tensor bifunctor. -/
@[simp]
theorem externalTensorBifunctor_obj
    (P : FGComoduleCat.{u, v, x} R B × FGComoduleCat.{u, w, x} R C) :
    (externalTensorBifunctor R B C).obj P = externalTensor R B C P.1 P.2 :=
  (rfl)

/-- The map part of the external tensor bifunctor. -/
@[simp]
theorem externalTensorBifunctor_map
    {P Q : FGComoduleCat.{u, v, x} R B × FGComoduleCat.{u, w, x} R C} (fg : P ⟶ Q) :
    (externalTensorBifunctor R B C).map fg = externalTensorMap fg.1 fg.2 :=
  (rfl)

end TauCeti.FGComoduleCat
