/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Tensor products of transports along object equalities

The tensor product of two morphisms `eqToHom h` and `eqToHom h'` is the transport along the induced
equality of tensor products. This complements Mathlib's `MonoidalCategory.whiskerLeft_eqToHom` and
`MonoidalCategory.eqToHom_whiskerRight`, which treat whiskering.

The inverse tensor comparison of an oplax monoidal functor `F`, followed by the image under `F` of
a morphism out of a tensor product, is unchanged when the factors and the target are transported
along object equalities.

## Main results

* `TauCeti.eqToHom_tensorHom_eqToHom`: `eqToHom h ⊗ₘ eqToHom h' = eqToHom _`.
* `CategoryTheory.Functor.eqToHom_conjugate_inv_δ_comp_map`: transporting
  `inv (δ F M N) ≫ F.map φ` along equalities `M = M'`, `N = N'` and `P = P'` gives
  `inv (δ F M' N') ≫ F.map ψ`, where `ψ` is the transport of `φ`.
-/

public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two transports along object equalities is the transport along the
induced equality of tensor products. -/
@[simp]
theorem eqToHom_tensorHom_eqToHom {X X' Y Y' : C} (h : X = X') (h' : Y = Y') :
    (eqToHom h ⊗ₘ eqToHom h') = eqToHom (congrArg₂ (· ⊗ ·) h h') := by
  subst h h'
  simp

end TauCeti

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The inverse tensor comparison of an oplax monoidal functor `F`, followed by the image under `F`
of a morphism `φ : M ⊗ N ⟶ P`, is unchanged when `M`, `N` and `P` are transported along object
equalities: transporting `φ` to `ψ : M' ⊗ N' ⟶ P'` transports `inv (δ F M N) ≫ F.map φ` to
`inv (δ F M' N') ≫ F.map ψ`. -/
theorem eqToHom_conjugate_inv_δ_comp_map {D : Type*} [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal] {M M' N N' P P' : C} (hM : M = M') (hN : N = N') (hP : P = P')
    [IsIso (δ F M N)] [IsIso (δ F M' N')] (φ : M ⊗ N ⟶ P) (ψ : M' ⊗ N' ⟶ P')
    (hψ : ψ = (eqToHom hM.symm ⊗ₘ eqToHom hN.symm) ≫ φ ≫ eqToHom hP) :
    (eqToHom (congrArg F.obj hM) ⊗ₘ eqToHom (congrArg F.obj hN)) ≫
        CategoryTheory.inv (δ F M' N') ≫ F.map ψ ≫ eqToHom (congrArg F.obj hP).symm =
      CategoryTheory.inv (δ F M N) ≫ F.map φ := by
  subst hM hN hP hψ
  simp

end CategoryTheory.Functor
