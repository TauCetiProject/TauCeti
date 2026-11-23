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
equality of tensor products, and whiskering by a morphism commutes with such transports of the
tensor factors. This complements Mathlib's `MonoidalCategory.whiskerLeft_eqToHom` and
`MonoidalCategory.eqToHom_whiskerRight`, which treat whiskering by a transport.

The inverse tensor comparison of an oplax monoidal functor `F`, followed by the image under `F` of
a morphism out of a tensor product, is unchanged when the factors and the target are transported
along object equalities. In particular, the inverse of an invertible tensor comparison `δ F a b`
followed by `F` applied to a transport of `a ⊗ b` is the transport of `F a ⊗ F b` followed by the
inverse tensor comparison at the transported factors.

## Main results

* `TauCeti.eqToHom_tensorHom_eqToHom`: `eqToHom h ⊗ₘ eqToHom h' = eqToHom _`.
* `TauCeti.eqToIso_tensorIso_eqToIso`: `eqToIso h ⊗ᵢ eqToIso h' = eqToIso _`.
* `TauCeti.whiskerRight_comp_tensorHom_eqToHom` and `TauCeti.whiskerLeft_comp_tensorHom_eqToHom`:
  whiskering by a morphism commutes with transports of the tensor factors.
* `CategoryTheory.Functor.eqToHom_conjugate_inv_δ_comp_map`: transporting
  `inv (δ F M N) ≫ F.map φ` along equalities `M = M'`, `N = N'` and `P = P'` gives
  `inv (δ F M' N') ≫ F.map ψ`, where `ψ` is the transport of `φ`;
* `CategoryTheory.Functor.inv_δ_comp_map_eqToHom`: transporting `inv (δ F a b)` along `a = a'`
  and `b = b'`;
* `CategoryTheory.Functor.map_comp_eq_of_eqToHom_conjugate_tensor`: reflecting a commuting square
  between `eqToHom`-conjugated binary morphisms along an oplax monoidal functor with invertible `δ`.
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

/-- The tensor product of two transport isomorphisms along object equalities is the transport
isomorphism along the induced equality of tensor products. -/
@[simp]
theorem eqToIso_tensorIso_eqToIso {X X' Y Y' : C} (h : X = X') (h' : Y = Y') :
    (eqToIso h ⊗ᵢ eqToIso h') = eqToIso (congrArg₂ (· ⊗ ·) h h') :=
  Iso.ext (eqToHom_tensorHom_eqToHom h h')

/-- Whiskering a morphism `g : A ⟶ B` on the right commutes with transports of the tensor factors
along equalities of objects. -/
theorem whiskerRight_comp_tensorHom_eqToHom {A A' B B' K K' : C} (hA : A = A') (hB : B = B')
    (hK : K = K') (g : A ⟶ B) :
    g ▷ K ≫ (eqToHom hB ⊗ₘ eqToHom hK) =
      (eqToHom hA ⊗ₘ eqToHom hK) ≫ (eqToHom hA.symm ≫ g ≫ eqToHom hB) ▷ K' := by
  subst hA hB hK
  simp

/-- Whiskering a morphism `g : A ⟶ B` on the left commutes with transports of the tensor factors
along equalities of objects. -/
theorem whiskerLeft_comp_tensorHom_eqToHom {L L' A A' B B' : C} (hL : L = L') (hA : A = A')
    (hB : B = B') (g : A ⟶ B) :
    L ◁ g ≫ (eqToHom hL ⊗ₘ eqToHom hB) =
      (eqToHom hL ⊗ₘ eqToHom hA) ≫ L' ◁ (eqToHom hA.symm ≫ g ≫ eqToHom hB) := by
  subst hL hA hB
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

/-- The inverse tensor comparison of an oplax monoidal functor commutes with transports along
identifications of the factors. -/
@[reassoc]
theorem inv_δ_comp_map_eqToHom {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.OplaxMonoidal] {a a' b b' : C} [IsIso (OplaxMonoidal.δ F a b)]
    [IsIso (OplaxMonoidal.δ F a' b')] (ha : a = a') (hb : b = b') (h : a ⊗ b = a' ⊗ b') :
    CategoryTheory.inv (OplaxMonoidal.δ F a b) ≫ F.map (eqToHom h) =
      eqToHom (by rw [ha, hb]) ≫ CategoryTheory.inv (OplaxMonoidal.δ F a' b') := by
  subst ha hb
  simp

/-- For an oplax monoidal functor `F` with invertible tensor comparison `δ`, a commuting square
between `eqToHom`-conjugated images of binary morphisms `mB : B₁ ⊗ B₂ ⟶ B₃` and
`mA : A₁ ⊗ A₂ ⟶ A₃` reflects to `F.map (mB ≫ f₃) = F.map ((f₁ ⊗ₘ f₂) ≫ mA)`. -/
theorem map_comp_eq_of_eqToHom_conjugate_tensor {D : Type*} [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal]
    {B₁ B₂ B₃ A₁ A₂ A₃ : C}
    [IsIso (OplaxMonoidal.δ F B₁ B₂)] [IsIso (OplaxMonoidal.δ F A₁ A₂)]
    {B₁' B₂' B₃' A₁' A₂' A₃' : D}
    {hB₁ : B₁' = F.obj B₁} {hB₂ : B₂' = F.obj B₂} {hB₃ : B₃' = F.obj B₃}
    {hA₁ : A₁' = F.obj A₁} {hA₂ : A₂' = F.obj A₂} {hA₃ : F.obj A₃ = A₃'}
    {mB : B₁ ⊗ B₂ ⟶ B₃} {mA : A₁ ⊗ A₂ ⟶ A₃}
    {f₁ : B₁ ⟶ A₁} {f₂ : B₂ ⟶ A₂} {f₃ : B₃ ⟶ A₃}
    {μB : B₁' ⊗ B₂' ⟶ B₃'} {μA : A₁' ⊗ A₂' ⟶ A₃'}
    {ψ₁ : B₁' ⟶ A₁'} {ψ₂ : B₂' ⟶ A₂'} {ψ₃ : B₃' ⟶ A₃'}
    (hμB : μB = (eqToHom hB₁ ⊗ₘ eqToHom hB₂) ≫
      CategoryTheory.inv (OplaxMonoidal.δ F B₁ B₂) ≫ F.map mB ≫ eqToHom hB₃.symm)
    (hμA : μA = (eqToHom hA₁ ⊗ₘ eqToHom hA₂) ≫
      CategoryTheory.inv (OplaxMonoidal.δ F A₁ A₂) ≫ F.map mA ≫ eqToHom hA₃)
    (hψ₁ : ψ₁ = eqToHom hB₁ ≫ F.map f₁ ≫ eqToHom hA₁.symm)
    (hψ₂ : ψ₂ = eqToHom hB₂ ≫ F.map f₂ ≫ eqToHom hA₂.symm)
    (hψ₃ : ψ₃ = eqToHom hB₃ ≫ F.map f₃ ≫ eqToHom hA₃)
    (hmul : μB ≫ ψ₃ = (ψ₁ ⊗ₘ ψ₂) ≫ μA) :
    F.map (mB ≫ f₃) = F.map ((f₁ ⊗ₘ f₂) ≫ mA) := by
  subst hB₁ hB₂ hB₃ hA₁ hA₂ hA₃
  rw [hμB, hμA, hψ₁, hψ₂, hψ₃] at hmul
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id,
    Category.assoc] at hmul
  rw [← Functor.map_comp] at hmul
  have hδ : (F.map f₁ ⊗ₘ F.map f₂) ≫ CategoryTheory.inv (OplaxMonoidal.δ F A₁ A₂) =
      CategoryTheory.inv (OplaxMonoidal.δ F B₁ B₂) ≫ F.map (f₁ ⊗ₘ f₂) := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← OplaxMonoidal.δ_natural, IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hδ, ← Functor.map_comp] at hmul
  exact (cancel_epi (CategoryTheory.inv (OplaxMonoidal.δ F B₁ B₂))).mp hmul

end CategoryTheory.Functor
