/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-!
# Group Object Laws for Representable Functors

This file defines the group object structure on a representable functor from a
Cartesian monoidal category to the category of commutative additive groups.

This advances the Tau Ceti Jacobian roadmap.
-/

public section

universe v w
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Opposite

namespace TauCeti.Jacobian

@[reducible]
noncomputable def representable_AddCommGrp_GrpObj {C_ : Type v} [Category C_]
    [CartesianMonoidalCategory C_] (F : C_ᵒᵖ ⥤ AddCommGrpCat.{w})
    (hF : (F ⋙ forget AddCommGrpCat).IsRepresentable) :
    GrpObj (Functor.reprX (F ⋙ forget AddCommGrpCat)) := by
  let X := Functor.reprX (F ⋙ forget AddCommGrpCat)
  let e A := ((F ⋙ forget AddCommGrpCat).reprW.app (op A)).toEquiv
  have he_nat : ∀ {A B : C_} (f : A ⟶ B) (g : B ⟶ X), e A (f ≫ g) = F.map f.op (e B g) := by
    intro A B f g
    change ((yoneda.obj X).map f.op ≫ (F ⋙ forget _).reprW.hom.app (op A)) g = _
    rw [(F ⋙ forget _).reprW.hom.naturality f.op]
    rfl
  let one : 𝟙_ C_ ⟶ X := (e (𝟙_ C_)).symm 0
  have he_one : e (𝟙_ C_) one = 0 := Equiv.apply_symm_apply _ 0
  let mul : X ⊗ X ⟶ X := (e (X ⊗ X)).symm (
    e (X ⊗ X) (fst X X) +
    e (X ⊗ X) (snd X X))
  have he_mul : e (X ⊗ X) mul = e (X ⊗ X) (fst X X) + e (X ⊗ X) (snd X X) :=
    Equiv.apply_symm_apply _ _
  let inv : X ⟶ X := (e X).symm (- e X (𝟙 X))
  have he_inv : e X inv = - e X (𝟙 X) := Equiv.apply_symm_apply _ _
  have h_fst_nat : ∀ {X Y Z : C_} (f : X ⟶ Y),
    f ▷ Z ≫ fst Y Z = fst X Z ≫ f := by intros; simp
  have h_snd_nat : ∀ {X Y Z : C_} (f : X ⟶ Y), f ▷ Z ≫ snd Y Z = snd X Z := by intros; simp
  have h_fst_nat_L : ∀ {X Y Z : C_} (f : X ⟶ Y),
    Z ◁ f ≫ fst Z Y = fst Z X := by intros; simp
  have h_snd_nat_L : ∀ {X Y Z : C_} (f : X ⟶ Y),
    Z ◁ f ≫ snd Z Y = snd Z X ≫ f := by intros; simp
  have associator_fst : ∀ (X Y Z : C_),
    (α_ X Y Z).hom ≫ fst X (Y ⊗ Z) = fst (X ⊗ Y) Z ≫ fst X Y := by intros; simp
  have associator_snd_fst : ∀ (X Y Z : C_),
    (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) ≫ fst Y Z = fst (X ⊗ Y) Z ≫ snd X Y := by intros; simp
  have associator_snd_snd : ∀ (X Y Z : C_),
    (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) ≫ snd Y Z = snd (X ⊗ Y) Z := by intros; simp
  have h_lift_fst : ∀ {X Y Z : C_} (f : X ⟶ Y) (g : X ⟶ Z), lift f g ≫ fst Y Z = f := by
    intros; simp
  have h_lift_snd : ∀ {X Y Z : C_} (f : X ⟶ Y) (g : X ⟶ Z), lift f g ≫ snd Y Z = g := by
    intros; simp
  exact {
    one := one
    mul := mul
    inv := inv
    one_mul := by
      apply (e (𝟙_ C_ ⊗ X)).injective
      rw [he_nat, he_mul, map_add, ← he_nat, ← he_nat, h_fst_nat, h_snd_nat, he_nat, he_one,
        map_zero, zero_add, ← leftUnitor_hom X]
    mul_one := by
      apply (e (X ⊗ 𝟙_ C_)).injective
      rw [he_nat, he_mul, map_add, ← he_nat, ← he_nat, h_fst_nat_L, h_snd_nat_L, he_nat, he_one,
        map_zero, add_zero, ← rightUnitor_hom X]
    mul_assoc := by
      apply (e ((X ⊗ X) ⊗ X)).injective
      have h1 : e _ (mul ▷ X ≫ mul) =
          e _ (fst (X ⊗ X) X ≫ fst X X) + e _ (fst (X ⊗ X) X ≫ snd X X) +
            e _ (snd (X ⊗ X) X) := by
        rw [he_nat, he_mul, map_add, ← he_nat, ← he_nat, h_fst_nat mul, h_snd_nat mul, he_nat,
          he_mul, map_add, ← he_nat, ← he_nat]; rfl
      have h2 : e _ ((α_ X X X).hom ≫ X ◁ mul ≫ mul) =
          e _ (fst (X ⊗ X) X ≫ fst X X) + e _ (fst (X ⊗ X) X ≫ snd X X) +
            e _ (snd (X ⊗ X) X) := by
        rw [← Category.assoc, he_nat, he_mul, map_add, ← he_nat, ← he_nat]
        simp only [Category.assoc]
        rw [h_fst_nat_L, h_snd_nat_L, associator_fst]
        have hA2 : e _ ((α_ X X X).hom ≫ snd X (X ⊗ X) ≫ mul) =
            e _ (fst (X ⊗ X) X ≫ snd X X) + e _ (snd (X ⊗ X) X) := by
          rw [← Category.assoc, he_nat, he_mul, map_add, ← he_nat, ← he_nat]
          simp only [Category.assoc]; rw [associator_snd_fst, associator_snd_snd]; rfl
        rw [hA2, add_assoc]; rfl
      rw [h1, h2]
    left_inv := by
      apply (e X).injective
      have h1 : e X (lift inv (𝟙 X) ≫ mul) =
          e X (lift inv (𝟙 X) ≫ fst X X) + e X (lift inv (𝟙 X) ≫ snd X X) := by
        rw [he_nat, he_mul, map_add]; simp only [← he_nat]; rfl
      rw [h1, h_lift_fst inv (𝟙 X), h_lift_snd inv (𝟙 X), he_inv, neg_add_cancel, he_nat, he_one,
        map_zero]; rfl
    right_inv := by
      apply (e X).injective
      have h1 : e X (lift (𝟙 X) inv ≫ mul) =
          e X (lift (𝟙 X) inv ≫ fst X X) + e X (lift (𝟙 X) inv ≫ snd X X) := by
        rw [he_nat, he_mul, map_add]; simp only [← he_nat]; rfl
      rw [h1, h_lift_fst (𝟙 X) inv, h_lift_snd (𝟙 X) inv, he_inv, add_neg_cancel, he_nat, he_one,
        map_zero]; rfl
  }

end TauCeti.Jacobian
