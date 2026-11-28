/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Ext with an action on the source

An action of a semiring on the source through its opposite endomorphism ring acts by
precomposition on Ext. The resulting module is covariant in the target.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace TauCeti.Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A : Type*} [Semiring A] {X : C}

/-- Ext with the left action induced by precomposition by an action on the source object. -/
def ExtWithSourceAction (_ρ : A →+* (End X)ᵐᵒᵖ) (Y : C) (n : ℕ) : Type w :=
  Ext X Y n

namespace ExtWithSourceAction

variable (ρ : A →+* (End X)ᵐᵒᵖ) {Y Y' Y'' : C} {n : ℕ}

instance : AddCommGroup (ExtWithSourceAction ρ Y n) :=
  inferInstanceAs (AddCommGroup (Ext X Y n))

private abbrev precompose (a : A) (x : Ext X Y n) : Ext X Y n :=
  (Ext.mk₀ (ρ a).unop.asHom).comp x (zero_add n)

private lemma precompose_one (x : Ext X Y n) : precompose ρ 1 x = x := by
  simp [precompose, End.one_asHom]

private lemma precompose_mul (a b : A) (x : Ext X Y n) :
    precompose ρ (a * b) x = precompose ρ a (precompose ρ b x) := by
  simp [precompose, End.mul_asHom]

private lemma precompose_zero (x : Ext X Y n) : precompose ρ 0 x = 0 := by
  simp [precompose]

private lemma precompose_add (a b : A) (x : Ext X Y n) :
    precompose ρ (a + b) x = precompose ρ a x + precompose ρ b x := by
  simp [precompose, Ext.mk₀_add]

/-- Scalars act on Ext by precomposition with the corresponding source endomorphism. -/
@[no_expose]
instance : Module A (ExtWithSourceAction ρ Y n) :=
  { smul := precompose ρ
    one_smul := precompose_one ρ
    mul_smul := precompose_mul ρ
    smul_zero a := Ext.comp_zero (Ext.mk₀ (ρ a).unop.asHom) Y n n (zero_add n)
    smul_add a x y := Ext.comp_add (Ext.mk₀ (ρ a).unop.asHom) x y (zero_add n)
    zero_smul := precompose_zero ρ
    add_smul := precompose_add ρ }

/-- Forget the action to recover the ordinary Ext group. -/
def toExt : ExtWithSourceAction ρ Y n ≃+ Ext X Y n := AddEquiv.refl _

/-- Scalars act on Ext by precomposition with the corresponding source endomorphism. -/
@[simp]
theorem toExt_smul (a : A) (x : ExtWithSourceAction ρ Y n) :
    toExt ρ (a • x) = (Ext.mk₀ (ρ a).unop.asHom).comp (toExt ρ x) (zero_add n) :=
  (rfl)

/-- Pushforward along a morphism of targets is linear for the source action. -/
def map (f : Y ⟶ Y') : ExtWithSourceAction ρ Y n →ₗ[A] ExtWithSourceAction ρ Y' n where
  toFun x := (toExt ρ).symm ((toExt ρ x).comp (Ext.mk₀ f) (add_zero n))
  map_add' x y := by simp
  map_smul' a x := (toExt ρ).injective (by
    simp only [AddEquiv.apply_symm_apply, toExt_smul, RingHom.id_apply,
      Ext.comp_assoc_of_third_deg_zero])

/-- Pushforward on the module with source action agrees with ordinary Ext pushforward. -/
@[simp]
theorem toExt_map (f : Y ⟶ Y') (x : ExtWithSourceAction ρ Y n) :
    toExt ρ (map ρ f x) = (toExt ρ x).comp (Ext.mk₀ f) (add_zero n) :=
  (toExt ρ).apply_symm_apply _

/-- Pushforward along the identity acts as the identity on Ext. -/
@[simp]
theorem map_id : map ρ (n := n) (𝟙 Y) = LinearMap.id := by
  ext x
  apply (toExt ρ).injective
  simp

/-- Pushforward on Ext respects composition of target morphisms. -/
@[simp]
theorem map_comp (f : Y ⟶ Y') (g : Y' ⟶ Y'') :
    map ρ (n := n) (f ≫ g) = map ρ g ∘ₗ map ρ f := by
  ext x
  apply (toExt ρ).injective
  simp [← Ext.mk₀_comp_mk₀]

/-- An isomorphism of targets induces a linear equivalence on Ext with source action. -/
def linearEquivOfIso (e : Y ≅ Y') (n : ℕ) :
    ExtWithSourceAction ρ Y n ≃ₗ[A] ExtWithSourceAction ρ Y' n :=
  LinearEquiv.ofLinearMap (map ρ e.hom) (map ρ e.inv)
    (by rw [← map_comp, e.inv_hom_id, map_id])
    (by rw [← map_comp, e.hom_inv_id, map_id])

/-- The target-isomorphism comparison is given by pushforward along the isomorphism. -/
@[simp]
theorem toExt_linearEquivOfIso (e : Y ≅ Y') (n : ℕ) (x : ExtWithSourceAction ρ Y n) :
    toExt ρ (linearEquivOfIso ρ e n x) = (toExt ρ x).comp (Ext.mk₀ e.hom) (add_zero n) :=
  toExt_map ρ e.hom x

/-- An additive comparison respecting the source action upgrades to a linear equivalence. -/
def linearEquivOfCompat {V : Type*} [AddCommGroup V] [Module A V] (e : V ≃+ Ext X Y n)
    (he : ∀ (a : A) (x : V),
      e (a • x) = (Ext.mk₀ (ρ a).unop.asHom).comp (e x) (zero_add n)) :
    V ≃ₗ[A] ExtWithSourceAction ρ Y n :=
  (e.trans (toExt ρ).symm).toLinearEquiv fun a x ↦ (toExt ρ).injective (by
    simpa only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, toExt_smul] using he a x)

/-- Forgetting the source action recovers the original additive comparison. -/
@[simp]
theorem toExt_linearEquivOfCompat {V : Type*} [AddCommGroup V] [Module A V] (e : V ≃+ Ext X Y n)
    (he : ∀ (a : A) (x : V),
      e (a • x) = (Ext.mk₀ (ρ a).unop.asHom).comp (e x) (zero_add n)) (x : V) :
    toExt ρ (linearEquivOfCompat ρ e he x) = e x :=
  (toExt ρ).apply_symm_apply _

end ExtWithSourceAction

end TauCeti.Abelian
