/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.IsFinite
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import TauCeti.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.Data.ZMod.MonoidHomEquiv

/-!
# The abelian category of finite abelian groups

Mathlib's Serre class of finite abelian groups is closed under finite products. Its full
subcategory therefore inherits an abelian category structure, and its inclusion into all abelian
groups is exact. The finite cyclic group of order `n` has underlying group `ULift (ZMod n)`; its
morphisms are determined by the image of `1`.
-/

public section

open CategoryTheory

namespace TauCeti

/-- The abelian category of finite abelian groups. -/
abbrev FiniteAddCommGrp := AddCommGrpCat.isFinite.FullSubcategory

end TauCeti

namespace TauCeti.FiniteAddCommGrp

universe u

/-- The finite cyclic group `ℤ/nℤ` as an object of the category of finite abelian groups. -/
abbrev zmod (n : ℕ) [NeZero n] : FiniteAddCommGrp.{u} :=
  ⟨AddCommGrpCat.of (ULift.{u} (ZMod n)), inferInstanceAs (Finite (ULift.{u} (ZMod n)))⟩

/-- The underlying abelian group of `zmod n` is the universe lift of `ZMod n`. -/
@[simp]
theorem zmod_obj (n : ℕ) [NeZero n] : (zmod.{u} n).obj = AddCommGrpCat.of (ULift.{u} (ZMod n)) :=
  (rfl)

variable (n : ℕ) [NeZero n]

/-- A map out of the finite cyclic group is determined by its value at `1`. -/
theorem zmod_hom_ext {Y : FiniteAddCommGrp.{u}} {f g : zmod n ⟶ Y}
    (h : f.hom (ULift.up 1) = g.hom (ULift.up 1)) : f = g :=
  AddCommGrpCat.isFinite.hom_ext (AddCommGrpCat.hom_ext
    ((AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).addMonoidHomCongrLeftEquiv.injective
      (AddMonoidHom.ext_zmod h)))

/-- Multiplication by an element of `ℤ/nℤ`, as an endomorphism of the finite cyclic group. -/
def zmodMul : ZMod n →+ (zmod.{u} n ⟶ zmod.{u} n) :=
  InducedCategory.homAddEquiv.symm.toAddMonoidHom.comp
    (AddCommGrpCat.homAddEquiv.symm.toAddMonoidHom.comp
      ((AddMonoid.End.mulLeft : ULift.{u} (ZMod n) →+ _).comp
        AddEquiv.ulift.symm.toAddMonoidHom))

/-- The endomorphism `zmodMul n a` acts by multiplication by `a`. -/
@[simp↓]
theorem zmodMul_apply (a : ZMod n) (b : ULift.{u} (ZMod n)) :
    (zmodMul.{u} n a).hom b = ULift.up (a * b.down) :=
  (rfl)

/-- Multiplication endomorphisms of the finite cyclic group distinguish the multipliers. -/
theorem zmodMul_injective : Function.Injective (zmodMul.{u} n) := by
  intro a b h
  have h₁ : (zmodMul.{u} n a).hom (ULift.up 1) = (zmodMul.{u} n b).hom (ULift.up 1) :=
    congrArg (fun f : zmod.{u} n ⟶ zmod.{u} n ↦ f.hom (ULift.up 1)) h
  rw [zmodMul_apply n a, zmodMul_apply n b, ULift.down_up, mul_one, mul_one] at h₁
  exact ULift.up_injective h₁

/-- Multiplication by `1` is the identity endomorphism. -/
@[simp]
theorem zmodMul_one : zmodMul.{u} n 1 = 𝟙 (zmod n) := by
  apply zmod_hom_ext
  rw [zmodMul_apply, ULift.down_up, one_mul, ObjectProperty.FullSubcategory.id_hom,
    ConcreteCategory.id_apply]

end TauCeti.FiniteAddCommGrp
