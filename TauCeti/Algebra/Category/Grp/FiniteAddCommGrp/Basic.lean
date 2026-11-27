/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.IsFinite
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# The abelian category of finite abelian groups

Mathlib's Serre class of finite abelian groups is closed under finite products. Its full
subcategory therefore inherits an abelian category structure, and its inclusion into all abelian
groups is exact. The finite cyclic group of order `n` has underlying group `ZMod n`; its
morphisms are determined by the image of `1`.
-/

public section

open CategoryTheory

namespace TauCeti

/-- The abelian category of finite abelian groups. -/
abbrev FiniteAddCommGrp := AddCommGrpCat.isFinite.FullSubcategory

end TauCeti

namespace TauCeti.FiniteAddCommGrp

/-- The finite cyclic group `ℤ/nℤ` as an object of the category of finite abelian groups. -/
abbrev zmod (n : ℕ) [NeZero n] : FiniteAddCommGrp.{0} :=
  ⟨AddCommGrpCat.of (ZMod n), inferInstanceAs (Finite (ZMod n))⟩

/-- The underlying abelian group of `zmod n` is `ZMod n`. -/
@[simp]
theorem zmod_obj (n : ℕ) [NeZero n] : (zmod n).obj = AddCommGrpCat.of (ZMod n) :=
  (rfl)

variable (n : ℕ) [NeZero n]

/-- A map out of the finite cyclic group is determined by its value at `1`. -/
theorem zmod_hom_ext {Y : FiniteAddCommGrp.{0}} {f g : zmod n ⟶ Y}
    (h : f.hom (1 : ZMod n) = g.hom (1 : ZMod n)) : f = g := by
  apply AddCommGrpCat.isFinite.ι.map_injective
  ext x
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  simpa only [ObjectProperty.ι_map, ← zsmul_one, map_zsmul] using congrArg (a • ·) h

/-- Multiplication by an element of `ℤ/nℤ`, as an endomorphism of the finite cyclic group. -/
def zmodMul : ZMod n →+ (zmod n ⟶ zmod n) :=
  InducedCategory.homAddEquiv.symm.toAddMonoidHom.comp
    (AddCommGrpCat.homAddEquiv.symm.toAddMonoidHom.comp (AddMonoid.End.mulLeft : _ →+ _))

/-- The endomorphism `zmodMul n a` acts by multiplication by `a`. -/
@[simp]
theorem zmodMul_apply (a b : ZMod n) : (zmodMul n a).hom b = a * b :=
  (rfl)

/-- Multiplication endomorphisms of the finite cyclic group distinguish the multipliers. -/
theorem zmodMul_injective : Function.Injective (zmodMul n) := by
  intro a b h
  have h₁ : (zmodMul n a).hom (1 : ZMod n) = (zmodMul n b).hom (1 : ZMod n) :=
    congrArg (fun f : zmod n ⟶ zmod n ↦ f.hom (1 : ZMod n)) h
  simpa only [mul_one] using
    (zmodMul_apply n a 1).symm.trans (h₁.trans (zmodMul_apply n b 1))

/-- Multiplication by `1` is the identity endomorphism. -/
@[simp]
theorem zmodMul_one : zmodMul n 1 = 𝟙 (zmod n) :=
  zmod_hom_ext n ((zmodMul_apply n 1 1).trans (one_mul 1))

end TauCeti.FiniteAddCommGrp
