/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.IsFinite
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# The abelian category of finite abelian groups

Mathlib's Serre class of finite abelian groups is closed under finite products. Its full
subcategory therefore inherits an abelian category structure, and its inclusion into all abelian
groups is exact. The finite cyclic group of order `n` has underlying group `ZMod n`; its
morphisms are determined by the image of `1`.
-/

public section

open CategoryTheory

namespace AddCommGrpCat

/-- Finite abelian groups are closed under finite products in the category of abelian groups. -/
instance isClosedUnderFiniteProducts_isFinite :
    isFinite.{u}.IsClosedUnderFiniteProducts := by
  have : isFinite.{u}.IsClosedUnderBinaryProducts :=
    isFinite.isClosedUnderBinaryProducts_of_prop_biprod fun _ _ hX hY ↦ isFinite.prop_biprod hX hY
  exact .mk'

end AddCommGrpCat

namespace TauCeti

/-- The abelian category of finite abelian groups. -/
abbrev FiniteAbelianGrp := AddCommGrpCat.isFinite.FullSubcategory

end TauCeti

namespace TauCeti.FiniteAbelianGrp

/-- The finite cyclic group `ℤ/nℤ` as an object of the category of finite abelian groups. -/
abbrev zmod (n : ℕ) [NeZero n] : FiniteAbelianGrp.{0} :=
  ⟨AddCommGrpCat.of (ZMod n), inferInstanceAs (Finite (ZMod n))⟩

/-- The underlying abelian group of `zmod n` is `ZMod n`. -/
@[simp]
theorem zmod_obj (n : ℕ) [NeZero n] : (zmod n).obj = AddCommGrpCat.of (ZMod n) :=
  (rfl)

variable (n : ℕ) [NeZero n]

/-- A map out of the finite cyclic group is determined by its value at `1`. -/
theorem zmod_hom_ext {Y : FiniteAbelianGrp.{0}} {f g : zmod n ⟶ Y}
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

/-- Multiplication by `1` is the identity endomorphism. -/
@[simp]
theorem zmodMul_one : zmodMul n 1 = 𝟙 (zmod n) :=
  zmod_hom_ext n ((zmodMul_apply n 1 1).trans (one_mul 1))

end TauCeti.FiniteAbelianGrp
