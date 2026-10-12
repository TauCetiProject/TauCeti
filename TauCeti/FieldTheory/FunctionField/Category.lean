/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# The category of algebraic function fields

`FunctionFieldCat k` is the full subcategory of commutative `k`-algebras consisting of fields
that are essentially of finite type and have transcendence degree one. Equivalently, its
objects satisfy the intrinsic predicate `IsFunctionField k F`. Its morphisms are all
`k`-algebra homomorphisms, hence embeddings. Neither a rational parameter nor exactness of the
constant field is part of an object.

The category and its concrete structure are inherited from Mathlib's `CommAlgCat` and
`ObjectProperty.FullSubcategory`. This supplies the field side of the contravariant
correspondence with regular curves.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Appendix B.
* R. Hartshorne, *Algebraic Geometry*, Chapter I, Section 6.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

/-- Algebraic function fields of one variable over `k`, with `k`-algebra embeddings.
The field condition is a property of the underlying commutative ring, so objects carry no
additional choice of an inverse operation or rational parameter. -/
abbrev FunctionFieldCat (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (fun A : CommAlgCat.{v} k ↦
    IsField A ∧ Algebra.EssFiniteType k A ∧ Algebra.trdeg k A = 1)

namespace FunctionFieldCat

variable {k : Type u} [Field k]

instance : CoeSort (FunctionFieldCat.{u, v} k) (Type v) := ⟨fun F ↦ F.obj⟩

/-- The field structure on an object is recovered from its field property. -/
noncomputable instance (F : FunctionFieldCat k) : Field F := F.property.1.toField

instance (F : FunctionFieldCat k) : Algebra k F := inferInstanceAs (Algebra k F.obj)

instance (F : FunctionFieldCat k) : Algebra.EssFiniteType k F := F.property.2.1

/-- Every object of the category is an algebraic function field. -/
theorem isFunctionField (F : FunctionFieldCat k) : IsFunctionField k F :=
  isFunctionField_iff_trdeg_eq_one.mpr F.property.2.2

/-- Regard an algebraic function field as an object, without choosing a rational parameter. -/
abbrev of (k : Type u) [Field k] (F : Type v) [Field F] [Algebra k F]
    (hF : IsFunctionField k F) : FunctionFieldCat.{u, v} k :=
  ⟨CommAlgCat.of k F, Field.toIsField F, hF.essFiniteType, hF.trdeg_eq_one⟩

/-- The underlying type of the object constructed from `F` is `F`. -/
@[simp] theorem coe_of (F : Type v) [Field F] [Algebra k F] (hF : IsFunctionField k F) :
    (of k F hF : Type v) = F := rfl

/-- The rational function field is an object of the category over every field. -/
noncomputable abbrev ratFunc (k : Type u) [Field k] : FunctionFieldCat.{u, u} k :=
  of k (RatFunc k) (IsFunctionField.ratFunc k)

/-- The fully faithful inclusion into commutative `k`-algebras. -/
abbrev inclusion (k : Type u) [Field k] : FunctionFieldCat.{u, v} k ⥤ CommAlgCat.{v} k :=
  ObjectProperty.ι _

end FunctionFieldCat

end TauCeti
