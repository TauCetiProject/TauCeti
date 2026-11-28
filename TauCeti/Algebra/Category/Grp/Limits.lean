/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Whiskering

/-!
# The group operations on sections of a functor to groups

Mathlib's `GrpCat.sectionsGroup` makes the sections of a functor `F : J ⥤ GrpCat` a group, with
the pointwise operations. This file records the values of the identity, products, inverses and
quotients of sections at each object, and their additive analogues. A natural transformation
also induces `GrpCat.sectionsMap`, bundling Mathlib’s `Functor.sectionsFunctor` with the
pointwise group laws.

## Main results

* `GrpCat.sections_mul_val`: the value of a product of sections is the product of the values.
* `GrpCat.sections_inv_val`: the value of the inverse of a section is the inverse of its value.
-/

public section

open CategoryTheory

universe v u w

variable {J : Type v} [Category.{w} J] {F : J ⥤ GrpCat.{u}}

namespace GrpCat

/-- The identity section takes the value `1` at each object. -/
@[to_additive (attr := simp) /-- The zero section takes the value `0` at each object. -/]
lemma sections_one_val (j : J) : (1 : (F ⋙ forget GrpCat).sections).val j = 1 :=
  (rfl)

/-- The value of a product of sections is the product of their values. -/
@[to_additive (attr := simp) /-- The value of a sum of sections is the sum of their values. -/]
lemma sections_mul_val (s t : (F ⋙ forget GrpCat).sections) (j : J) :
    (s * t).val j = s.val j * t.val j :=
  (rfl)

/-- The value of the inverse of a section is the inverse of its value. -/
@[to_additive (attr := simp)
/-- The value of the negation of a section is the negation of its value. -/]
lemma sections_inv_val (s : (F ⋙ forget GrpCat).sections) (j : J) : s⁻¹.val j = (s.val j)⁻¹ :=
  (rfl)

/-- The value of a quotient of sections is the quotient of their values. -/
@[to_additive (attr := simp)
/-- The value of a difference of sections is the difference of their values. -/]
lemma sections_div_val (s t : (F ⋙ forget GrpCat).sections) (j : J) :
    (s / t).val j = s.val j / t.val j :=
  (rfl)

variable {G H : J ⥤ GrpCat.{u}}

/-- The homomorphism on compatible sections induced by a natural transformation. -/
def sectionsMap (α : F ⟶ G) : (F ⋙ forget GrpCat).sections →* (G ⋙ forget GrpCat).sections where
  toFun := (Functor.sectionsFunctor J).map (Functor.whiskerRight α (forget GrpCat))
  map_one' := by ext U; exact map_one (α.app U).hom
  map_mul' s t := by ext U; exact map_mul (α.app U).hom (s.val U) (t.val U)

@[simp]
lemma sectionsMap_apply (α : F ⟶ G) (s : (F ⋙ forget GrpCat).sections) (U : J) :
    (sectionsMap α s).val U = α.app U (s.val U) := (rfl)

@[simp]
lemma sectionsMap_id : sectionsMap (𝟙 F) = MonoidHom.id _ := by ext s U; rfl

@[simp]
lemma sectionsMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    sectionsMap (α ≫ β) = (sectionsMap β).comp (sectionsMap α) := by ext s U; rfl

end GrpCat
