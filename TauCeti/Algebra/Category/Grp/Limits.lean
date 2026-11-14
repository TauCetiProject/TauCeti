/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits

/-!
# The group operations on sections of a functor to groups

Mathlib's `GrpCat.sectionsGroup` makes the sections of a functor `F : J ⥤ GrpCat` a group, with
the pointwise operations. This file records the values of the identity, products, inverses and
quotients of sections at each object, and their additive analogues.

## Main results

* `GrpCat.sections_mul_val`: the value of a product of sections is the product of the values.
* `GrpCat.sections_inv_val`: the value of the inverse of a section is the inverse of its value.
-/

@[expose] public section

open CategoryTheory

universe v u w

variable {J : Type v} [Category.{w} J] {F : J ⥤ GrpCat.{u}}

namespace GrpCat

/-- The identity section takes the value `1` at each object. -/
@[to_additive (attr := simp) /-- The zero section takes the value `0` at each object. -/]
lemma sections_one_val (j : J) : (1 : (F ⋙ forget GrpCat).sections).1 j = 1 :=
  (rfl)

/-- The value of a product of sections is the product of their values. -/
@[to_additive (attr := simp) /-- The value of a sum of sections is the sum of their values. -/]
lemma sections_mul_val (s t : (F ⋙ forget GrpCat).sections) (j : J) :
    (s * t).1 j = s.1 j * t.1 j :=
  (rfl)

/-- The value of the inverse of a section is the inverse of its value. -/
@[to_additive (attr := simp)
/-- The value of the negation of a section is the negation of its value. -/]
lemma sections_inv_val (s : (F ⋙ forget GrpCat).sections) (j : J) : s⁻¹.1 j = (s.1 j)⁻¹ :=
  (rfl)

/-- The value of a quotient of sections is the quotient of their values. -/
@[to_additive (attr := simp)
/-- The value of a difference of sections is the difference of their values. -/]
lemma sections_div_val (s t : (F ⋙ forget GrpCat).sections) (j : J) :
    (s / t).1 j = s.1 j / t.1 j :=
  (rfl)

end GrpCat
