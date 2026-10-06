/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Additive and linear structure on morphisms of a full subcategory

A full subcategory of a preadditive (resp. `R`-linear) category inherits a preadditive
(resp. `R`-linear) structure. This file records that the underlying morphism of a sum, a
negation, a difference or a scalar multiple of morphisms in the full subcategory is the
corresponding operation applied to the underlying morphisms in the ambient category. The zero
morphism is Mathlib's `CategoryTheory.ObjectProperty.zero_hom`.

## Main results

* `CategoryTheory.ObjectProperty.add_hom`, `CategoryTheory.ObjectProperty.neg_hom`,
  `CategoryTheory.ObjectProperty.sub_hom`: the underlying morphism of a morphism built from the
  preadditive structure.
* `CategoryTheory.ObjectProperty.smul_hom`: the underlying morphism of a scalar multiple.
-/

public section

namespace CategoryTheory.ObjectProperty

universe w v u

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

section Preadditive

variable [Preadditive C] {X Y : P.FullSubcategory}

/-- The underlying morphism of a sum in a full subcategory is the sum of the underlying
morphisms. -/
@[simp] theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl

/-- The underlying morphism of a negation in a full subcategory is the negation of the underlying
morphism. -/
@[simp] theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl

/-- The underlying morphism of a difference in a full subcategory is the difference of the
underlying morphisms. -/
@[simp] theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl

end Preadditive

/-- The underlying morphism of a scalar multiple in a full subcategory of a linear category is the
scalar multiple of the underlying morphism. -/
@[simp] theorem smul_hom {R : Type w} [Semiring R] [Preadditive C] [Linear R C]
    {X Y : P.FullSubcategory} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom := rfl

end CategoryTheory.ObjectProperty
