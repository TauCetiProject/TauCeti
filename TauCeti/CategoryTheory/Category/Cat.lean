/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat

/-!
# Coherence isomorphisms of identity functors in Cat

The associator and right unitor of identity functors in the bicategory of categories are
identity natural transformations.
-/

public section

universe w v

open CategoryTheory Bicategory

namespace CategoryTheory.Cat

/-- The associator of three identity functors in `Cat` is the identity. -/
@[simp]
lemma associator_id_hom (C : Type w) [Category.{v} C] :
    (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The inverse associator of three identity functors in `Cat` is the identity. -/
@[simp]
lemma associator_id_inv (C : Type w) [Category.{v} C] :
    (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).inv = 𝟙 _ := by
  ext X
  simp

/-- The right unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma rightUnitor_id_hom (C : Type w) [Category.{v} C] :
    (ρ_ (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The inverse right unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma rightUnitor_id_inv (C : Type w) [Category.{v} C] :
    (ρ_ (𝟙 (Cat.of C))).inv = 𝟙 _ := by
  ext X
  simp

end CategoryTheory.Cat
