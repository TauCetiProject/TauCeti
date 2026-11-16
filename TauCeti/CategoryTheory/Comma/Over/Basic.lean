/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Full faithfulness of `Over.map` along a monomorphism

For any monomorphism `j : U ⟶ S` in a category `C`, postcomposition along `j` defines a fully
faithful functor `Over.map j : Over U ⥤ Over S`.

## Main declarations

* `CategoryTheory.Over.fullyFaithfulMap`: `Over.map j` is fully faithful when `j` is a
  monomorphism.
-/

public section

namespace CategoryTheory.Over

variable {C : Type*} [Category* C]

/-- For a monomorphism `j : U ⟶ S`, the postcomposition functor `Over.map j : Over U ⥤ Over S` is
fully faithful. -/
def fullyFaithfulMap {U S : C} (j : U ⟶ S) [Mono j] : (Over.map j).FullyFaithful where
  preimage {A B} φ := Over.homMk φ.left (by
    rw [← cancel_mono j, Category.assoc]
    exact Over.w φ)
  map_preimage _ := rfl
  preimage_map _ := rfl

end CategoryTheory.Over
