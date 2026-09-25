/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Precomposing an internal Hom with an isomorphism

`MonoidalClosed.pre_isIso` states that precomposition by an isomorphism of objects is an
isomorphism of internal Hom functors.  Use it when an isomorphism of source objects identifies
the two internal Hom functors appearing in a comparison, so that invertibility, or any other
isomorphism-level property, can be read across that identification.  For instance it is how
the invertibility of one internal-Hom comparison is transported to an isomorphic source object
in `CategoryTheory.Functor.ihomComparison_isIso_of_iso`.  It is Mathlib's isomorphism instance
`CategoryTheory.conjugateEquiv_iso` specialized to `MonoidalClosed.pre`.

## Main declaration

* `MonoidalClosed.pre_isIso`.
-/

public section

namespace CategoryTheory

open Category MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Precomposition with an isomorphism, as a natural transformation between internal Hom
functors, is an isomorphism. -/
theorem MonoidalClosed.pre_isIso {A B : C} (e : A ≅ B) [Closed A] [Closed B] :
    IsIso (MonoidalClosed.pre e.hom) := by
  -- `pre` is the mate of the left tensoring along `e.hom` under the two tensor--Hom
  -- adjunctions, and tensoring on the left takes an isomorphism of objects to an isomorphism
  -- of functors, so the mate is invertible.
  have hα : IsIso ((tensoringLeft C).map e.hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    exact MonoidalCategory.whiskerRight_isIso e.hom Z
  unfold MonoidalClosed.pre
  exact @conjugateEquiv_iso _ _ _ _ _ _ _ _ (ihom.adjunction _) (ihom.adjunction _)
    ((tensoringLeft C).map e.hom) hα

end CategoryTheory
