/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Precomposing an internal Hom with an isomorphism

`MonoidalClosed.pre f` is the mate of the left tensoring along `f` under the two tensor--Hom
adjunctions, and tensoring on the left is invertible along an isomorphism, so precomposing an
internal Hom with an isomorphism is an isomorphism.  This is the isomorphism instance
`CategoryTheory.conjugateEquiv_iso` read at `MonoidalClosed.pre`, and it is the reusable form of
that computation, for instance when an isomorphism of objects identifies the internal Hom
functors involved in a comparison.

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
  have hα : IsIso ((tensoringLeft C).map e.hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    exact MonoidalCategory.whiskerRight_isIso e.hom Z
  unfold MonoidalClosed.pre
  exact @conjugateEquiv_iso _ _ _ _ _ _ _ _ (ihom.adjunction _) (ihom.adjunction _)
    ((tensoringLeft C).map e.hom) hα

end CategoryTheory
