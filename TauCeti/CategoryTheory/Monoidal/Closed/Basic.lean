/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Precomposing an internal Hom with an isomorphism or an epimorphism

`MonoidalClosed.pre_isIso` states that precomposition by an isomorphism of objects is an
isomorphism of internal Hom functors, and `MonoidalClosed.mono_pre_app` that, in a braided
closed monoidal category, precomposition by an epimorphism is a monomorphism of internal
Homs: `[-, X]` is contravariant and turns epimorphisms into monomorphisms.

Use `MonoidalClosed.pre_isIso` when an isomorphism of source objects identifies the two internal
Hom functors appearing in a comparison, so that invertibility, or any other isomorphism-level
property, can be read across that identification.  For instance it is how
the invertibility of one internal-Hom comparison is transported to an isomorphic source object
in `CategoryTheory.Functor.ihomComparison_isIso_of_iso`.  It is Mathlib's isomorphism instance
`CategoryTheory.conjugateEquiv_iso` specialized to `MonoidalClosed.pre`.

## Main declarations

* `MonoidalClosed.pre_isIso`;
* `MonoidalClosed.mono_pre_app`.
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

/-- In a braided closed monoidal category, precomposition of internal Homs with an epimorphism
`f : B ⟶ A` is a monomorphism `(A ⟶[C] X) ⟶ (B ⟶[C] X)`. -/
instance MonoidalClosed.mono_pre_app [BraidedCategory C] [MonoidalClosed C] {A B : C}
    (f : B ⟶ A) [Epi f] (X : C) : Mono ((MonoidalClosed.pre f).app X) where
  right_cancellation {Z} g h hgh := by
    -- Uncurrying turns precomposition with `f` into whiskering by `f`, which is an epimorphism:
    -- it is conjugate under the braiding to `Z ◁ f`, and tensoring on the left preserves
    -- colimits in a closed monoidal category.
    have hf : Epi (f ▷ Z) := by
      rw [(Iso.eq_comp_inv _).mpr (BraidedCategory.braiding_naturality_left f Z)]
      have : Epi (Z ◁ f) := (tensorLeft Z).map_epi f
      infer_instance
    apply MonoidalClosed.uncurry_injective
    have e := congrArg MonoidalClosed.uncurry hgh
    rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_pre_app] at e
    exact (cancel_epi _).1 e

end CategoryTheory
