/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Ideal.Over

/-!
# Residue separability under a group action

If a group acts on an algebra while fixing its base, translation by a group element identifies
the residue extension at an ideal with the residue extension at the translated ideal.
Consequently separability of the residue extension is invariant under translation.

Thus separability at one prime suffices throughout its group orbit. No primality or maximality is
assumed, since `Algebra.IsSeparable` is defined over arbitrary commutative base rings: the
translated ideal has the same contraction, and translation induces an isomorphism of the quotient
algebras over it.

## Main result

* `Ideal.Quotient.isSeparable_smul`: residue separability is preserved by translation.
-/

public section

open scoped Pointwise

namespace Ideal

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- Separability of `B ⧸ Q` over `A ⧸ Q.under A` is preserved when the ideal `Q` is translated by
a group action that fixes the base ring. -/
theorem Quotient.isSeparable_smul (Q : Ideal B) (σ : G)
    [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)] :
    Algebra.IsSeparable (A ⧸ (σ • Q).under A) (B ⧸ σ • Q) := by
  -- The contractions of `σ • Q` and `Q` are equal but not definitionally so; abstract the lower
  -- ideal so that the equation can be substituted.
  have key (p : Ideal A) [(σ • Q).LiesOver p] (hp : p = Q.under A) :
      Algebra.IsSeparable (A ⧸ p) (B ⧸ σ • Q) := by
    subst hp
    exact AlgEquiv.Algebra.isSeparable <|
      algEquivOfEqMap (Q.under A) (MulSemiringAction.toAlgEquiv A B σ) (by
        rw [pointwise_smul_eq_comap, ← map_comap_of_equiv]
        -- Both maps are the ring-hom coercion of the action of `σ` on `B`.
        rfl)
  exact key _ (under_smul A Q σ)

end Ideal
