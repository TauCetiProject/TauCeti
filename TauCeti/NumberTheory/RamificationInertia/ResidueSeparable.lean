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
the residue extension at a maximal ideal with the residue extension at the translated ideal.
Consequently separability of the residue extension is invariant under translation.

The result uses Mathlib's `Ideal.Quotient.algEquivOfEqMap` for the upper residue fields and the
equality `Ideal.under_smul` for the lower ideals. It assumes maximality of both the upper ideal
and its contraction, which says exactly that the quotients in the residue extension are fields.

## Main result

* `Ideal.Quotient.isSeparable_smul`: residue separability is preserved by translation.
-/

public section

open scoped Pointwise

namespace Ideal

attribute [local instance] Ideal.Quotient.field

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- Residue separability is preserved when a maximal ideal is translated by a group action
that fixes the base ring. -/
theorem Quotient.isSeparable_smul (Q : Ideal B) [Q.IsMaximal] [(Q.under A).IsMaximal] (σ : G)
    [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)] :
    Algebra.IsSeparable (A ⧸ (σ • Q).under A) (B ⧸ σ • Q) := by
  let _ : (σ • Q).IsMaximal := by
    rw [pointwise_smul_eq_comap]
    infer_instance
  let _ : ((σ • Q).under A).IsMaximal := by
    rw [under_smul]
    infer_instance
  let e : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ σ • Q) :=
    Ideal.Quotient.algEquivOfEqMap (Q.under A) (MulSemiringAction.toAlgEquiv A B σ) (by
      rw [pointwise_smul_eq_comap, ← map_comap_of_equiv]
      -- Both maps are the ring-hom coercion of the action of `σ` on `B`.
      rfl)
  let eA : (A ⧸ Q.under A) ≃+* (A ⧸ (σ • Q).under A) :=
    (Ideal.quotientEquivAlgOfEq A (under_smul A Q σ).symm).toRingEquiv
  exact Algebra.IsSeparable.of_equiv_equiv
      (A₁ := A ⧸ Q.under A) (B₁ := B ⧸ Q)
      (A₂ := A ⧸ (σ • Q).under A) (B₂ := B ⧸ σ • Q) eA e.toRingEquiv (by
    ext x
    simpa [eA] using (e.commutes (Ideal.Quotient.mk (Q.under A) x)).symm)

end Ideal
