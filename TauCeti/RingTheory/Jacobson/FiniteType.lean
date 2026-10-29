/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Maximal ideals under finite type algebras over Jacobson rings

Zariski's lemma over a Jacobson ring makes the residue field at a maximal ideal of a finite type
algebra finite over the base. Integrality then shows that maximal ideals contract to maximal ideals
along any intermediate algebra.

## Main results

* `Ideal.isMaximal_under_of_finiteType`: a maximal ideal of a finite type algebra over a Jacobson
  ring contracts to a maximal ideal in any intermediate algebra.
-/

public section

namespace TauCeti

/-- Let `A → B` be a homomorphism of algebras over a Jacobson ring `R`, with `B` finitely generated
over `R`. Then every maximal ideal of `B` contracts to a maximal ideal of `A`. -/
theorem _root_.Ideal.isMaximal_under_of_finiteType (R : Type*) {A B : Type*} [CommRing R]
    [IsJacobsonRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [Algebra.FiniteType R B] (q : Ideal B) [q.IsMaximal] :
    (q.under A).IsMaximal := by
  -- The field `B ⧸ q` is finite over `R` by Zariski's lemma, hence integral over `A`; so its zero
  -- ideal contracts to a maximal ideal of `A`, which is `q ∩ A`.
  let := Ideal.Quotient.field q
  have : Module.Finite R (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing R (B ⧸ q)
  have : Module.Finite A (B ⧸ q) := .of_restrictScalars_finite R A (B ⧸ q)
  have h : ((⊥ : Ideal (B ⧸ q)).under A).IsMaximal := Ideal.IsMaximal.under A ⊥
  have hker : (⊥ : Ideal (B ⧸ q)).under A = q.under A := by
    have hq : (⊥ : Ideal (B ⧸ q)).under B = q := by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot,
        Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    rw [← Ideal.under_under (B := B), hq]
  rwa [hker] at h

end TauCeti
