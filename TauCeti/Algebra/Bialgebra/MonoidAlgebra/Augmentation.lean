/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# The monoid-algebra counit is the coefficient sum

This identifies the bialgebra counit with the augmentation used in the ideal-theoretic
exactness of monoid algebras, and the bialgebra map induced by a monoid homomorphism with the
ring map `MonoidAlgebra.mapDomainRingHom` appearing there, deducing surjectivity of
`MonoidAlgebra.mapDomainBialgHom` along a surjective monoid homomorphism
(`MonoidAlgebra.mapDomainBialgHom_surjective`).
-/

public section

namespace TauCeti.MonoidAlgebra

/-- The counit of a monoid algebra over its coefficient semiring is its coefficient-sum
augmentation. -/
@[simp]
theorem counitAlgHom_toRingHom (R M : Type*) [CommSemiring R] [Monoid M] :
    (Bialgebra.counitAlgHom R (MonoidAlgebra R M) : MonoidAlgebra R M →+* R) =
      MonoidAlgebra.augmentation R M := by
  apply MonoidAlgebra.ringHom_ext <;> intro <;> simp

/-- The bialgebra map of monoid algebras induced by a monoid homomorphism is, as a ring
homomorphism, `MonoidAlgebra.mapDomainRingHom`. -/
@[simp]
theorem mapDomainBialgHom_toRingHom (R : Type*) {M N : Type*} [CommSemiring R] [Monoid M]
    [Monoid N] (f : M →* N) :
    ((MonoidAlgebra.mapDomainBialgHom R f : MonoidAlgebra R M →ₐ[R] MonoidAlgebra R N) :
        MonoidAlgebra R M →+* MonoidAlgebra R N) =
      MonoidAlgebra.mapDomainRingHom R f :=
  rfl

/-- Pushing coefficients of a monoid algebra forward along a surjective monoid homomorphism induces
a surjective bialgebra homomorphism. -/
theorem _root_.MonoidAlgebra.mapDomainBialgHom_surjective (R : Type*) {M N : Type*}
    [CommSemiring R] [Monoid M] [Monoid N] {f : M →* N} (hf : Function.Surjective f) :
    Function.Surjective (MonoidAlgebra.mapDomainBialgHom R f) := by
  rw [← BialgHom.coe_toAlgHom, ← RingHom.coe_coe, mapDomainBialgHom_toRingHom]
  exact fun y ↦ (MonoidAlgebra.mapDomain_surjective hf y).imp fun x hx ↦
    (MonoidAlgebra.mapDomainRingHom_apply R f x).trans hx

end TauCeti.MonoidAlgebra
