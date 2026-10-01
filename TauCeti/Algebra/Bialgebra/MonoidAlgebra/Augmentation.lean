/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Exactness
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# The monoid-algebra counit is the coefficient sum

This identifies the bialgebra counit with the augmentation used in the ideal-theoretic
exactness of monoid algebras, and the bialgebra map induced by a monoid homomorphism with the
ring map `MonoidAlgebra.mapDomainRingHom` appearing there.
-/

public section

namespace TauCeti.MonoidAlgebra

/-- The counit of a monoid algebra over its coefficient ring is its coefficient-sum
augmentation. -/
@[simp]
theorem counitAlgHom_toRingHom (R M : Type*) [CommRing R] [Monoid M] :
    (Bialgebra.counitAlgHom R (MonoidAlgebra R M) : MonoidAlgebra R M →+* R) =
      augmentation R M := by
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

end TauCeti.MonoidAlgebra
