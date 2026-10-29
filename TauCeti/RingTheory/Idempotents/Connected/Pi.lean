/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.LinearAlgebra.StdBasis

/-!
# Maps from function algebras to connected rings

An algebra map from a finite power of the base semiring into a commutative ring with connected
prime spectrum factors through any augmentation of that ring to the base. The characteristic
functions have idempotent images, so each image is zero or one and is fixed by the augmentation
followed by the algebra map. Extensionality on the standard basis gives the factorization.

This applies to the function algebras of finite constant groups: compatibility with the counit
then forces a morphism from a connected affine group to be trivial.
-/

public section

namespace AlgHom

/-- An algebra map from a finite function algebra to a ring with connected prime spectrum
factors through any augmentation to the base semiring. -/
theorem eq_algebraMap_comp_of_connected {R A ι : Type*} [CommSemiring R] [CommRing A]
    [Algebra R A] [_root_.Finite ι] [ConnectedSpace (PrimeSpectrum A)]
    (f : (ι → R) →ₐ[R] A) (q : A →ₐ[R] R) :
    f = (Algebra.ofId R A).comp (q.comp f) := by
  classical
  apply AlgHom.toLinearMap_injective
  apply (Pi.basisFun R ι).ext
  intro i
  simp only [Pi.basisFun_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply]
  have hidempotent : IsIdempotentElem (f (Pi.single i 1)) := by
    apply IsIdempotentElem.map
    simp [IsIdempotentElem, ← Pi.single_mul]
  rcases TauCeti.eq_zero_or_eq_one_of_isIdempotentElem hidempotent with hzero | hone
  · simp [hzero]
  · simp [hone]

end AlgHom
