/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Opposite

/-!
# Transporting involutions along ring and algebra equivalences

Transporting `star` on `A` against `star` on `M` along `φ` yields `X ↦ φ (star (φ.symm (star X)))`
(`RingEquiv.starConjAlgEquiv`).
-/

public section

namespace RingEquiv

/-- Transporting `star` on `A` against `star` on `M` along a ring isomorphism `φ : A ≃+* M`
produces an `F`-algebra automorphism `X ↦ φ (star (φ.symm (star X)))` of `M`, once scalar
compatibility holds. -/
def starConjAlgEquiv (F : Type*) {A M : Type*} [CommSemiring F] [Semiring A] [StarRing A]
    [Semiring M] [Algebra F M] [StarRing M] (φ : A ≃+* M)
    (hcomm : ∀ z : F, φ (star (φ.symm (star (algebraMap F M z)))) = algebraMap F M z) :
    M ≃ₐ[F] M :=
  AlgEquiv.ofRingEquiv
    (f := ((starRingEquiv (R := M)).trans φ.symm.op).trans ((starRingEquiv (R := A)).symm.trans φ))
    hcomm

@[simp] theorem starConjAlgEquiv_apply (F : Type*) {A M : Type*} [CommSemiring F] [Semiring A]
    [StarRing A] [Semiring M] [Algebra F M] [StarRing M] (φ : A ≃+* M)
    (hcomm : ∀ z : F, φ (star (φ.symm (star (algebraMap F M z)))) = algebraMap F M z) (X : M) :
    φ.starConjAlgEquiv F hcomm X = φ (star (φ.symm (star X))) := (rfl)

end RingEquiv
