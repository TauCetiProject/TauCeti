/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Nonunital algebra homomorphisms

* `NonUnitalRingHom.toIntNonUnitalAlgHom` regards a homomorphism of nonunital,
  nonassociative rings as a homomorphism of nonunital `ℤ`-algebras, using their canonical
  integer scalar actions.
* `NonUnitalAlgHom.eq_zero_or_map_one`: a nonunital algebra homomorphism from a unital algebra
  into a semiring without zero divisors, such as a multiplicative linear functional, is either
  `0` or unital.
-/

public section

namespace NonUnitalRingHom

variable {R A : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing A]

/-- Reinterpret a nonunital ring homomorphism as a nonunital `ℤ`-algebra homomorphism. -/
def toIntNonUnitalAlgHom (f : R →ₙ+* A) : R →ₙₐ[ℤ] A :=
  { f with map_smul' := fun z x ↦ f.map_zsmul z x }

@[simp]
theorem toIntNonUnitalAlgHom_apply (f : R →ₙ+* A) (x : R) :
    f.toIntNonUnitalAlgHom x = f x := by
  rfl

end NonUnitalRingHom

namespace NonUnitalAlgHom

variable {R A B : Type*} [Monoid R] [Semiring A] [Semiring B] [IsLeftCancelMulZero B]
  [DistribMulAction R A] [DistribMulAction R B]

/-- A nonunital algebra homomorphism from a unital algebra into a semiring without zero divisors
is either `0` or unital: `ψ 1` is an idempotent. -/
theorem eq_zero_or_map_one (ψ : A →ₙₐ[R] B) : ψ = 0 ∨ ψ 1 = 1 := by
  have hidem : IsIdempotentElem (ψ 1) := by rw [IsIdempotentElem, ← map_mul, mul_one]
  refine (IsIdempotentElem.iff_eq_zero_or_one.mp hidem).imp_left fun h0 ↦ ?_
  ext a
  rw [← mul_one a, map_mul, h0, mul_zero, zero_apply]

end NonUnitalAlgHom
