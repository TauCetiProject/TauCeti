/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Ring.Prod

/-!
# Products of rings

Over a ring with invertible `2`, the half-sum and half-difference of a pair
have sum and difference equal to that pair (`Prod.invOf_two_mul_add_sub`).

The projections `RingHom.fst` and `RingHom.snd`, viewed as non-unital ring homomorphisms, are
`NonUnitalRingHom.fst` and `NonUnitalRingHom.snd` (`RingHom.toNonUnitalRingHom_fst`,
`RingHom.toNonUnitalRingHom_snd`).

A ring endomorphism of `R × R` acting as the swap `(a, b) ↦ (b, a)` is an involution
(`RingHomInvPair.of_forall_eq_swap`).
-/

public section

namespace Prod

variable {R : Type*} [Ring R] [Invertible (2 : R)]

/-- The pair `(⅟2 (x + y), ⅟2 (x - y))` is sent back to `(x, y)` by `(a, b) ↦ (a + b, a - b)`. -/
theorem invOf_two_mul_add_sub (z : R × R) :
    (⅟(2 : R) * (z.1 + z.2) + ⅟(2 : R) * (z.1 - z.2),
      ⅟(2 : R) * (z.1 + z.2) - ⅟(2 : R) * (z.1 - z.2)) = z := by
  ext <;> simp [← mul_add, ← mul_sub, ← two_mul]

end Prod

namespace RingHom

variable (R S : Type*) [NonAssocSemiring R] [NonAssocSemiring S]

/-- The first projection of a product of rings, viewed as a non-unital ring homomorphism, is
`NonUnitalRingHom.fst`. -/
@[simp]
theorem toNonUnitalRingHom_fst : (fst R S).toNonUnitalRingHom = NonUnitalRingHom.fst R S :=
  -- Mathlib has no lemma evaluating the coercion of `RingHom.toNonUnitalRingHom f` (only the
  -- `RingEquiv` version); both maps are `Prod.fst` by definition.
  NonUnitalRingHom.ext fun _ ↦ rfl

/-- The second projection of a product of rings, viewed as a non-unital ring homomorphism, is
`NonUnitalRingHom.snd`. -/
@[simp]
theorem toNonUnitalRingHom_snd : (snd R S).toNonUnitalRingHom = NonUnitalRingHom.snd R S :=
  -- As for `RingHom.toNonUnitalRingHom_fst`, both maps are `Prod.snd` by definition.
  NonUnitalRingHom.ext fun _ ↦ rfl

end RingHom

/-- A ring endomorphism of `R × R` acting as the swap `(a, b) ↦ (b, a)` is an involution. -/
theorem RingHomInvPair.of_forall_eq_swap {R : Type*} [Semiring R] {σ : R × R →+* R × R}
    (hσ : ∀ x, σ x = x.swap) : RingHomInvPair σ σ :=
  ⟨RingHom.ext fun x ↦ by simp [hσ], RingHom.ext fun x ↦ by simp [hσ]⟩
