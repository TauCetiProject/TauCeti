/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Cancelling factors in algebra automorphisms

These lemmas recover the action of an algebra automorphism on one factor from its action on a
product or quotient and a fixed cancellable factor. An automorphism negating a nonzero element
is nontrivial when multiplication by `2` is injective.
-/

public section

namespace AlgEquiv

/-- Cancel a fixed left-regular factor to show that an automorphism fixes the other factor. -/
theorem apply_eq_self_of_apply_mul_eq_mul {F L : Type*} [CommSemiring F] [Semiring L]
    [Algebra F L] (σ : L ≃ₐ[F] L) {x y : L} (hx : IsLeftRegular x)
    (hσx : σ x = x) (h : σ (x * y) = x * y) : σ y = y := by
  rw [map_mul, hσx] at h
  exact hx h

/-- An automorphism that negates a nonzero element is not the identity when multiplication by
`2` is injective. -/
theorem ne_one_of_apply_eq_neg {F L : Type*} [CommSemiring F] [Ring L]
    [Algebra F L] (σ : L ≃ₐ[F] L) (h2 : IsLeftRegular (2 : L)) {x : L} (hx : x ≠ 0)
    (h : σ x = -x) : σ ≠ 1 := by
  rintro rfl
  exact hx (h2 (by simpa only [two_mul, mul_zero, AlgEquiv.one_apply] using
    eq_neg_iff_add_eq_zero.mp h))

/-- An automorphism negating `x / e` negates `x` when it fixes the nonzero element `e`. -/
theorem apply_eq_neg_of_apply_div_eq_neg {F L : Type*} [CommSemiring F] [DivisionRing L]
    [Algebra F L] (σ : L ≃ₐ[F] L) {x e : L} (he : e ≠ 0)
    (hσe : σ e = e) (h : σ (x / e) = -(x / e)) : σ x = -x := by
  rw [map_div₀, hσe, div_eq_iff he] at h
  rw [h, neg_mul, div_mul_cancel₀ _ he]

end AlgEquiv
