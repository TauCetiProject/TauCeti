/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Algebra automorphisms as ring automorphisms; cancelling factors

The underlying ring automorphism of an algebra automorphism turns the identity and product of
`A ≃ₐ[R] A` into the identity and composition of ring equivalences
(`AlgEquiv.toRingEquiv_one`, `AlgEquiv.toRingEquiv_mul`). For inverses, Mathlib's
`AlgEquiv.aut_inv` and `AlgEquiv.symm_toRingEquiv` already apply. An algebra with no nontrivial
automorphisms admits at most one isomorphism from any algebra
(`AlgEquiv.subsingleton_of_subsingleton_aut`).

The remaining lemmas relate the action of an algebra automorphism on one factor to its action
on a product or quotient with a fixed cancellable factor. An automorphism negating a nonzero
element is nontrivial when multiplication by `2` is injective. An automorphism multiplying an
element by a fixed factor `c` multiplies it by `cᵏ` under its `k`-th power.
-/

public section

namespace AlgEquiv

variable {R A : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A]

/-- The identity algebra automorphism is the identity ring automorphism. -/
@[simp]
theorem toRingEquiv_one : ((1 : A ≃ₐ[R] A) : A ≃+* A) = RingEquiv.refl A :=
  (rfl)

/-- A product of algebra automorphisms is the composite of the ring automorphisms, the right
factor applied first. -/
@[simp]
theorem toRingEquiv_mul (σ τ : A ≃ₐ[R] A) :
    ((σ * τ : A ≃ₐ[R] A) : A ≃+* A) = (τ : A ≃+* A).trans σ :=
  (rfl)

/-- If an algebra `B` has no nontrivial automorphisms, then there is at most one isomorphism from
any algebra onto `B`. -/
theorem subsingleton_of_subsingleton_aut {B : Type*} [Semiring B] [Algebra R B]
    [Subsingleton (B ≃ₐ[R] B)] : Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun e₁ e₂ ↦ AlgEquiv.ext fun x ↦ by
    simpa using congr($(Subsingleton.elim (e₁.symm.trans e₂) AlgEquiv.refl) (e₁ x)).symm⟩

/-- An automorphism fixing a left-regular factor `x` fixes `x * y` exactly when it fixes `y`. -/
theorem apply_mul_eq_mul_iff (σ : A ≃ₐ[R] A) {x y : A} (hx : IsLeftRegular x)
    (hσx : σ x = x) : σ (x * y) = x * y ↔ σ y = y := by
  rw [map_mul, hσx, hx.eq_iff]

/-- If an automorphism `σ` multiplies `u` by a factor `c` that it fixes, then `σᵏ` multiplies `u`
by `cᵏ`. -/
theorem pow_apply_eq_mul_pow (σ : A ≃ₐ[R] A) {u c : A} (hc : σ c = c) (h : σ u = u * c)
    (k : ℕ) : (σ ^ k) u = u * c ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ', mul_apply, ih, map_mul, map_pow, h, hc, mul_assoc]

end Semiring

/-- An automorphism that negates a nonzero element is not the identity when multiplication by
`2` is injective. -/
theorem ne_one_of_apply_eq_neg [Ring A] [Algebra R A] (σ : A ≃ₐ[R] A)
    (h2 : IsLeftRegular (2 : A)) {x : A} (hx : x ≠ 0) (h : σ x = -x) : σ ≠ 1 := by
  rintro rfl
  exact hx <| h2 <| by simpa [two_mul, eq_neg_iff_add_eq_zero] using h

/-- An automorphism fixing the nonzero element `e` negates `x / e` exactly when it negates `x`. -/
theorem apply_div_eq_neg_iff [DivisionRing A] [Algebra R A] (σ : A ≃ₐ[R] A) {x e : A}
    (he : e ≠ 0) (hσe : σ e = e) : σ (x / e) = -(x / e) ↔ σ x = -x := by
  rw [map_div₀, hσe, ← neg_div, div_left_inj' he]

end AlgEquiv
