/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Regular.SMul

/-!
# Linearized Jordan identity

The four-variable Jordan identity follows from Mathlib's operator linearization after
cancelling `2`. It requires only absence of `2`-torsion, and supplies the common algebraic
identity used for Peirce products and inner derivations.
-/

public section

namespace TauCeti.Jordan

/-- Invertibility of `2` in the scalar ring makes doubling injective on the module. -/
theorem isSMulRegular_two (R J : Type*) [CommRing R] [AddCommGroup J] [Module R J]
    [Invertible (2 : R)] : IsSMulRegular J (2 : ℕ) := by
  intro x y h
  apply (isUnit_of_invertible (2 : R)).isSMulRegular J
  simpa only [← Nat.cast_smul_eq_nsmul R, Nat.cast_ofNat] using h

/-- The evaluated four-variable linearized Jordan identity, with no `2`-torsion. -/
theorem mul_mul_mul_sub_add_add_eq_zero {J : Type*} [NonUnitalNonAssocCommRing J]
    [IsCommJordan J] (h2 : IsSMulRegular J (2 : ℕ)) (a b c d : J) :
    a * (b * c * d) - b * c * (a * d) + (b * (c * a * d) - c * a * (b * d)) +
      (c * (a * b * d) - a * b * (c * d)) = 0 := by
  apply h2
  have h := DFunLike.congr_fun (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c) d
  simp only [Ring.lie_def] at h
  -- Evaluation of AddMonoid.End respects its pointwise operations and composition by definition.
  exact h.trans (smul_zero _).symm

/-- Left multiplication by an element in the `1`- or `0`-space commutes with an idempotent. -/
theorem mul_left_comm_of_mul_eq_self_or_zero {J : Type*} [NonUnitalNonAssocCommRing J]
    [IsCommJordan J] (h2 : IsSMulRegular J (2 : ℕ)) {c x : J} (hc : c * c = c)
    (hx : c * x = x ∨ c * x = 0) (w : J) : c * (x * w) = x * (c * w) := by
  have h := mul_mul_mul_sub_add_add_eq_zero h2 c c x w
  rcases hx with hx | hx
  · simp only [hc, mul_comm x c, hx] at h
    apply sub_eq_zero.mp
    convert h using 1; abel
  · simpa only [hc, mul_comm x c, hx, zero_mul, mul_zero, sub_self, zero_add,
      sub_eq_zero, eq_comm] using h

/-- The `1`- and `0`-eigenspaces of multiplication by an idempotent annihilate one another. -/
theorem mul_eq_zero_of_mul_eq_self_of_mul_eq_zero {J : Type*} [NonUnitalNonAssocCommRing J]
    [IsCommJordan J] (h2 : IsSMulRegular J (2 : ℕ)) {c x y : J} (hc : c * c = c)
    (hx : c * x = x) (hy : c * y = 0) : x * y = 0 := by
  have h₀ : c * (x * y) = 0 := by
    rw [mul_left_comm_of_mul_eq_self_or_zero h2 hc (Or.inl hx), hy, mul_zero]
  have h₁ : c * (x * y) = x * y := by
    rw [mul_comm x y, mul_left_comm_of_mul_eq_self_or_zero h2 hc (Or.inr hy), hx, mul_comm y x]
  exact h₁.symm.trans h₀

/-- The multiplication operators of `1`- and `0`-eigenvectors at an idempotent commute. -/
theorem mul_left_comm_of_mul_eq_self_of_mul_eq_zero {J : Type*} [NonUnitalNonAssocCommRing J]
    [IsCommJordan J] (h2 : IsSMulRegular J (2 : ℕ)) {c x y : J} (hc : c * c = c)
    (hx : c * x = x) (hy : c * y = 0) (w : J) : x * (y * w) = y * (x * w) := by
  have h := mul_mul_mul_sub_add_add_eq_zero h2 x y c w
  simp only [mul_eq_zero_of_mul_eq_self_of_mul_eq_zero h2 hc hx hy, mul_comm y c, hx, hy,
    zero_mul, mul_zero, sub_self, zero_add, add_zero] at h
  exact (sub_eq_zero.mp h).symm

end TauCeti.Jordan
