/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.GaussSum

/-!
# Factorization of Gauss sums

`MulChar.gaussSum_eq_mul_of_equiv` factors Mathlib's `gaussSum` through a bijection with a
product whenever the two characters split along its coordinates. This gives the finite-sum step
in the Chinese remainder formula for Gauss sums.
-/

public section

namespace MulChar

variable {A B C R : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing R]
  [Fintype A] [Fintype B] [Fintype C]

/-- If the multiplicative and additive characters split along a bijection with a product,
their Gauss sum is the product of the two coordinate Gauss sums. -/
theorem gaussSum_eq_mul_of_equiv (χ : MulChar A R) (ψ : AddChar A R) (e : A ≃ B × C)
    {χ₁ : MulChar B R} {χ₂ : MulChar C R} {ψ₁ : AddChar B R} {ψ₂ : AddChar C R}
    (hχ : ∀ x, χ x = χ₁ (e x).1 * χ₂ (e x).2)
    (hψ : ∀ x, ψ x = ψ₁ (e x).1 * ψ₂ (e x).2) :
    gaussSum χ ψ = gaussSum χ₁ ψ₁ * gaussSum χ₂ ψ₂ := by
  calc
    gaussSum χ ψ = ∑ x : B × C, (χ₁ x.1 * ψ₁ x.1) * (χ₂ x.2 * ψ₂ x.2) := by
      simp only [gaussSum]
      refine Fintype.sum_equiv e _ _ fun x ↦ ?_
      rw [hχ x, hψ x, mul_mul_mul_comm]
    _ = gaussSum χ₁ ψ₁ * gaussSum χ₂ ψ₂ := by
      simp only [Fintype.sum_prod_type, gaussSum, Fintype.sum_mul_sum]

end MulChar
