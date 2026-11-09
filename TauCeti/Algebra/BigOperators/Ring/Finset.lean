/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# Identities for finite sums in commutative rings

## Scaling weighted sums of natural numbers

In a commutative semiring, multiplying a weighted sum `∑ᵢ sᵢ cᵢ` of natural numbers `cᵢ` by a
natural number `d` gives the weighted sum `∑ᵢ sᵢ (cᵢ d)` of the products, computed in `ℕ`. This
turns inequalities for counts `cᵢ` weighted by a dimension `d`, such as the strong Morse
inequalities with coefficients in a `d`-dimensional space, into inequalities for the sequence
`cᵢ d` of natural numbers.

## Replacing the factors of a triple product by constants

`TauCeti.sum_sum_sum_mul_sub_eq` writes the difference between a triple sum
`∑ x, ∑ y, ∑ z, a x y * b x z * c y z` and the corresponding product of three constants as a sum
of three one-factor discrepancies.
-/

public section

namespace TauCeti

/-- Scaling a weighted sum of natural numbers `cᵢ` by a natural number `d` gives the same weighted
sum of the products `cᵢ d`: `d ∑ᵢ sᵢ cᵢ = ∑ᵢ sᵢ (cᵢ d)`. This turns the strong inequalities for
counts `cᵢ` weighted by the dimension `d` of a coefficient space into strong inequalities for the
sequence `cᵢ d`. -/
theorem natCast_mul_sum_mul_natCast {ι R : Type*} [CommSemiring R] (d : ℕ) (s : ι → R)
    (c : ι → ℕ) (t : Finset ι) :
    (d : R) * ∑ i ∈ t, s i * c i = ∑ i ∈ t, s i * ((c i * d : ℕ) : R) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

open Finset in
/-- Replacing the three factors of a triple product by constants one at a time: the difference of
`∑ a b c` and the product of the three constants is a sum of three one-factor discrepancies. -/
theorem sum_sum_sum_mul_sub_eq {α β γ R : Type*} [CommRing R] (a : α → β → R) (b : α → γ → R)
    (c : β → γ → R) (p q r : R) (s₀ : Finset α) (s₁ : Finset β) (s₂ : Finset γ) :
    ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, a x y * b x z * c y z -
      (#s₀ * #s₁ * #s₂ : R) * (p * q * r) =
      ∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p) +
        p * ∑ y ∈ s₁, ∑ x ∈ s₀, ∑ z ∈ s₂, 1 * c y z * (b x z - q) +
        p * q * ∑ _x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, 1 * 1 * (c y z - r) := by
  have e₁ : ∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p) =
      ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, b x z * c y z * (a x y - p) := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_comm
  have e₃ : (#s₀ * #s₁ * #s₂ : R) * (p * q * r) =
      ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, p * q * r := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  rw [e₁, sum_comm (s := s₁), e₃]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ ?_
  ring

end TauCeti
