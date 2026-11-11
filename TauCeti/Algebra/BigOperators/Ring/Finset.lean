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
`∑ x, ∑ y, ∑ z, a x y * b x z * c y z` and the sum of the constant product of the three constants
over all triples, `(#s₀ * #s₁ * #s₂) * (p * q * r)`, as a sum of three one-factor discrepancies.

## Regrouping coordinates of a bilinear operation

For a bilinear operation with structure constants `Mᵢⱼₖ`, composing with a matrix on its output
or on one of its inputs regroups, in coordinates `xᵢ`, `yⱼ`, as a double sum `∑ᵢ ∑ⱼ xᵢ yⱼ c(i, j)`
whose coefficients `c(i, j)` are the composite structure constants
(`TauCeti.sum_sum_sum_mul_mul_eq`, `TauCeti.sum_sum_sum_mul_mul_eq_left`,
`TauCeti.sum_sum_sum_mul_mul_eq_right`).
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
`∑ a b c` and the triple sum `(#s₀ * #s₁ * #s₂) * (p * q * r)` of the constant product is a sum of
three one-factor discrepancies. -/
theorem sum_sum_sum_mul_sub_eq {α β γ R : Type*} [CommRing R] (a : α → β → R) (b : α → γ → R)
    (c : β → γ → R) (p q r : R) (s₀ : Finset α) (s₁ : Finset β) (s₂ : Finset γ) :
    ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, a x y * b x z * c y z -
      (#s₀ * #s₁ * #s₂ : R) * (p * q * r) =
      ∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p) +
        p * ∑ y ∈ s₁, ∑ x ∈ s₀, ∑ z ∈ s₂, c y z * (b x z - q) +
        p * q * (#s₀ * ∑ y ∈ s₁, ∑ z ∈ s₂, (c y z - r)) := by
  have e₁ : ∑ z ∈ s₂, ∑ x ∈ s₀, ∑ y ∈ s₁, b x z * c y z * (a x y - p) =
      ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, b x z * c y z * (a x y - p) := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_comm
  have e₃ : (#s₀ * #s₁ * #s₂ : R) * (p * q * r) =
      ∑ x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, p * q * r := by
    simp only [sum_const, nsmul_eq_mul]
    ring
  have e₄ : (#s₀ : R) * ∑ y ∈ s₁, ∑ z ∈ s₂, (c y z - r) =
      ∑ _x ∈ s₀, ∑ y ∈ s₁, ∑ z ∈ s₂, (c y z - r) := by
    rw [sum_const, nsmul_eq_mul]
  rw [e₁, sum_comm (s := s₁), e₃, e₄]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ ?_
  ring

section Regroup

open Finset

variable {ι κ ν R : Type*} [CommSemiring R] {s : Finset ι} {t : Finset κ} {u : Finset ν}

/-- Applying `Ψ` to the output of the bilinear operation with structure constants `M` regroups in
coordinates as `∑ₖ (∑ᵢ ∑ⱼ xᵢ yⱼ Mᵢⱼₖ) Ψₖ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Mᵢⱼₖ Ψₖ`. -/
theorem sum_sum_sum_mul_mul_eq (x : ι → R) (y : κ → R) (M : ι → κ → ν → R) (Ψ : ν → R) :
    ∑ k ∈ u, (∑ i ∈ s, ∑ j ∈ t, x i * y j * M i j k) * Ψ k =
      ∑ i ∈ s, ∑ j ∈ t, x i * y j * ∑ k ∈ u, M i j k * Ψ k := by
  simp only [sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_comm

/-- Applying the matrix `D` to the first input of the bilinear operation with structure constants
`M` regroups in coordinates as `∑ₖ ∑ⱼ (∑ᵢ xᵢ Dᵢₖ) yⱼ Mₖⱼ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Dᵢₖ Mₖⱼ`. -/
theorem sum_sum_sum_mul_mul_eq_left (x : ι → R) (y : κ → R) (D : ι → ν → R) (M : ν → κ → R) :
    ∑ k ∈ u, ∑ j ∈ t, (∑ i ∈ s, x i * D i k) * y j * M k j =
      ∑ i ∈ s, ∑ j ∈ t, x i * y j * ∑ k ∈ u, D i k * M k j := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine (sum_congr rfl fun j _ => sum_comm).trans ?_
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- Applying the matrix `D` to the second input of the bilinear operation with structure constants
`M` regroups in coordinates as `∑ᵢ ∑ₖ xᵢ (∑ⱼ yⱼ Dⱼₖ) Mᵢₖ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Dⱼₖ Mᵢₖ`. -/
theorem sum_sum_sum_mul_mul_eq_right (x : ι → R) (y : κ → R) (D : κ → ν → R) (M : ι → ν → R) :
    ∑ i ∈ s, ∑ k ∈ u, x i * (∑ j ∈ t, y j * D j k) * M i k =
      ∑ i ∈ s, ∑ j ∈ t, x i * y j * ∑ k ∈ u, D j k * M i k := by
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

end Regroup

end TauCeti
