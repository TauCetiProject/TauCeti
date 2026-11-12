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
# Regrouping contracted bilinear sums

Let `x` and `y` be coordinates of two inputs and `c(i, j, k)` a three-index array of coefficients
in a commutative semiring. The bilinear combination `∑ᵢ ∑ⱼ xᵢ yⱼ c(i, j, k)` can be contracted
with a matrix in its output index `k`, or its inputs can first be transformed by matrices. In each
case the result is again a bilinear combination `∑ᵢ ∑ⱼ xᵢ yⱼ c'(i, j)`, whose coefficient `c'` is
the corresponding contraction of `c`. These are the regroupings that turn identities between
matrices of structure constants into identities between the products and maps they define.

## Main results

* `Finset.sum_mul_sum_sum_mul_mul`: contracting the output index.
* `Finset.sum_sum_sum_mul_mul_mul_left`: transforming the first input.
* `Finset.sum_sum_mul_sum_mul_mul_right`: transforming the second input.
* `Finset.sum_sum_sum_mul_sum_mul_mul`: transforming both inputs.
-/

public section

namespace Finset

variable {ι₁ ι₂ ι₀ κ₁ κ₂ R : Type*} [CommSemiring R] (s₁ : Finset ι₁) (s₂ : Finset ι₂)
  (x : ι₁ → R) (y : ι₂ → R)

/-- Contracting a bilinear combination with `c` in its output index:
`∑ₖ (∑ᵢ ∑ⱼ xᵢ yⱼ Qᵢⱼₖ) cₖ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Qᵢⱼₖ cₖ`. -/
theorem sum_mul_sum_sum_mul_mul (s₀ : Finset ι₀) (Q : ι₁ → ι₂ → ι₀ → R) (c : ι₀ → R) :
    ∑ k ∈ s₀, (∑ i ∈ s₁, ∑ j ∈ s₂, x i * y j * Q i j k) * c k =
      ∑ i ∈ s₁, ∑ j ∈ s₂, x i * y j * ∑ k ∈ s₀, Q i j k * c k := by
  simp only [sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_comm

/-- Transforming the first input of a bilinear combination by a matrix `D`:
`∑ₖ ∑ⱼ (∑ᵢ xᵢ Dᵢₖ) yⱼ Qₖⱼ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Dᵢₖ Qₖⱼ`. -/
theorem sum_sum_sum_mul_mul_mul_left (t₁ : Finset κ₁) (D : ι₁ → κ₁ → R) (Q : κ₁ → ι₂ → R) :
    ∑ k ∈ t₁, ∑ j ∈ s₂, (∑ i ∈ s₁, x i * D i k) * y j * Q k j =
      ∑ i ∈ s₁, ∑ j ∈ s₂, x i * y j * ∑ k ∈ t₁, D i k * Q k j := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine (sum_congr rfl fun _ _ ↦ sum_comm).trans ?_
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

/-- Transforming the second input of a bilinear combination by a matrix `D`:
`∑ᵢ ∑ₖ (xᵢ ∑ⱼ yⱼ Dⱼₖ) Qᵢₖ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Dⱼₖ Qᵢₖ`. -/
theorem sum_sum_mul_sum_mul_mul_right (t₂ : Finset κ₂) (D : ι₂ → κ₂ → R) (Q : ι₁ → κ₂ → R) :
    ∑ i ∈ s₁, ∑ k ∈ t₂, (x i * ∑ j ∈ s₂, y j * D j k) * Q i k =
      ∑ i ∈ s₁, ∑ j ∈ s₂, x i * y j * ∑ k ∈ t₂, D j k * Q i k := by
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun _ _ ↦ ?_
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

/-- Transforming both inputs of a bilinear combination by matrices `A` and `B`:
`∑ₖ ∑ₘ (∑ᵢ xᵢ Aᵢₖ) (∑ⱼ yⱼ Bⱼₘ) Qₖₘ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ ∑ₘ Aᵢₖ Bⱼₘ Qₖₘ`. -/
theorem sum_sum_sum_mul_sum_mul_mul (t₁ : Finset κ₁) (t₂ : Finset κ₂) (A : ι₁ → κ₁ → R)
    (B : ι₂ → κ₂ → R) (Q : κ₁ → κ₂ → R) :
    ∑ k ∈ t₁, ∑ m ∈ t₂, (∑ i ∈ s₁, x i * A i k) * (∑ j ∈ s₂, y j * B j m) * Q k m =
      ∑ i ∈ s₁, ∑ j ∈ s₂, x i * y j * ∑ k ∈ t₁, ∑ m ∈ t₂, A i k * B j m * Q k m := by
  refine (sum_sum_mul_sum_mul_mul_right t₁ s₂ (fun k ↦ ∑ i ∈ s₁, x i * A i k) y t₂ B Q).trans ?_
  refine (sum_sum_sum_mul_mul_mul_left s₁ s₂ x y t₁ A _).trans ?_
  simp only [mul_sum, mul_left_comm (A _ _), mul_assoc]

end Finset
