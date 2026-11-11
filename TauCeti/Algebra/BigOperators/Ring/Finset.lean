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

## Regrouping coordinates of products given by matrices

Let `M : ι₁ → ι₂ → ι₀ → A` be the matrix of a bilinear product on coordinate vectors over finite
types, so that the product of `x` and `y` has coordinates `∑ᵢ ∑ⱼ xᵢ yⱼ Mᵢⱼₖ`. Composing it with
matrices of linear maps on either input or on the output gives a vector whose coordinates regroup
as `∑ᵢ ∑ⱼ xᵢ yⱼ c(i, j)`, where `c(i, j)` is the corresponding composite matrix entry:

* `TauCeti.sum_mul_sum_sum_mul_mul`: a map `Ψ` on the output;
* `TauCeti.sum_sum_sum_mul_mul_mul`: a map `P` on the first input;
* `TauCeti.sum_sum_mul_sum_mul_mul`: a map `P` on the second input;
* `TauCeti.sum_sum_sum_mul_sum_mul`: maps `P` and `Q` on both inputs.

These are the coordinate computations behind Leibniz rules and comparison homotopies for products
given by matrices.
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

variable {A ι₁ ι₂ ι₀ κ₁ κ₂ : Type*} [CommSemiring A] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
  [Fintype κ₁] [Fintype κ₂]

/-- Applying a matrix `Ψ` after the product of a matrix `M`, in coordinates, regroups as
`∑ₖ (∑ᵢ ∑ⱼ xᵢ yⱼ Mᵢⱼₖ) Ψₖ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Mᵢⱼₖ Ψₖ`. -/
theorem sum_mul_sum_sum_mul_mul (x : ι₁ → A) (y : ι₂ → A) (M : ι₁ → ι₂ → ι₀ → A)
    (Ψ : ι₀ → A) :
    ∑ k, (∑ i, ∑ j, x i * y j * M i j k) * Ψ k = ∑ i, ∑ j, x i * y j * ∑ k, M i j k * Ψ k := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Applying a matrix `P` to the first input of the product of a matrix `M`, in coordinates,
regroups as `∑ₖ ∑ⱼ (∑ᵢ xᵢ Pᵢₖ) yⱼ Mₖⱼ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Pᵢₖ Mₖⱼ`. -/
theorem sum_sum_sum_mul_mul_mul (x : κ₁ → A) (y : ι₂ → A) (P : κ₁ → ι₁ → A)
    (M : ι₁ → ι₂ → A) :
    ∑ k, ∑ j, (∑ i, x i * P i k) * y j * M k j = ∑ i, ∑ j, x i * y j * ∑ k, P i k * M k j := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => by ring

/-- Applying a matrix `P` to the second input of the product of a matrix `M`, in coordinates,
regroups as `∑ᵢ ∑ⱼ (xᵢ ∑ₘ yₘ Pₘⱼ) Mᵢⱼ = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ₖ Pⱼₖ Mᵢₖ`. -/
theorem sum_sum_mul_sum_mul_mul (x : ι₁ → A) (y : κ₂ → A) (P : κ₂ → ι₂ → A)
    (M : ι₁ → ι₂ → A) :
    ∑ i, ∑ j, (x i * ∑ m, y m * P m j) * M i j = ∑ i, ∑ j, x i * y j * ∑ k, P j k * M i k := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- Applying matrices `P` and `Q` to the two inputs of the product of a matrix `M`, in
coordinates, regroups as
`∑ᵢ' ∑ⱼ' (∑ᵢ xᵢ Pᵢᵢ') (∑ⱼ yⱼ Qⱼⱼ') Mᵢ'ⱼ' = ∑ᵢ ∑ⱼ xᵢ yⱼ ∑ᵢ' ∑ⱼ' Pᵢᵢ' Qⱼⱼ' Mᵢ'ⱼ'`. -/
theorem sum_sum_sum_mul_sum_mul (x : κ₁ → A) (y : κ₂ → A) (P : κ₁ → ι₁ → A)
    (Q : κ₂ → ι₂ → A) (M : ι₁ → ι₂ → A) :
    ∑ i', ∑ j', (∑ i, x i * P i i') * (∑ j, y j * Q j j') * M i' j' =
      ∑ i, ∑ j, x i * y j * ∑ i', ∑ j', P i i' * Q j j' * M i' j' := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- Move the sums over the inputs `i ∈ κ₁` and `j ∈ κ₂` outside those over `i' ∈ ι₁`, `j' ∈ ι₂`.
  calc _ = ∑ i', ∑ j', ∑ i, ∑ j, x i * P i i' * (y j * Q j j') * M i' j' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ i', ∑ j', ∑ j, x i * P i i' * (y j * Q j j') * M i' j' :=
        (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ i', ∑ j', x i * P i i' * (y j * Q j j') * M i' j' :=
        Finset.sum_congr rfl fun _ _ =>
          (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Regroup

end TauCeti
