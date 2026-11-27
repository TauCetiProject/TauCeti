/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve

/-!
# Sieving a weighted finite family

A sieve on polynomial values may assign the same natural number to several inputs.
`BoundingSieve.ofFiniteFamily` puts the sum of their weights at that label, so that
divisibility and sifting count each input with its own weight. For instance, the seven
integers from 2 through 8 give just four distinct values of `n * (10 - n)`. With unit weights,
their divisibility sum at 1 is seven.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, §§11.2, 11.4 (weighted sieves).
* D. R. Heath-Brown, *Lectures on sieves*, §1, Example 2 (the Goldbach polynomial).
-/

public section

open Finset

namespace BoundingSieve

variable {ι : Type*} (s : BoundingSieve) (A : Finset ι) (f : ι → ℕ) (w : ι → ℝ)
  (hw : ∀ a ∈ A, 0 ≤ w a)

/-- Use the labels of a finite family as sieve support and sum weights over each fiber.
The sieving primes, multiplicative density and approximate mass are taken from `s`. -/
noncomputable def ofFiniteFamily : BoundingSieve :=
  { s with
    support := A.image f
    weights := fun n ↦ ∑ a ∈ A with f a = n, w a
    weights_nonneg := fun _ ↦ sum_nonneg fun a ha ↦ hw a (mem_filter.mp ha).1 }

/-- The support is the full image, including labels of weight zero. -/
@[simp] theorem ofFiniteFamily_support :
    (s.ofFiniteFamily A f w hw).support = A.image f := (rfl)

/-- The weight of a label is the total weight of its preimages in the family. -/
@[simp] theorem ofFiniteFamily_weights (n : ℕ) :
    (s.ofFiniteFamily A f w hw).weights n = ∑ a ∈ A with f a = n, w a := (rfl)

/-- A label outside the image has weight zero. -/
@[simp↓] theorem ofFiniteFamily_weights_eq_zero_of_notMem_image {n : ℕ} (hn : n ∉ A.image f) :
    (s.ofFiniteFamily A f w hw).weights n = 0 := by
  rw [ofFiniteFamily_weights, filter_false_of_mem (fun a ha he ↦ hn (mem_image.mpr ⟨a, ha, he⟩)),
    sum_empty]

/-- Relabelling the population preserves the product of sieving primes. -/
@[simp] theorem ofFiniteFamily_prodPrimes :
    (s.ofFiniteFamily A f w hw).prodPrimes = s.prodPrimes := (rfl)

/-- The finite family inherits the template's approximate mass. -/
@[simp] theorem ofFiniteFamily_totalMass :
    (s.ofFiniteFamily A f w hw).totalMass = s.totalMass := (rfl)

/-- The finite family inherits the entire density function. -/
@[simp] theorem ofFiniteFamily_nu :
    (s.ofFiniteFamily A f w hw).nu = s.nu := (rfl)

/-- The weight of the labels satisfying a predicate is the weight of the indices whose
labels satisfy it. -/
theorem sum_filter_ofFiniteFamily (p : ℕ → Prop) [DecidablePred p] :
    ∑ n ∈ (s.ofFiniteFamily A f w hw).support with p n, (s.ofFiniteFamily A f w hw).weights n =
      ∑ a ∈ A with p (f a), w a := by
  simp only [ofFiniteFamily_support, ofFiniteFamily_weights, sum_fiberwise_eq_sum_filter]
  exact sum_congr (filter_congr fun a ha ↦ by simp [mem_image_of_mem f ha]) fun _ _ ↦ rfl

/-- The divisibility sum at `d` counts all indices whose label is divisible by `d`. -/
@[simp↓] theorem multSum_ofFiniteFamily (d : ℕ) :
    (s.ofFiniteFamily A f w hw).multSum d = ∑ a ∈ A with d ∣ f a, w a := by
  simpa only [multSum, sum_filter] using s.sum_filter_ofFiniteFamily A f w hw (d ∣ ·)

/-- The sifted sum counts all indices whose label is coprime to the prime product. -/
@[simp] theorem siftedSum_ofFiniteFamily :
    (s.ofFiniteFamily A f w hw).siftedSum = ∑ a ∈ A with s.prodPrimes.Coprime (f a), w a := by
  simpa only [siftedSum, ofFiniteFamily_prodPrimes, sum_filter] using
    s.sum_filter_ofFiniteFamily A f w hw s.prodPrimes.Coprime

/-- The identity-labelled family on the original support preserves every divisibility sum. -/
theorem multSum_ofFiniteFamily_id (d : ℕ) :
    (s.ofFiniteFamily s.support id s.weights (fun a _ ↦ s.weights_nonneg a)).multSum d =
      s.multSum d := by
  rw [multSum_ofFiniteFamily, multSum, sum_filter]
  rfl

/-- The identity-labelled family on the original support preserves the sifted sum. -/
theorem siftedSum_ofFiniteFamily_id :
    (s.ofFiniteFamily s.support id s.weights (fun a _ ↦ s.weights_nonneg a)).siftedSum =
      s.siftedSum := by
  rw [siftedSum_ofFiniteFamily, siftedSum, sum_filter]
  rfl

end BoundingSieve
