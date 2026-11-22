/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Order estimates for sums and products of finite sequences

A nonnegative finite sequence in which every term is at most half of the previous one sums to at
most twice its first term. In Roth's lemma this bounds the sum of the weights `rᵢ` by `2 r₀`.

The partial products of a sequence of terms at least `1`, and the partial sums of a nonnegative
sequence, are monotone. The partial products of a sequence bounded by `c` are bounded by powers of
`c`, and its partial sums by multiples of `c`.

A nonnegative monotone sequence of length `D * k` bounds the `D`-th power of the product of `k`
of its terms, the `j`-th of which is taken no later than position `D * j`. This converts bounds
for vectors selected from an ordered family, such as a family of successive minima, into a bound
by the product of the whole family. In the same way, a monotone sequence of terms at least `1`
bounds the `(n - i)`-th power of its `i`-th term, the length of the tail it starts, by the product
of the whole sequence.

## Main results

* `Fin.sum_le_two_mul_of_two_mul_succ_le`: if `0 ≤ rᵢ` and `2 rᵢ₊₁ ≤ rᵢ`, then
  `∑ᵢ rᵢ ≤ 2 r₀`.
* `Fin.monotone_partialProd`, `Fin.monotone_partialSum`: the partial products of entries at least
  `1` (the partial sums of nonnegative entries) are monotone.
* `Fin.partialProd_le_pow`, `Fin.partialSum_le_nsmul`: if `fᵢ ≤ c`, the partial product up to `i`
  is at most `c ^ i` (the partial sum is at most `i • c`).
* `Fin.prod_pow_le_prod_of_monotone`: if `c` is nonnegative and monotone on `Fin (D * k)` and
  `s j ≤ D * j`, then `(∏ⱼ c (s j)) ^ D ≤ ∏ᵢ cᵢ`.
* `Fin.pow_sub_le_prod_of_monotone`: if `c : Fin n → R` is monotone with `1 ≤ cⱼ`, then
  `cᵢ ^ (n - i) ≤ ∏ⱼ cⱼ`.
-/

public section

namespace Fin

/-- A nonnegative sequence whose terms at least halve at each step sums to at most twice its
first term. -/
theorem sum_le_two_mul_of_two_mul_succ_le {R : Type*} [NonAssocSemiring R] [Preorder R]
    [AddLeftMono R] {n : ℕ} {r : Fin (n + 1) → R} (hr : ∀ i, 0 ≤ r i)
    (h : ∀ i : Fin n, 2 * r i.succ ≤ r i.castSucc) : ∑ i, r i ≤ 2 * r 0 := by
  induction n with
  | zero =>
    rw [sum_univ_one, two_mul]
    exact le_add_of_nonneg_right (hr 0)
  | succ n ih =>
    have hs := ih (r := fun i ↦ r i.succ) (fun i ↦ hr _) fun i ↦ by
      rw [succ_castSucc]
      exact h i.succ
    have h0 := h 0
    rw [castSucc_zero] at h0
    rw [sum_univ_succ, two_mul]
    gcongr
    exact hs.trans h0

/-- Selecting `k` terms of a nonnegative monotone sequence of length `D * k`, the `j`-th at
position at most `D * j`, the product of the selected terms raised to the power `D` is at most the
product of the whole sequence: the `j`-th block of `D` consecutive terms bounds the `D`-th power of
the `j`-th selected term from above. -/
theorem prod_pow_le_prod_of_monotone {R : Type*} [CommMonoidWithZero R] [Preorder R]
    [PosMulMono R] {D k : ℕ} {c : Fin (D * k) → R} (hc0 : ∀ i, 0 ≤ c i)
    (hc : Monotone c) {s : Fin k → Fin (D * k)} (hs : ∀ j, (s j : ℕ) ≤ D * j) :
    (∏ j, c (s j)) ^ D ≤ ∏ i, c i := by
  obtain rfl | hD := D.eq_zero_or_pos
  · -- `Fin (0 * k)` is empty, so both sides are `1`.
    have : IsEmpty (Fin (0 * k)) := ⟨fun i ↦ by simpa using i.isLt⟩
    simp
  let e : Fin k × Fin D ≃ Fin (D * k) := finProdFinEquiv.trans (finCongr (Nat.mul_comm k D))
  have he (p : Fin k × Fin D) : (e p : ℕ) = p.2 + D * p.1 := by simp [e]
  have hD' : (Finset.univ : Finset (Fin D)).Nonempty := ⟨⟨0, hD⟩, Finset.mem_univ _⟩
  rw [← e.prod_comp, Fintype.prod_prod_type, ← Finset.prod_pow]
  refine Finset.prod_le_prod_of_nonneg_of_le (fun j _ ↦ ?_) fun j _ ↦ ?_
  · rw [← Fin.prod_const]
    exact Finset.prod_nonneg_of_nonempty hD' fun _ _ ↦ hc0 _
  rw [← Fin.prod_const]
  refine Finset.prod_le_prod_of_nonneg_of_le (fun _ _ ↦ hc0 _) fun t _ ↦ hc ?_
  rw [Fin.le_iff_val_le_val, he]
  exact (hs j).trans (Nat.le_add_left _ _)

/-- The partial products of entries at least `1` are monotone. -/
@[to_additive /-- The partial sums of nonnegative entries are monotone. -/]
theorem monotone_partialProd {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] {n : ℕ}
    {f : Fin n → M} (hf : ∀ i, 1 ≤ f i) : Monotone (partialProd f) :=
  monotone_iff_le_succ.2 fun i ↦ by
    rw [partialProd_succ]
    exact le_mul_of_one_le_right' (hf i)

/-- If every factor of a tuple is at most `c`, its partial product up to `i` is at most
`c ^ i`. -/
@[to_additive /-- If every term of a tuple is at most `c`, its partial sum up to `i` is at most
`i • c`. -/]
theorem partialProd_le_pow {M : Type*} [Monoid M] [Preorder M] [MulLeftMono M] [MulRightMono M]
    {n : ℕ} {f : Fin n → M} {c : M} (h : ∀ i, f i ≤ c) (i : Fin (n + 1)) :
    partialProd f i ≤ c ^ (i : ℕ) := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialProd_succ, val_succ, pow_succ]
    exact mul_le_mul' (by simpa using ih) (h i)

/-- In a monotone sequence `c : Fin n → R` of terms at least `1`, the `i`-th term raised to the
power `n - i` is at most the product of the whole sequence: the `n - i` terms from position `i`
on are at least `c i`, and the others are at least `1`. Both hypotheses are needed: `(1 / 2, 2)`
has last term `2` above its product `1`, and `(4, 1)` has `4 ^ 2` above its product `4`. -/
theorem pow_sub_le_prod_of_monotone {R : Type*} [CommMonoidWithZero R] [Preorder R]
    [ZeroLEOneClass R] [PosMulMono R] {n : ℕ} {c : Fin n → R} (hc1 : ∀ i, 1 ≤ c i)
    (hc : Monotone c) (i : Fin n) : c i ^ (n - i) ≤ ∏ j, c j := by
  have hc0 (j : Fin n) : 0 ≤ c j := zero_le_one.trans (hc1 j)
  calc c i ^ (n - i) = ∏ _j ∈ Finset.Ici i, c i := by rw [Finset.prod_const, card_Ici]
    _ ≤ ∏ j ∈ Finset.Ici i, c j :=
        Finset.prod_le_prod₀ (fun _ _ ↦ hc0 i) fun _ hj ↦ hc (Finset.mem_Ici.1 hj)
    _ ≤ ∏ j, c j :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _) (fun j _ ↦ hc0 j)
          fun j _ _ ↦ hc1 j

end Fin
