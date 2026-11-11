/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.HalfDiagram

/-!
# Convolution of half-diagram counts

The ballot recurrence for half-diagrams is symmetric in the possible changes of the number of
defects: adding a point changes it by one, upwards or downwards. Consequently a step can be
transferred from one factor of the convolution to the other. Iterating this transfer proves
`sum_halfCount_mul`: the sum of `halfCount n k * halfCount m k` over the possible common defect
numbers is `halfCount (n + m) 0`.

In particular, `sum_halfCount_sq` proves that the squares of the half-diagram counts on `n`
points sum to `catalan n`. This is the numerical identity underlying the decomposition of planar
endomorphism diagrams into pairs of half-diagrams with the same number of through strands.
The argument uses the branching recurrence, not a diagram-cutting equivalence.

## References

* B. W. Westbury, *The representation theory of the Temperley–Lieb algebras*, Math. Z. 219
  (1995), 539–565.
-/

public section

open Finset

namespace TauCeti

/-- Transferring one step between two truncated ballot paths leaves only the two boundary
terms. Keeping these terms makes the identity valid at every cutoff. -/
private theorem halfCount_transfer_boundary (n m N : ℕ) :
    (∑ k ∈ range (N + 1), halfCount (n + 1) k * halfCount m k) +
        halfCount n N * halfCount m (N + 1) =
      (∑ k ∈ range (N + 1), halfCount n k * halfCount (m + 1) k) +
        halfCount n (N + 1) * halfCount m N := by
  induction N with
  | zero => simp [halfCount_succ_zero, add_comm]
  | succ N ih =>
    simp only [sum_range_succ, halfCount_succ_succ] at ih ⊢
    nlinarith only [ih]

/-- Above both boundary sizes the boundary terms vanish, so a point can be moved from the
first half-diagram count to the second inside the convolution. -/
private theorem halfCount_transfer (n m N : ℕ) (hn : n ≤ N) (hm : m ≤ N) :
    (∑ k ∈ range (N + 1), halfCount (n + 1) k * halfCount m k) =
      ∑ k ∈ range (N + 1), halfCount n k * halfCount (m + 1) k := by
  have hn' : n < N + 1 := by omega
  have hm' : m < N + 1 := by omega
  simpa [halfCount_eq_zero_of_lt hn', halfCount_eq_zero_of_lt hm'] using
    halfCount_transfer_boundary n m N

/-- With a cutoff above the total boundary size, transfer every point to the second factor. -/
private theorem sum_halfCount_mul_of_add_le (n m N : ℕ) (h : n + m ≤ N) :
    (∑ k ∈ range (N + 1), halfCount n k * halfCount m k) = halfCount (n + m) 0 := by
  induction n generalizing m with
  | zero =>
    simp only [zero_add]
    rw [sum_eq_single 0]
    · simp
    · intro k _ hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      simp
    · simp
  | succ n ih =>
    rw [halfCount_transfer n m N (by omega) (by omega), ih (m + 1) (by omega)]
    congr 1; omega

/-- Terms above either boundary size vanish, so increasing the summation cutoff changes
nothing. -/
private theorem sum_halfCount_mul_stable (n m a b : ℕ) (ha : min n m < a) (hab : a ≤ b) :
    (∑ k ∈ range b, halfCount n k * halfCount m k) =
      ∑ k ∈ range a, halfCount n k * halfCount m k := by
  refine (sum_subset (range_mono hab) fun k _ hk => ?_).symm
  simp only [mem_range, not_lt] at hk
  have : n < k ∨ m < k := by omega
  rcases this with h | h <;> simp [halfCount_eq_zero_of_lt h]

/-- **The half-diagram convolution.** Summing the products of the numbers of half-diagrams on
`n` and `m` points with the same number of defects gives the number of planar matchings on
`n + m` points. The upper bound `min n m` includes every possible common defect number. -/
theorem sum_halfCount_mul (n m : ℕ) :
    (∑ k ∈ range (min n m + 1), halfCount n k * halfCount m k) = halfCount (n + m) 0 := by
  rw [← sum_halfCount_mul_stable n m (min n m + 1) (n + m + 1) (by omega) (by omega)]
  exact sum_halfCount_mul_of_add_le n m (n + m) le_rfl

/-- **The sum-of-squares identity.** The numbers of half-diagrams on `n` points, squared and
summed over all possible defect numbers, add up to the Catalan number `catalan n`. -/
theorem sum_halfCount_sq (n : ℕ) :
    (∑ k ∈ range (n + 1), halfCount n k ^ 2) = catalan n := by
  simpa only [min_self, pow_two, ← two_mul, halfCount_two_mul_zero] using sum_halfCount_mul n n

end TauCeti
