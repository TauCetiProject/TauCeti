/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Nat.Choose.Sum

/-!
# The volume of a Hamming ball

For an alphabet of `q` letters and words of length `n`, the Hamming ball of radius `t` about a
word has `V_q(n, t) = ∑_{i ≤ t} (n choose i) (q - 1)^i` words: a word at distance exactly `i`
is chosen by the set of `i` coordinates where it differs, and at each of them by one of the
`q - 1` other letters.

## Main results

* `Nat.hammingBallVolume q n t`: the volume `V_q(n, t)`, with its values at radius zero, at length
  zero and for alphabets of at most one letter, and the step from radius `t` to radius `t + 1`.
* `Nat.hammingBallVolume_eq_pow_of_le`: for `q ≥ 1` and `t ≥ n` the volume is `q^n`.
* `TauCeti.card_filter_filter_ne_eq`: exactly `∏ j ∈ s, (|β j| - 1)` words of `∀ j, β j` differ
  from `x` exactly on `s`.
* `TauCeti.card_filter_hammingDist_eq`: exactly `(n choose i) (q - 1)^i` words are at distance
  `i` from `x`.
* `TauCeti.card_hammingBall`: exactly `V_q(n, t)` words are at distance at most `t` from `x`.

## References

* V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, proof of Theorem 1.7.2,
  equation (1.18), and Definition 3.3.2.
-/

public section

open Finset

namespace Nat

/-- The volume `V_q(n, t) = ∑_{i ≤ t} (n choose i) (q - 1)^i` of a Hamming ball of radius `t` in
the words of length `n` over an alphabet of `q` letters. -/
def hammingBallVolume (q n t : ℕ) : ℕ :=
  ∑ i ∈ range (t + 1), n.choose i * (q - 1) ^ i

/-- The volume of a Hamming ball is the sum, over the distances `i ≤ t`, of the number
`(n choose i) (q - 1)^i` of words at distance `i` from the centre. -/
theorem hammingBallVolume_def (q n t : ℕ) :
    hammingBallVolume q n t = ∑ i ∈ range (t + 1), n.choose i * (q - 1) ^ i := (rfl)

/-- The Hamming ball of radius `0` is the centre alone. -/
@[simp]
theorem hammingBallVolume_zero (q n : ℕ) : hammingBallVolume q n 0 = 1 := by
  simp [hammingBallVolume_def]

/-- Increasing the radius from `t` to `t + 1` adds the `(n choose (t + 1)) (q - 1)^(t + 1)`
words at distance exactly `t + 1`. -/
theorem hammingBallVolume_succ (q n t : ℕ) :
    hammingBallVolume q n (t + 1) =
      hammingBallVolume q n t + n.choose (t + 1) * (q - 1) ^ (t + 1) := by
  simp only [hammingBallVolume_def, sum_range_succ (n := t + 1)]

/-- There is one word of length `0`, so every Hamming ball in it has one word. -/
@[simp]
theorem hammingBallVolume_zero_length (q t : ℕ) : hammingBallVolume q 0 t = 1 := by
  simp [hammingBallVolume_def, sum_range_succ']

/-- Over the empty alphabet the volume is `1`, as `0 - 1 = 0` in `ℕ`. -/
@[simp]
theorem zero_hammingBallVolume (n t : ℕ) : hammingBallVolume 0 n t = 1 := by
  simp [hammingBallVolume_def, sum_range_succ']

/-- Over an alphabet of one letter there is one word, so every Hamming ball has one word. -/
@[simp]
theorem one_hammingBallVolume (n t : ℕ) : hammingBallVolume 1 n t = 1 := by
  simp [hammingBallVolume_def, sum_range_succ']

/-- A Hamming ball whose radius is at least the word length contains every word: over a nonempty
alphabet of `q` letters its volume is the number `q^n` of all words of length `n`. -/
theorem hammingBallVolume_eq_pow_of_le {q n t : ℕ} (hq : 1 ≤ q) (h : n ≤ t) :
    hammingBallVolume q n t = q ^ n := by
  have hsub : range (n + 1) ⊆ range (t + 1) := range_subset_range.2 (by omega)
  rw [hammingBallVolume_def, ← sum_subset hsub fun i _ hi ↦ by
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi), zero_mul]]
  conv_rhs => rw [← Nat.sub_add_cancel hq, add_pow]
  exact sum_congr rfl fun i _ ↦ by rw [one_pow, mul_one, mul_comm, Nat.cast_id]

end Nat

namespace TauCeti

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Exactly `∏ j ∈ s, (|β j| - 1)` words `y : ∀ j, β j` differ from `x` exactly on the
coordinates in `s`: at each `j ∈ s` the word `y` takes one of the `|β j| - 1` letters other than
`x j`, and off `s` it agrees with `x`. -/
theorem card_filter_filter_ne_eq {β : ι → Type*} [∀ j, Fintype (β j)]
    [∀ j, DecidableEq (β j)] (x : ∀ j, β j) (s : Finset ι) :
    #{y : ∀ j, β j | ({j | x j ≠ y j} : Finset ι) = s} = ∏ j ∈ s, (Fintype.card (β j) - 1) := by
  set T : ∀ j, Finset (β j) := fun j ↦ if j ∈ s then univ.erase (x j) else {x j}
  have hT : ({y : ∀ j, β j | ({j | x j ≠ y j} : Finset ι) = s} : Finset (∀ j, β j)) =
      Fintype.piFinset T := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Finset.ext_iff]
    refine forall_congr' fun j ↦ ?_
    by_cases hj : j ∈ s <;> simp [T, hj, eq_comm]
  rw [hT, Fintype.card_piFinset, ← prod_ite_mem_eq s]
  refine prod_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ s <;> simp [T, hj]

/-- Exactly `(n choose i) (q - 1)^i` words are at Hamming distance `i` from `x`. -/
theorem card_filter_hammingDist_eq (x : ι → α) (i : ℕ) :
    #{y : ι → α | hammingDist x y = i} = (Fintype.card ι).choose i * (Fintype.card α - 1) ^ i := by
  have hfilter : #{y : ι → α | hammingDist x y = i} =
      #{y : ι → α | ({j | x j ≠ y j} : Finset ι) ∈ powersetCard i univ} := by
    congr 1
    ext y
    simp [mem_powersetCard, hammingDist]
  rw [hfilter, ← sum_card_fiberwise_eq_card_filter, card_univ.symm, ← card_powersetCard]
  refine sum_const_nat fun s hs ↦ ?_
  rw [card_filter_filter_ne_eq, prod_const, (mem_powersetCard.1 hs).2]

/-- **The volume of a Hamming ball.** Exactly `V_q(n, t)` words are at Hamming distance at most
`t` from a word `x` of length `n` over an alphabet of `q` letters. -/
theorem card_hammingBall (x : ι → α) (t : ℕ) :
    #{y : ι → α | hammingDist x y ≤ t} =
      (Fintype.card α).hammingBallVolume (Fintype.card ι) t := by
  rw [Nat.hammingBallVolume_def, ← sum_congr rfl fun i _ ↦ card_filter_hammingDist_eq x i,
    sum_card_fiberwise_eq_card_filter]
  simp only [mem_range, Nat.lt_succ_iff]

/-! ### Checks -/

example : Nat.hammingBallVolume 2 7 1 = 8 := by decide
example : Nat.hammingBallVolume 2 23 3 = 2048 := by decide
example : Nat.hammingBallVolume 3 11 2 = 243 := by decide

/-- Radii beyond the length count every word: `V_3(2, 5) = 3^2`. -/
example : Nat.hammingBallVolume 3 2 5 = 9 := by decide

end TauCeti
