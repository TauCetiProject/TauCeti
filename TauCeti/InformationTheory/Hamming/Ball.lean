/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Choose.Sum

/-!
# The volume of a Hamming ball

For an alphabet of `q` letters and words of length `n`, the Hamming ball of radius `t` about a
word has `V_q(n, t) = ∑_{i ≤ t} (n choose i) (q - 1)^i` words: a word at distance exactly `i`
is chosen by the set of `i` coordinates where it differs, and at each of them by one of the
`q - 1` other letters.

## Main results

* `TauCeti.hammingBallVolume q n t`: the volume `V_q(n, t)`.
* `TauCeti.card_filter_ne_eq`: exactly `(q - 1)^#s` words differ from `x` exactly on `s`.
* `TauCeti.card_filter_hammingDist_eq`: exactly `(n choose i) (q - 1)^i` words are at distance
  `i` from `x`.
* `TauCeti.card_hammingBall`: exactly `V_q(n, t)` words are at distance at most `t` from `x`.
* `TauCeti.hammingBallVolume_of_le`: for `q ≥ 1` and `t ≥ n` the volume is `q^n`.

## References

* V. Guruswami, A. Rudra and M. Sudan, *Essential Coding Theory*, proof of Theorem 1.7.2,
  equation (1.18), and Definition 3.3.2.
-/

public section

open Finset

namespace TauCeti

/-- The volume `V_q(n, t) = ∑_{i ≤ t} (n choose i) (q - 1)^i` of a Hamming ball of radius `t` in
the words of length `n` over an alphabet of `q` letters. -/
def hammingBallVolume (q n t : ℕ) : ℕ :=
  ∑ i ∈ range (t + 1), n.choose i * (q - 1) ^ i

theorem hammingBallVolume_def (q n t : ℕ) :
    hammingBallVolume q n t = ∑ i ∈ range (t + 1), n.choose i * (q - 1) ^ i := (rfl)

/-- For `q ≥ 1` and `t ≥ n` the volume is `q^n`, by the binomial theorem. -/
theorem hammingBallVolume_of_le {q n t : ℕ} (hq : 1 ≤ q) (h : n ≤ t) :
    hammingBallVolume q n t = q ^ n := by
  have hsub : range (n + 1) ⊆ range (t + 1) := range_subset_range.2 (by omega)
  rw [hammingBallVolume_def, ← sum_subset hsub fun i _ hi ↦ by
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi), zero_mul]]
  conv_rhs => rw [← Nat.sub_add_cancel hq, add_pow]
  exact sum_congr rfl fun i _ ↦ by rw [one_pow, mul_one, mul_comm, Nat.cast_id]

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Exactly `(q - 1)^#s` words differ from `x` exactly on the coordinates in `s`. -/
theorem card_filter_ne_eq (x : ι → α) (s : Finset ι) :
    #{y : ι → α | ({j | x j ≠ y j} : Finset ι) = s} = (Fintype.card α - 1) ^ #s := by
  set T : ι → Finset α := fun j ↦ if j ∈ s then univ.erase (x j) else {x j}
  have hT : ({y : ι → α | ({j | x j ≠ y j} : Finset ι) = s} : Finset (ι → α)) =
      Fintype.piFinset T := by
    ext y
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Finset.ext_iff]
    refine forall_congr' fun j ↦ ?_
    by_cases hj : j ∈ s <;> simp [T, hj, eq_comm]
  rw [hT, Fintype.card_piFinset, ← prod_const, ← prod_ite_mem_eq s]
  refine prod_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ s <;> simp [T, hj]

/-- Exactly `(n choose i) (q - 1)^i` words are at Hamming distance `i` from `x`. -/
theorem card_filter_hammingDist_eq (x : ι → α) (i : ℕ) :
    #{y : ι → α | hammingDist x y = i} = (Fintype.card ι).choose i * (Fintype.card α - 1) ^ i := by
  rw [card_eq_sum_card_fiberwise (f := fun y ↦ ({j | x j ≠ y j} : Finset ι))
    (t := powersetCard i univ) fun y hy ↦ by
      simpa [mem_powersetCard, hammingDist] using hy]
  rw [← card_univ, ← card_powersetCard, card_eq_sum_ones, sum_mul, one_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  have hs' := (mem_powersetCard.1 hs).2
  rw [filter_filter, ← hs', ← card_filter_ne_eq x s]
  refine congr_arg card (filter_congr fun y _ ↦ ⟨And.right, fun h ↦ ⟨?_, h⟩⟩)
  rw [hammingDist, h]

/-- **The volume of a Hamming ball.** Exactly `V_q(n, t)` words are at Hamming distance at most
`t` from a word `x` of length `n` over an alphabet of `q` letters. -/
theorem card_hammingBall (x : ι → α) (t : ℕ) :
    #{y : ι → α | hammingDist x y ≤ t} =
      hammingBallVolume (Fintype.card α) (Fintype.card ι) t := by
  rw [card_eq_sum_card_fiberwise (f := fun y ↦ hammingDist x y) (t := range (t + 1)) fun y hy ↦ by
      simpa [Nat.lt_succ_iff] using hy, hammingBallVolume_def]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [filter_filter, ← card_filter_hammingDist_eq x i]
  refine congr_arg card (filter_congr fun y _ ↦ ⟨And.right, fun h ↦ ⟨?_, h⟩⟩)
  rw [h]
  exact Nat.lt_succ_iff.1 (mem_range.1 hi)

/-! ### Checks -/

example : hammingBallVolume 2 7 1 = 8 := by decide
example : hammingBallVolume 2 23 3 = 2048 := by decide
example : hammingBallVolume 3 11 2 = 243 := by decide

/-- Radii beyond the length count every word: `V_3(2, 5) = 3^2`. -/
example : hammingBallVolume 3 2 5 = 9 := by decide

end TauCeti
