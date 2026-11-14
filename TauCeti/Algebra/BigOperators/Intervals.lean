/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.SuccPred.Int
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sums over intervals of natural numbers and integers

A sum `∑ k ∈ Ico m (n + 1), f k` whose summands split as `f m = β m`, `f n = γ n`, and
`f k = γ k + β k` for `m < k < n` regroups as the sum over `m ≤ k < n` of the adjacent pairs
`β k + γ (k + 1)`. The codomain is any additive commutative monoid. In a not necessarily
associative ring, a constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it.
For an integer interval `[-a, b]` with `a, b : ℕ`, adding the term `F 0` to
`∑ i ∈ Icc (-(a : ℤ)) b, F i` splits the sum into the nonnegative part `∑ j ∈ range (b + 1), F j`
and the nonpositive part `∑ j ∈ range (a + 1), F (-(j : ℤ))`. In a ring, the partial sums
`∑_{1 ≤ k ≤ n} (-1) ^ (k + 1)` of the alternating sequence `1, -1, 1, …` are `0` or `1`.
The sum of squares `∑_{r < n} r ^ 2 = n (n - 1) (2 n - 1) / 6` holds in `ℕ`, and with the
denominator cleared it holds in any ring, as does Gauss's sum `2 ∑_{r < n} r = n (n - 1)`.
Counted with sign, the integers between `0` and any `k : ℤ` sum to `k (k - 1) / 2`, the signed
form of Gauss's sum.
A window sum `∑_{j - L ≤ k < j + L} f k` is the sum over `d < 2 L` of the shifts of `f` that read
`f` at `j + d - L` where this index is defined, and vanish otherwise.

## Main results

* `Finset.sum_Ico_eq_sum_Ico_add`: the regrouping of `∑ k ∈ Ico m (n + 1), f k` into the pairs
  `β k + γ (k + 1)`.
* `Finset.sum_Ico_one_sub_one_const`: `∑ _k ∈ Ico 1 (n - 1), c = (n - 2) * c` for `2 ≤ n`.
* `Finset.sum_Icc_eq_add_sum_range`: `(∑ i ∈ Icc (-(a : ℤ)) b, F i) + F 0` equals the sum of `F j`
  over `j ∈ range (b + 1)` plus the sum of `F (-(j : ℤ))` over `j ∈ range (a + 1)`.
* `Finset.sum_range_natCast_mul_two`, `Finset.sum_range_id_sq_mul_six`, `Finset.sum_range_id_sq`,
  `Finset.sum_range_natCast_sq_mul_six`: Gauss's sum in a ring and the sum of squares below `n`.
* `Finset.sum_range_sub_mul_two`: twice the sum of `r + 1 - j` over `j < e` is `e (2 r + 3 - e)`.
* `Finset.sum_Icc_neg_one_pow_add_one`: `∑ k ∈ Icc 1 n, (-1) ^ (k + 1)` is `0` for even `n` and
  `1` for odd `n`.
* `Finset.two_mul_sum_Ico_zero_sub_sum_Ico_zero`: twice `∑_{0 ≤ j < k} j - ∑_{k ≤ j < 0} j` is
  `k (k - 1)` for every `k : ℤ`.
* `Finset.sum_Ico_sub_add_eq_sum_range_indicator`: a window sum `∑_{j - L ≤ k < j + L} f k` as the
  sum of `2 L` shifts of `f`.
-/

public section

namespace Finset

/-- If `m < n`, the summands `f m = β m`, `f n = γ n`, and `f k = γ k + β k` for
`m < k < n` regroup as the adjacent pairs `β k + γ (k + 1)` over `m ≤ k < n`. -/
theorem sum_Ico_eq_sum_Ico_add {M : Type*} [AddCommMonoid M] {f β γ : ℕ → M} {m n : ℕ}
    (hmn : m < n) (hfirst : f m = β m) (hmid : ∀ k ∈ Ico (m + 1) n, f k = γ k + β k)
    (hlast : f n = γ n) :
    ∑ k ∈ Ico m (n + 1), f k = ∑ k ∈ Ico m n, (β k + γ (k + 1)) := by
  -- peel off the endpoint summands
  have hf : ∑ k ∈ Ico m (n + 1), f k = f m + ∑ k ∈ Ico (m + 1) n, f k + f n := by
    rw [sum_eq_sum_Ico_succ_bot (by omega), sum_Ico_succ_top (by omega), add_assoc]
  -- peel off the first `β`-summand
  have hβ : ∑ k ∈ Ico m n, β k = β m + ∑ k ∈ Ico (m + 1) n, β k :=
    sum_eq_sum_Ico_succ_bot hmn β
  -- shift the `γ`-summands down by one and peel off the last one
  have hγ : ∑ k ∈ Ico m n, γ (k + 1) = ∑ k ∈ Ico (m + 1) n, γ k + γ n := by
    rw [sum_Ico_add' γ, sum_Ico_succ_top (by omega : m + 1 ≤ n)]
  simp only [hf, sum_congr rfl hmid, sum_add_distrib, hβ, hγ, hfirst, hlast]
  abel

/-- A constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it. -/
theorem sum_Ico_one_sub_one_const {R : Type*} [NonAssocRing R] {n : ℕ} (hn : 2 ≤ n) (c : R) :
    ∑ _k ∈ Ico 1 (n - 1), c = ((n : R) - 2) * c := by
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.sub_sub, Nat.cast_sub hn, Nat.cast_ofNat]

/-- Splitting an integer interval `[-a, b]` into its parts `0 ≤ j ≤ b` and `-a ≤ -j ≤ 0`, which
overlap in `0`. -/
theorem sum_Icc_eq_add_sum_range {M : Type*} [AddCommMonoid M] (F : ℤ → M) (a b : ℕ) :
    (∑ i ∈ Icc (-(a : ℤ)) b, F i) + F 0 =
      (∑ j ∈ range (b + 1), F j) + ∑ j ∈ range (a + 1), F (-(j : ℤ)) := by
  classical
  set s : Finset ℤ := (range (b + 1)).image (fun j : ℕ ↦ (j : ℤ)) with hs
  set t : Finset ℤ := (range (a + 1)).image (fun j : ℕ ↦ -(j : ℤ)) with ht
  have hunion : s ∪ t = Icc (-(a : ℤ)) b := by
    ext i
    simp only [hs, ht, mem_union, mem_image, mem_range, mem_Icc]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
    · intro hi
      rcases le_or_gt 0 i with h | h
      · exact Or.inl ⟨i.toNat, by omega, by omega⟩
      · exact Or.inr ⟨(-i).toNat, by omega, by omega⟩
  have hinter : s ∩ t = {(0 : ℤ)} := by
    ext i
    simp only [hs, ht, mem_inter, mem_image, mem_range, mem_singleton]
    constructor
    · rintro ⟨⟨j, _, rfl⟩, k, _, hk'⟩
      omega
    · rintro rfl
      exact ⟨⟨0, by omega, by simp⟩, 0, by omega, by simp⟩
  have hkey := sum_union_inter (s₁ := s) (s₂ := t) (f := F)
  rw [hunion, hinter, sum_singleton] at hkey
  rw [hkey, hs, ht, sum_image (fun _ _ _ _ h ↦ by exact_mod_cast h),
    sum_image (fun _ _ _ _ h ↦ by omega)]

/-- Gauss's sum cast into a not necessarily associative ring: twice the sum of the natural numbers
below `n` is `n (n - 1)`. -/
theorem sum_range_natCast_mul_two {R : Type*} [NonAssocRing R] (n : ℕ) :
    (∑ r ∈ range n, (r : R)) * 2 = n * (n - 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have h := congrArg (Nat.cast : ℕ → R) (sum_range_id_mul_two n)
  push_cast [Nat.cast_sub hn] at h
  exact h

/-- Six times the sum of the squares of the natural numbers below `n` is `n (n - 1) (2 n - 1)`. -/
theorem sum_range_id_sq_mul_six (n : ℕ) :
    (∑ i ∈ range n, i ^ 2) * 6 = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, show 2 * (n + 1 + 1) - 1 = 2 * n + 3 by omega,
        show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      ring

/-- The sum of the squares of the natural numbers below `n` is `n (n - 1) (2 n - 1) / 6`. -/
theorem sum_range_id_sq (n : ℕ) : ∑ i ∈ range n, i ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  rw [← sum_range_id_sq_mul_six, Nat.mul_div_cancel _ (by decide)]

/-- The sum of the squares of the natural numbers below `n`, cast into a ring, is
`n (n - 1) (2 n - 1)` after multiplying by `6`. -/
theorem sum_range_natCast_sq_mul_six {R : Type*} [Ring R] (n : ℕ) :
    (∑ r ∈ range n, (r : R) ^ 2) * 6 = n * (n - 1) * (2 * n - 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have h := congrArg (Nat.cast : ℕ → R) (sum_range_id_sq_mul_six n)
  push_cast [Nat.cast_sub hn, Nat.cast_sub (by omega : 1 ≤ 2 * n)] at h
  exact h

/-- Twice the number of pairs `(j, i)` with `j < e` and `i + j ≤ r`, that is, the sum of `r + 1 - j`
over `j < e`, doubled. -/
theorem sum_range_sub_mul_two (r e : ℕ) (he : e ≤ r + 1) :
    (∑ j ∈ range e, ((r + 1 - j : ℕ) : ℤ)) * 2 = e * (2 * r + 3 - e) := by
  rw [sum_congr rfl fun j hj ↦ Nat.cast_sub (by grind), sum_sub_distrib, sub_mul,
    sum_range_natCast_mul_two]
  simp
  ring

/-- The partial sums `∑_{1 ≤ k ≤ n} (-1) ^ (k + 1)` of the alternating sequence `1, -1, 1, …` are
`0` for even `n` and `1` for odd `n`; this is Mathlib's `neg_one_geom_sum` with the index shifted
by one. -/
theorem sum_Icc_neg_one_pow_add_one {R : Type*} [Ring R] (n : ℕ) :
    ∑ k ∈ Icc 1 n, (-1 : R) ^ (k + 1) = if Even n then 0 else 1 := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, add_tsub_cancel_right, ← neg_one_geom_sum]
  simp [pow_add]

/-- Counted with sign, the integers between `0` and `k` sum to `k (k - 1) / 2`: twice
`∑_{0 ≤ j < k} j - ∑_{k ≤ j < 0} j` is `k (k - 1)`. For `k ≥ 0` only the first sum is nonempty
and this is Gauss's sum; for `k < 0` only the second one is. -/
theorem two_mul_sum_Ico_zero_sub_sum_Ico_zero (k : ℤ) :
    2 * (∑ j ∈ Ico 0 k, j - ∑ j ∈ Ico k 0, j) = k * (k - 1) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have hi : (0 : ℤ) ≤ i := by positivity
    rw [← insert_Ico_right_eq_Ico_add_one hi, sum_insert (by simp),
      Ico_eq_empty_of_le (by omega : (0 : ℤ) ≤ i + 1)]
    rw [Ico_eq_empty_of_le hi] at ih
    simp only [sum_empty, sub_zero] at ih ⊢
    linear_combination ih
  | pred i ih =>
    have hi : -(i : ℤ) ≤ 0 := by omega
    rw [← insert_Ico_left_eq_Ico_sub_one hi, sum_insert (by simp),
      Ico_eq_empty_of_le (by omega : -(i : ℤ) - 1 ≤ 0)]
    rw [Ico_eq_empty_of_le hi] at ih
    simp only [sum_empty, zero_sub] at ih ⊢
    linear_combination ih

/-- A window sum `∑_{j - L ≤ k < j + L} f k` is the sum of `2 L` shifts of `f`: the `d`-th one
reads `f` at `j + d - L`, where this index is defined. -/
theorem sum_Ico_sub_add_eq_sum_range_indicator {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (L j : ℕ) :
    ∑ k ∈ Ico (j - L) (j + L), f k =
      ∑ d ∈ range (2 * L), {i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L) j := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Function.comp_apply]
  rw [← sum_filter]
  refine sum_nbij' (fun k ↦ k + L - j) (fun d ↦ j + d - L) (fun k hk ↦ ?_) (fun d hd ↦ ?_)
    (fun k hk ↦ ?_) (fun d hd ↦ ?_) fun k hk ↦ ?_
  all_goals simp only [mem_Ico, mem_filter, mem_range] at *
  all_goals first | omega | (congr 1; omega)

end Finset
