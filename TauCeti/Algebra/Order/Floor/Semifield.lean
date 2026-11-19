/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Floor

/-!
# Ceilings and floors of quotients by a step

For a step `τ > 0` in a linearly ordered division semiring, the multiples `n τ` of the step
lying in a half-open interval `[s, t)` are those with `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)`. With ordered
subtraction and `s ≤ t`, there are strictly fewer than `(t - s) / τ + 1` of them. These are the
index counts of time discretizations with step `τ`. The counting bound also holds for `τ = 0`.

Dually, for `B > 0` and any natural degree bound `n`, multiplying `B < ⌊B⌋₊ + 1` by
`n / B < ⌊n / B⌋₊ + 1` gives `n < (⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)`, and in particular
`n < (2 * ⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)`. This includes `n = 0` and `B < 1`, and counts the available
jet conditions on an integer interval of radius `B`.

For closed intervals `[0, W]` subdivided into `n > 0` equal cells of step `W / n`, clamping the
floor index `⌊x / (W / n)⌋₊` at `n - 1` keeps the right endpoint `W` inside the last cell while
preserving `[k * (W / n), (k + 1) * (W / n)]` for all `x ∈ [0, W]`. Similarly, `max 1 ⌈t⌉₊` gives
a positive cell count bounded by `t + 1` for `t ≥ 0`, and strictly below `t + 1` whenever `t > 0`.

## Main results

* `TauCeti.natCast_ceil_div_sub_ceil_div_lt`: `⌈t / τ⌉₊ - ⌈s / τ⌉₊ < (t - s) / τ + 1`.
* `TauCeti.mem_Ico_ceil_div_iff`: `n ∈ [⌈s / τ⌉₊, ⌈t / τ⌉₊)` if and only if `n τ ∈ [s, t)`.
* `TauCeti.exists_pos_nat_mul_bounds`: a positive multiple `N a` lies in `(t, t + a]`.
* `TauCeti.pairwiseDisjoint_Ico_ceil_div`: the index sets `[⌈sᵢ / τ⌉₊, ⌈tᵢ / τ⌉₊)` are pairwise
  disjoint whenever the intervals `(sᵢ, tᵢ]` are.
* `TauCeti.card_biUnion_Ico_ceil_div_le`: the union of these index sets over `k` intervals has at
  most `(∑ᵢ (tᵢ - sᵢ)) / τ + k` elements.
* `TauCeti.lt_floor_add_one_mul_floor_div_add_one`: `n < (⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` for `B > 0`.
* `TauCeti.lt_two_mul_floor_add_one_mul_floor_div_add_one`:
  `n < (2 * ⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` for `B > 0`.
* `TauCeti.mem_Icc_min_sub_one_natFloor_div`: for `0 ≤ W` and `0 < n`, every `x ∈ [0, W]` lies in
  the closed cell of step `W / n` indexed by `min (n - 1) ⌊x / (W / n)⌋₊`.
* `TauCeti.natCast_max_one_ceil_lt_add_one` and `TauCeti.natCast_max_one_ceil_le_add_one`:
  `max 1 ⌈t⌉₊ < t + 1` for `0 < t`, and `max 1 ⌈t⌉₊ ≤ t + 1` for `0 ≤ t`.
-/

public section

namespace TauCeti

variable {K : Type*} [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  {τ s t B : K}

/-- For a nonnegative step `τ` and `s ≤ t`, the indices in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` number
strictly less than `(t - s) / τ + 1`. This holds for both ordinary and truncated subtraction. -/
theorem natCast_ceil_div_sub_ceil_div_lt [Sub K] [OrderedSub K] (hτ : 0 ≤ τ) (hst : s ≤ t) :
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : K) < (t - s) / τ + 1 := by
  -- For `t < 0` both ceilings vanish.
  rcases lt_or_ge t 0 with ht | ht
  · rw [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg ht.le hτ), Nat.zero_sub,
      Nat.cast_zero]
    exact add_pos_of_nonneg_of_pos
      (div_nonneg (le_tsub_of_add_le_left ((add_zero s).trans_le hst)) hτ) zero_lt_one
  have hle : ⌈s / τ⌉₊ ≤ ⌈t / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hst hτ)
  have hdiv : t / τ ≤ (t - s) / τ + s / τ := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right le_tsub_add hτ
  apply (add_lt_add_iff_right (⌈s / τ⌉₊ : K)).mp
  calc
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : K) + ⌈s / τ⌉₊ = (⌈t / τ⌉₊ : K) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hle]
    _ < t / τ + 1 := Nat.ceil_lt_add_one (div_nonneg ht hτ)
    _ ≤ (t - s) / τ + s / τ + 1 := by gcongr
    _ ≤ (t - s) / τ + 1 + ⌈s / τ⌉₊ := by
      rw [add_right_comm]
      gcongr
      exact Nat.le_ceil _

/-- For a step `τ > 0`, an index `n` lies in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` exactly when the multiple
`n τ` lies in `[s, t)`. -/
theorem mem_Ico_ceil_div_iff (hτ : 0 < τ) {n : ℕ} :
    n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊ ↔ n * τ ∈ Set.Ico s t := by
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hτ, lt_div_iff₀ hτ, Set.mem_Ico]

/-- For a step `τ > 0`, the index sets `[⌈sᵢ / τ⌉₊, ⌈tᵢ / τ⌉₊)` of the multiples of `τ` in
`[sᵢ, tᵢ)` are pairwise disjoint whenever the intervals `(sᵢ, tᵢ]` are. -/
theorem pairwiseDisjoint_Ico_ceil_div (hτ : 0 < τ) {ι : Type*} {s t : ι → K} {S : Set ι}
    (h : S.PairwiseDisjoint fun i ↦ Set.Ioc (s i) (t i)) :
    S.PairwiseDisjoint fun i ↦ Finset.Ico ⌈s i / τ⌉₊ ⌈t i / τ⌉₊ := by
  intro i hi j hj hij
  refine Finset.disjoint_left.2 fun n hni hnj ↦ ?_
  rw [mem_Ico_ceil_div_iff hτ] at hni hnj
  exact Set.disjoint_left.1 (h hi hj hij)
    ⟨lt_of_le_of_lt hni.1 (lt_min hni.2 hnj.2), min_le_left _ _⟩
    ⟨lt_of_le_of_lt hnj.1 (lt_min hni.2 hnj.2), min_le_right _ _⟩

/-- For `0 ≤ τ` and `sᵢ ≤ tᵢ` for `k` indices `i`, the union `⋃ᵢ [⌈sᵢ / τ⌉₊, ⌈tᵢ / τ⌉₊)` has at
most `(∑ᵢ (tᵢ - sᵢ)) / τ + k` elements. The intervals need not be disjoint. -/
theorem card_biUnion_Ico_ceil_div_le [Sub K] [OrderedSub K] (hτ : 0 ≤ τ)
    {ι : Type*} (I : Finset ι) {s t : ι → K} (hst : ∀ i ∈ I, s i ≤ t i) :
    ((I.biUnion fun i ↦ Finset.Ico ⌈s i / τ⌉₊ ⌈t i / τ⌉₊).card : K) ≤
      (∑ i ∈ I, (t i - s i)) / τ + I.card := by
  calc ((I.biUnion fun i ↦ Finset.Ico ⌈s i / τ⌉₊ ⌈t i / τ⌉₊).card : K)
      ≤ ((∑ i ∈ I, (Finset.Ico ⌈s i / τ⌉₊ ⌈t i / τ⌉₊).card : ℕ) : K) :=
        Nat.cast_le.2 Finset.card_biUnion_le
    _ = ∑ i ∈ I, ((⌈t i / τ⌉₊ - ⌈s i / τ⌉₊ : ℕ) : K) := by simp
    _ ≤ ∑ i ∈ I, ((t i - s i) / τ + 1) :=
        Finset.sum_le_sum fun i hi ↦ (natCast_ceil_div_sub_ceil_div_lt hτ (hst i hi)).le
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_div]; simp

/-- For `B > 0` and any `n : ℕ`, `(⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` strictly exceeds `n`, including
when `n = 0` or `B < 1`. -/
theorem lt_floor_add_one_mul_floor_div_add_one (hB : 0 < B) (n : ℕ) :
    n < (⌊B⌋₊ + 1) * (⌊(n : K) / B⌋₊ + 1) := by
  -- Multiply `n / B < ⌊n / B⌋₊ + 1` by `B < ⌊B⌋₊ + 1`; the left side is `n / B * B = n`.
  have h := mul_lt_mul'' (Nat.lt_floor_add_one ((n : K) / B)) (Nat.lt_floor_add_one B)
    (div_nonneg n.cast_nonneg hB.le) hB.le
  rw [div_mul_cancel₀ (n : K) hB.ne'] at h
  rw [Nat.mul_comm]
  exact_mod_cast h

/-- For `B > 0` and any `n : ℕ`, `(2 * ⌊B⌋₊ + 1) * (⌊n / B⌋₊ + 1)` strictly exceeds `n`: an
integer interval `[-⌊B⌋₊, ⌊B⌋₊]` with derivative orders up to `⌊n / B⌋₊` has more than `n`
point-order pairs, also when `n = 0` or `B < 1`. -/
theorem lt_two_mul_floor_add_one_mul_floor_div_add_one (hB : 0 < B) (n : ℕ) :
    n < (2 * ⌊B⌋₊ + 1) * (⌊(n : K) / B⌋₊ + 1) :=
  (lt_floor_add_one_mul_floor_div_add_one hB n).trans_le (Nat.mul_le_mul_right _ (by omega))

/-- For a nonnegative `t` and positive `a`, some positive multiple `N a` lies in `(t, t + a]`. -/
theorem exists_pos_nat_mul_bounds {t a : K} (ht : 0 ≤ t) (ha : 0 < a) :
    ∃ N : ℕ, 1 ≤ N ∧ t < N * a ∧ N * a ≤ t + a := by
  have htdiv : 0 ≤ t / a := div_nonneg ht ha.le
  refine ⟨⌊t / a⌋₊ + 1, by omega, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (t / a)
    exact (div_lt_iff₀ ha).mp (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  · push_cast
    rw [add_mul, one_mul]
    exact add_le_add_left ((le_div_iff₀ ha).mp (Nat.floor_le htdiv)) a

/-- For `n = 3` and `B = 1 / 2`, `⌊B⌋₊ = 0` and `⌊n / B⌋₊ = 6`, giving `1 * 7 > 3`; for `n = 2`
and `B = 3`, `⌊B⌋₊ = 3` and `⌊n / B⌋₊ = 0`, giving `7 * 1 > 2`. -/
example : ⌊(1 / 2 : ℚ)⌋₊ = 0 ∧ ⌊(3 : ℚ) / (1 / 2)⌋₊ = 6 ∧
    3 < (2 * ⌊(1 / 2 : ℚ)⌋₊ + 1) * (⌊(3 : ℚ) / (1 / 2)⌋₊ + 1) ∧
    ⌊(3 : ℚ)⌋₊ = 3 ∧ ⌊(2 : ℚ) / 3⌋₊ = 0 ∧
    2 < (2 * ⌊(3 : ℚ)⌋₊ + 1) * (⌊(2 : ℚ) / 3⌋₊ + 1) := by
  refine ⟨?_, ?_, lt_two_mul_floor_add_one_mul_floor_div_add_one (by norm_num) 3, ?_, ?_,
    lt_two_mul_floor_add_one_mul_floor_div_add_one (by norm_num) 2⟩ <;> norm_num

/-- For `0 ≤ W` and `0 < n`, every `x ∈ [0, W]` lies in the closed cell
`[k * (W / n), (k + 1) * (W / n)]` of step `W / n` indexed by
`k = min (n - 1) ⌊x / (W / n)⌋₊`, including at `W = 0` and at the right endpoint `x = W`. -/
theorem mem_Icc_min_sub_one_natFloor_div {W x : K} (hW : 0 ≤ W) {n : ℕ} (hn : 0 < n)
    (hx : x ∈ Set.Icc 0 W) :
    x ∈ Set.Icc ((min (n - 1) ⌊x / (W / n)⌋₊ : ℕ) * (W / n))
      (((min (n - 1) ⌊x / (W / n)⌋₊ : ℕ) + 1) * (W / n)) := by
  rcases hW.eq_or_lt with rfl | hW
  · simp [le_antisymm hx.2 hx.1]
  have hnpos : (0 : K) < n := Nat.cast_pos.2 hn
  have hτ : 0 < W / n := div_pos hW hnpos
  refine ⟨?_, ?_⟩
  · rw [← le_div_iff₀ hτ]
    exact (Nat.cast_le.2 (min_le_right _ _)).trans (Nat.floor_le (div_nonneg hx.1 hτ.le))
  · rcases le_total (n - 1) ⌊x / (W / n)⌋₊ with h | h
    · have hn1 : ((n - 1 : ℕ) : K) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
      rw [min_eq_left h, hn1, Nat.cast_comm, div_mul_cancel₀ W hnpos.ne']
      exact hx.2
    · rw [min_eq_right h, ← div_le_iff₀ hτ]
      exact (Nat.lt_floor_add_one _).le

section Semiring

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

/-- For a positive `t`, the positive cell count `max 1 ⌈t⌉₊` is strictly below `t + 1`, including
when `t` is a positive natural number. -/
theorem natCast_max_one_ceil_lt_add_one {t : R} (ht : 0 < t) :
    ((max 1 ⌈t⌉₊ : ℕ) : R) < t + 1 := by
  rw [max_eq_right (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 ht).ne')]
  exact Nat.ceil_lt_add_one ht.le

/-- For a nonnegative `t`, the positive cell count `max 1 ⌈t⌉₊` is at most `t + 1`. -/
theorem natCast_max_one_ceil_le_add_one {t : R} (ht : 0 ≤ t) :
    ((max 1 ⌈t⌉₊ : ℕ) : R) ≤ t + 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · exact (natCast_max_one_ceil_lt_add_one ht).le

end Semiring

end TauCeti
