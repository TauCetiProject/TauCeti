/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Bounded overlap of families labelled by integers

Let the indices of a family be labelled injectively by integers. A finite set of indices whose
labels lie within `L` of a fixed integer has at most `2 L` elements; in particular, if `W i` is the
set of indices whose labels lie within `L` of that of `i`, then each `W i` has at most `2 L`
elements and each index lies in at most `2 L` of the sets `W i`. These are the counting hypotheses
of the banded Cauchy–Schwarz inequality `ENNReal.tsum_sum_mul_le_of_card_le`.

If the members of a family whose labels are at least `L` apart have zero product, then at most
`L` members are nonzero, so that the sum of squares of a real family is at most `L` when its values
lie in `[-1, 1]`; and if the family moreover sums to `1`, then `(∑_{k ∈ W} f k) f i = f i` for
every finite `W` containing the members whose labels lie within `L` of that of `i`, that is, the
neighbouring members sum to `1` wherever `f i ≠ 0`. Applied pointwise to a family of functions,
these give the finite overlap, the bounded sum of squares and the window identity of partitions of
unity such as the Littlewood–Paley cutoffs.

## Main results

* `TauCeti.card_le_two_mul_of_abs_sub_lt`: a set of indices with labels within `L` of `a` has at
  most `2 L` elements.
* `TauCeti.card_filter_mem_le_two_mul_of_abs_sub_lt`: if every `k ∈ W i` has label within `L` of
  that of `i`, then every index lies in at most `2 L` of the sets `W i`.
* `TauCeti.card_filter_ne_zero_le_of_mul_eq_zero`: at most `L` members of a family whose
  `L`-separated members have zero product are nonzero.
* `TauCeti.sum_sq_le_of_mul_eq_zero`: the sum of squares of such a real family with values in
  `[-1, 1]` is at most `L`.
* `TauCeti.sum_mul_eq_right_of_mul_eq_zero`: for such a real family summing to `1`,
  `(∑_{k ∈ W} f k) f i = f i` whenever `W` contains the indices with labels within `L` of that
  of `i`.
-/

public section

namespace TauCeti

variable {ι : Type*}

/-- A finite set of indices whose labels under an injective `c : ι → ℤ` lie within `L` of an
integer `a` has at most `2 L` elements. -/
theorem card_le_two_mul_of_abs_sub_lt {c : ι → ℤ} (hc : Function.Injective c) {L : ℕ}
    {u : Finset ι} {a : ℤ} (hu : ∀ k ∈ u, |c k - a| < L) : u.card ≤ 2 * L :=
  (Finset.card_le_card_of_injOn c (t := Finset.Ioo (a - L) (a + L))
    (fun k hk ↦ by
      have := abs_sub_lt_iff.1 (hu k hk); rw [Finset.mem_coe, Finset.mem_Ioo]; omega)
    hc.injOn).trans (by simp only [Int.card_Ioo]; omega)

/-- If every `k ∈ W i` has label under an injective `c : ι → ℤ` within `L` of the label of `i`,
then every index `k` lies in at most `2 L` of the sets `W i`, over any finite set of indices `i`.
-/
theorem card_filter_mem_le_two_mul_of_abs_sub_lt [DecidableEq ι] {c : ι → ℤ}
    (hc : Function.Injective c) {L : ℕ} {W : ι → Finset ι}
    (hWL : ∀ i k, k ∈ W i → |c k - c i| < L) (s : Finset ι) (k : ι) :
    (s.filter (k ∈ W ·)).card ≤ 2 * L :=
  card_le_two_mul_of_abs_sub_lt hc fun j hj ↦ by
    rw [abs_sub_comm]
    exact hWL j k (Finset.mem_filter.1 hj).2

/-- **Bounded overlap of a family labelled by integers.** Let the indices of `f : ι → M₀` be
labelled by an injective `e : ι → ℤ`, and let `f i * f k = 0` whenever `e i + L ≤ e k`. Then at
most `L` of the `f i` are nonzero, over any finite set of indices. Applied to the values `ψ i ξ` of
a family of functions, this bounds the number of members that are nonzero at `ξ`. -/
theorem card_filter_ne_zero_le_of_mul_eq_zero {M₀ : Type*} [MulZeroClass M₀] [NoZeroDivisors M₀]
    [DecidableEq M₀]
    {f : ι → M₀} {e : ι → ℤ} (he : Function.Injective e) {L : ℕ}
    (hL : ∀ i k, e i + L ≤ e k → f i * f k = 0) (s : Finset ι) :
    (s.filter fun i ↦ f i ≠ 0).card ≤ L := by
  set t := s.filter fun i ↦ f i ≠ 0
  rcases (t.image e).eq_empty_or_nonempty with ht | ht
  · simp [Finset.image_eq_empty.1 ht]
  -- The labels of the nonzero members lie in `[a, a + L)`, where `a` is the least of them.
  obtain ⟨i₀, hi₀, hi₀a⟩ := Finset.mem_image.1 ((t.image e).min'_mem ht)
  refine (Finset.card_le_card_of_injOn e (t := Finset.Ico ((t.image e).min' ht)
    ((t.image e).min' ht + L)) (fun i hi ↦ ?_) he.injOn).trans (by simp)
  refine Finset.mem_Ico.2 ⟨(t.image e).min'_le _ (Finset.mem_image_of_mem e hi),
    lt_of_not_ge fun h ↦ ?_⟩
  exact mul_ne_zero (Finset.mem_filter.1 hi₀).2 (Finset.mem_filter.1 hi).2 (hL i₀ i (hi₀a ▸ h))

/-- **Bounded sum of squares of a family labelled by integers.** If, in addition to the hypotheses
of `TauCeti.card_filter_ne_zero_le_of_mul_eq_zero`, every `f i` lies in `[-1, 1]`, then
`∑ᵢ f i ² ≤ L`, over any finite set of indices. -/
theorem sum_sq_le_of_mul_eq_zero {f : ι → ℝ} {e : ι → ℤ} (he : Function.Injective e)
    {L : ℕ} (hL : ∀ i k, e i + L ≤ e k → f i * f k = 0)
    (habs : ∀ i, |f i| ≤ 1) (s : Finset ι) : ∑ i ∈ s, f i ^ 2 ≤ L := by
  rw [← Finset.sum_filter_of_ne fun i _ h ↦ by simpa using h]
  calc ∑ i ∈ s.filter (fun i ↦ f i ≠ 0), f i ^ 2
      ≤ ∑ _i ∈ s.filter (fun i ↦ f i ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ (sq_le_one_iff_abs_le_one _).2 (habs i)
    _ ≤ L := by simpa using card_filter_ne_zero_le_of_mul_eq_zero he hL s

/-- **Neighbouring members of a partition of unity.** Let `f : ι → ℝ` satisfy `f i * f k = 0`
whenever the labels under `e : ι → ℤ` satisfy `e i + L ≤ e k`, and let `∑ₖ f k = 1` if
`f i ≠ 0`. Then `(∑_{k ∈ W} f k) f i = f i` for every finite set `W` containing the indices whose
labels lie within `L` of that of `i`. Applied to the values `ψ k ξ` of a family of functions, this
says the neighbouring members sum to `1` on the support of `ψ i`. -/
theorem sum_mul_eq_right_of_mul_eq_zero {f : ι → ℝ} {e : ι → ℤ} {L : ℕ}
    (hL : ∀ i k, e i + L ≤ e k → f i * f k = 0) {i : ι}
    (hsum : f i ≠ 0 → HasSum f 1) {W : Finset ι} (hW : ∀ k, |e k - e i| < L → k ∈ W) :
    (∑ k ∈ W, f k) * f i = f i := by
  rcases eq_or_ne (f i) 0 with h | h
  · rw [h, mul_zero]
  -- Multiply `∑ₖ f k = 1` by `f i`: the terms with `k ∉ W` vanish.
  have hzero : ∀ k ∉ W, f k * f i = 0 := fun k hk ↦ by
    have hk := mt (hW k) hk
    rw [abs_sub_lt_iff, not_and_or, not_lt, not_lt] at hk
    rcases hk with hk | hk
    · rw [mul_comm]
      exact hL i k (by omega)
    · exact hL k i (by omega)
  rw [Finset.sum_mul]
  exact (hasSum_sum_of_ne_finset_zero hzero).unique (by simpa using (hsum h).mul_right (f i))

end TauCeti
