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

If the members of one family of real functions labelled by integers `j` vanish outside balls of
radius comparable to `2 ^ j`, and those of another vanish inside such balls, then members of the
two families whose labels are far enough apart have disjoint supports.

If the members of a family of real functions whose labels are at least `L` apart have disjoint
supports, then at most `L` members are nonzero at each point, so that the sum of squares
of the family is at most `L` when its values lie in `[-1, 1]`; and if the family is moreover a
partition of unity, then the members whose labels lie within `L` of that of `i` sum to `1` on the
support of the `i`-th member.

## Main results

* `TauCeti.card_le_two_mul_of_abs_sub_lt`: a set of indices with labels within `L` of `a` has at
  most `2 L` elements.
* `TauCeti.card_filter_mem_le_two_mul_of_abs_sub_lt`: if every `k ∈ W i` has label within `L` of
  that of `i`, then every index lies in at most `2 L` of the sets `W i`.
* `TauCeti.exists_mul_eq_zero_of_dyadic_support`: members of two families supported in dyadic
  annuli whose labels are far enough apart have disjoint supports.
* `TauCeti.card_filter_ne_zero_le_of_mul_eq_zero`: at most `L` members of a family with
  `L`-separated disjoint supports are nonzero at each point.
* `TauCeti.sum_sq_le_of_mul_eq_zero`: the sum of squares of such a family with values in
  `[-1, 1]` is at most `L`.
* `TauCeti.sum_mul_eq_right_of_mul_eq_zero`: for such a family summing to `1`, the members with
  labels within `L` of that of `i` sum to `1` on the support of the `i`-th member.
-/

public section

namespace TauCeti

variable {ι α : Type*}

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

/-- **Finite overlap of dyadically supported families.** Let `ψ i` vanish where
`2 ^ e i * R ≤ ρ ξ` and `ψ' k` vanish where `ρ ξ ≤ 2 ^ (e' k - 1) * r`, with `0 < r`. Then there
is `L` such that `ψ i` and `ψ' k` have disjoint supports whenever `e i + L ≤ e' k`. -/
theorem exists_mul_eq_zero_of_dyadic_support {κ : Type*} {ψ : ι → α → ℝ} {ψ' : κ → α → ℝ}
    {e : ι → ℤ} {e' : κ → ℤ} {ρ : α → ℝ} {R r : ℝ} (hr : 0 < r)
    (hψ : ∀ i ξ, 2 ^ e i * R ≤ ρ ξ → ψ i ξ = 0)
    (hψ' : ∀ k ξ, ρ ξ ≤ 2 ^ (e' k - 1) * r → ψ' k ξ = 0) :
    ∃ L : ℕ, ∀ i k, e i + L ≤ e' k → ∀ ξ, ψ i ξ * ψ' k ξ = 0 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / r) (one_lt_two (α := ℝ))
  have hn' : R ≤ 2 ^ n * r := ((div_lt_iff₀ hr).1 hn).le
  refine ⟨n + 1, fun i k hik ξ ↦ ?_⟩
  rcases le_or_gt (ρ ξ) (2 ^ (e' k - 1) * r) with hξ | hξ
  · rw [hψ' k ξ hξ, mul_zero]
  · refine mul_eq_zero_of_left (hψ i ξ (le_trans ?_ hξ.le)) _
    calc (2 : ℝ) ^ e i * R ≤ 2 ^ e i * (2 ^ n * r) :=
          mul_le_mul_of_nonneg_left hn' (zpow_nonneg zero_le_two _)
      _ = 2 ^ (e i + n) * r := by rw [zpow_add₀ two_ne_zero, zpow_natCast, mul_assoc]
      _ ≤ 2 ^ (e' k - 1) * r :=
          mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ one_le_two (by push_cast at hik; omega))
            hr.le

/-- **Bounded overlap of a family labelled by integers.** Let the indices of `ψ : ι → α → ℝ` be
labelled by an injective `e : ι → ℤ`, and let `ψ i` and `ψ k` have disjoint supports whenever
`e i + L ≤ e k`. Then at every `ξ` at most `L` of the `ψ i` are nonzero, over any finite set of
indices. -/
theorem card_filter_ne_zero_le_of_mul_eq_zero {ψ : ι → α → ℝ} {e : ι → ℤ}
    (he : Function.Injective e) {L : ℕ} (hL : ∀ i k, e i + L ≤ e k → ∀ ξ, ψ i ξ * ψ k ξ = 0)
    (s : Finset ι) (ξ : α) : (s.filter fun i ↦ ψ i ξ ≠ 0).card ≤ L := by
  set t := s.filter fun i ↦ ψ i ξ ≠ 0
  rcases (t.image e).eq_empty_or_nonempty with ht | ht
  · simp [Finset.image_eq_empty.1 ht]
  -- The labels of the nonzero members lie in `[a, a + L)`, where `a` is the least of them.
  obtain ⟨i₀, hi₀, hi₀a⟩ := Finset.mem_image.1 ((t.image e).min'_mem ht)
  refine (Finset.card_le_card_of_injOn e (t := Finset.Ico ((t.image e).min' ht)
    ((t.image e).min' ht + L)) (fun i hi ↦ ?_) he.injOn).trans (by simp)
  refine Finset.mem_Ico.2 ⟨(t.image e).min'_le _ (Finset.mem_image_of_mem e hi),
    lt_of_not_ge fun h ↦ ?_⟩
  exact mul_ne_zero (Finset.mem_filter.1 hi₀).2 (Finset.mem_filter.1 hi).2
    (hL i₀ i (hi₀a ▸ h) ξ)

/-- **Bounded sum of squares of a family labelled by integers.** If, in addition to the hypotheses
of `TauCeti.card_filter_ne_zero_le_of_mul_eq_zero`, every `ψ i` takes values in `[-1, 1]`, then
`∑ᵢ ψ i ξ ² ≤ L` for every `ξ`, over any finite set of indices. -/
theorem sum_sq_le_of_mul_eq_zero {ψ : ι → α → ℝ} {e : ι → ℤ} (he : Function.Injective e)
    {L : ℕ} (hL : ∀ i k, e i + L ≤ e k → ∀ ξ, ψ i ξ * ψ k ξ = 0)
    (habs : ∀ i ξ, |ψ i ξ| ≤ 1) (s : Finset ι) (ξ : α) : ∑ i ∈ s, ψ i ξ ^ 2 ≤ L := by
  rw [← Finset.sum_filter_of_ne fun i _ h ↦ by simpa using h]
  calc ∑ i ∈ s.filter (fun i ↦ ψ i ξ ≠ 0), ψ i ξ ^ 2
      ≤ ∑ _i ∈ s.filter (fun i ↦ ψ i ξ ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ (sq_le_one_iff_abs_le_one _).2 (habs i ξ)
    _ ≤ L := by simpa using card_filter_ne_zero_le_of_mul_eq_zero he hL s ξ

/-- **Neighbouring members of a partition of unity.** Let the members of `ψ : ι → α → ℝ` whose
labels under `e : ι → ℤ` are at least `L` apart have disjoint supports, and let `∑ₖ ψ k ξ = 1` if
`ψ i ξ ≠ 0`. Then `(∑_{k ∈ W} ψ k ξ) ψ i ξ = ψ i ξ` for every finite set `W` containing the indices
whose labels lie within `L` of that of `i`. -/
theorem sum_mul_eq_right_of_mul_eq_zero {ψ : ι → α → ℝ} {e : ι → ℤ} {L : ℕ}
    (hL : ∀ i k, e i + L ≤ e k → ∀ ξ, ψ i ξ * ψ k ξ = 0) {i : ι} {ξ : α}
    (hsum : ψ i ξ ≠ 0 → HasSum (ψ · ξ) 1) {W : Finset ι} (hW : ∀ k, |e k - e i| < L → k ∈ W) :
    (∑ k ∈ W, ψ k ξ) * ψ i ξ = ψ i ξ := by
  rcases eq_or_ne (ψ i ξ) 0 with h | h
  · rw [h, mul_zero]
  -- Multiply `∑ₖ ψ k ξ = 1` by `ψ i ξ`: the terms with `k ∉ W` vanish.
  have hzero : ∀ k ∉ W, ψ k ξ * ψ i ξ = 0 := fun k hk ↦ by
    have hk := mt (hW k) hk
    rw [abs_sub_lt_iff, not_and_or, not_lt, not_lt] at hk
    rcases hk with hk | hk
    · rw [mul_comm]
      exact hL i k (by omega) ξ
    · exact hL k i (by omega) ξ
  rw [Finset.sum_mul]
  exact (hasSum_sum_of_ne_finset_zero hzero).unique (by simpa using (hsum h).mul_right (ψ i ξ))

end TauCeti
