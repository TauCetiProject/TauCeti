/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Max

/-!
# Products of antitone sequences over finite sets of indices

For a nonnegative antitone sequence `f : ℕ → R` in an ordered commutative monoid with zero, the
product of `f` over a finite set `s` of indices is largest when `s` is an initial segment: it is
at most the product over `range #s` (`Finset.prod_le_prod_range_card`). More generally, the
product over `s` is at most the product over any set `t` of the same size having, below every
threshold, at least as many indices as `s` (`Finset.prod_le_prod_of_card_filter_lt_le`). If `s`
has `n + 1` elements and is not the initial segment `range (n + 1)`, then it contains an index at
least `n + 1`, and its product is at most `(∏ i ∈ range n, f i) * f (n + 1)`
(`Finset.prod_le_prod_range_mul_of_not_subset`). For a strictly decreasing positive sequence the
right-hand side is strictly smaller than the product over `range (n + 1)`, which gives an explicit
gap between the initial segment and every other set of the same size. This is how a dominant term
is singled out among the products of `n` entries of a decreasing sequence of norms.
-/

public section

namespace Finset

variable {R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R] [PosMulMono R]
  {f : ℕ → R}

/-- **Products along a count domination.** For a nonnegative antitone sequence `f`, let `s` and
`t` be finite sets of indices of the same size such that, below every threshold `k`, `s` has at
most as many indices as `t`. Then the product of `f` over `s` is at most its product over `t`. -/
theorem prod_le_prod_of_card_filter_lt_le (hf₀ : ∀ i, 0 ≤ f i) (hf : Antitone f)
    {s t : Finset ℕ} (hst : #s = #t) (h : ∀ k, #{i ∈ s | i < k} ≤ #{i ∈ t | i < k}) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  have := PosMulMono.toMulPosMono (α := R)
  induction hn : #s generalizing s t with
  | zero => rw [card_eq_zero.1 hn, card_eq_zero.1 (by omega : #t = 0)]
  | succ n ih =>
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ∀ i ∈ s, i ≤ a :=
      ⟨s.max' (card_pos.1 (by omega)), s.max'_mem _, s.le_max'⟩
    obtain ⟨b, hbt, hb⟩ : ∃ b ∈ t, ∀ i ∈ t, i ≤ b :=
      ⟨t.max' (card_pos.1 (by omega)), t.max'_mem _, t.le_max'⟩
    -- The largest index of `s` is at least the largest index of `t`: otherwise all of `s`, but
    -- not all of `t`, lies below `b`.
    have hba : b ≤ a := by
      by_contra! hab
      have h₁ : {i ∈ s | i < b} = s := filter_true_of_mem fun i hi ↦ (ha i hi).trans_lt hab
      have h₂ : #{i ∈ t | i < b} < #t := card_lt_card (filter_ssubset.2 ⟨b, hbt, lt_irrefl b⟩)
      have := h b
      rw [h₁] at this
      omega
    have herase (k : ℕ) : #{i ∈ s.erase a | i < k} ≤ #{i ∈ t.erase b | i < k} := by
      have hk := h k
      rw [filter_erase, filter_erase]
      by_cases hak : a < k
      · have has' : a ∈ {i ∈ s | i < k} := mem_filter.2 ⟨has, hak⟩
        have hbt' : b ∈ {i ∈ t | i < k} := mem_filter.2 ⟨hbt, hba.trans_lt hak⟩
        rw [card_erase_of_mem has', card_erase_of_mem hbt']
        omega
      have has' : a ∉ {i ∈ s | i < k} := fun hm ↦ hak (mem_filter.1 hm).2
      rw [erase_eq_of_notMem has']
      by_cases hbk : b < k
      · -- All of `t`, but not all of `s`, lies below `k`.
        have h₁ : #{i ∈ s | i < k} < #s := card_lt_card (filter_ssubset.2 ⟨a, has, hak⟩)
        have h₂ : {i ∈ t | i < k} = t := filter_true_of_mem fun i hi ↦ (hb i hi).trans_lt hbk
        have hbt' : b ∈ {i ∈ t | i < k} := mem_filter.2 ⟨hbt, hbk⟩
        rw [card_erase_of_mem hbt', h₂]
        omega
      · have hbt' : b ∉ {i ∈ t | i < k} := fun hm ↦ hbk (mem_filter.1 hm).2
        rwa [erase_eq_of_notMem hbt']
    rw [← mul_prod_erase s f has, ← mul_prod_erase t f hbt]
    refine mul_le_mul (hf hba) (ih ?_ herase ?_) (prod_nonneg fun i _ ↦ hf₀ i) (hf₀ b)
    · rw [card_erase_of_mem has, card_erase_of_mem hbt, hst]
    · rw [card_erase_of_mem has, hn, Nat.add_sub_cancel]

/-- For a nonnegative antitone sequence `f`, the product of `f` over a finite set `s` of indices
is at most its product over the initial segment `range #s` of the same size. -/
theorem prod_le_prod_range_card (hf₀ : ∀ i, 0 ≤ f i) (hf : Antitone f) (s : Finset ℕ) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ range #s, f i := by
  refine prod_le_prod_of_card_filter_lt_le hf₀ hf (card_range _).symm fun k ↦ ?_
  have hk : {i ∈ range #s | i < k} = range (min #s k) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [hk, card_range]
  exact le_min (card_filter_le _ _)
    ((card_le_card fun i hi ↦ mem_range.2 (mem_filter.1 hi).2).trans_eq (card_range k))

/-- For a nonnegative antitone sequence `f`, a set `s` of `n + 1` indices that is not contained in
the initial segment `range (n + 1)` has product at most `(∏ i ∈ range n, f i) * f (n + 1)`. -/
theorem prod_le_prod_range_mul_of_not_subset (hf₀ : ∀ i, 0 ≤ f i) (hf : Antitone f)
    {s : Finset ℕ} {n : ℕ} (hs : #s = n + 1) (hsub : ¬s ⊆ range (n + 1)) :
    ∏ i ∈ s, f i ≤ (∏ i ∈ range n, f i) * f (n + 1) := by
  have := PosMulMono.toMulPosMono (α := R)
  obtain ⟨m, hms, hm⟩ := not_subset.1 hsub
  rw [mem_range, not_lt] at hm
  rw [← mul_prod_erase s f hms, mul_comm]
  have herase := prod_le_prod_range_card hf₀ hf (s.erase m)
  rw [card_erase_of_mem hms, hs, Nat.add_sub_cancel] at herase
  exact mul_le_mul herase (hf hm) (hf₀ m) (prod_nonneg fun i _ ↦ hf₀ i)

end Finset
