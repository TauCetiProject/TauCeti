/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Products of antitone sequences over finite sets of indices

For a nonnegative antitone sequence `f : ℕ → R` in an ordered commutative semiring, the product
of `f` over a finite set `s` of indices is largest when `s` is an initial segment: it is at most
the product over `range #s` (`Finset.prod_le_prod_range_card`). If `s` has `n + 1` elements and
is not the initial segment `range (n + 1)`, then it contains an index at least `n + 1`, and its
product is at most `(∏ i ∈ range n, f i) * f (n + 1)`
(`Finset.prod_le_prod_range_mul_of_not_subset`). For a strictly decreasing positive sequence the
right-hand side is strictly smaller than the product over `range (n + 1)`, which gives an explicit
gap between the initial segment and every other set of the same size. This is how a dominant term
is singled out among the products of `n` entries of a decreasing sequence of norms.
-/

public section

namespace Finset

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f : ℕ → R}

/-- For a nonnegative antitone sequence `f`, the product of `f` over a finite set `s` of indices
is at most its product over the initial segment `range #s` of the same size. -/
theorem prod_le_prod_range_card (hf₀ : ∀ i, 0 ≤ f i) (hf : Antitone f) (s : Finset ℕ) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ range #s, f i := by
  induction h : #s generalizing s with
  | zero => simp [card_eq_zero.1 h]
  | succ n ih =>
    have hne : s.Nonempty := card_pos.1 (h ▸ n.succ_pos)
    -- The largest element `m` of `s` is at least `n`, since `s ⊆ range (m + 1)`.
    set m := s.max' hne
    have hm : n ≤ m := by
      have hsub : s ⊆ range (m + 1) := fun i hi ↦ mem_range.2 (Nat.lt_succ_of_le (s.le_max' i hi))
      have := card_le_card hsub
      rw [h, card_range] at this
      omega
    rw [← mul_prod_erase s f (s.max'_mem hne), prod_range_succ, mul_comm (∏ i ∈ range n, f i)]
    have herase : #(s.erase m) = n := by
      rw [card_erase_of_mem (s.max'_mem hne), h, Nat.add_sub_cancel]
    exact mul_le_mul (hf hm) (ih _ herase) (prod_nonneg fun i _ ↦ hf₀ i) (hf₀ n)

/-- For a nonnegative antitone sequence `f`, a set `s` of `n + 1` indices that is not contained in
the initial segment `range (n + 1)` has product at most `(∏ i ∈ range n, f i) * f (n + 1)`. -/
theorem prod_le_prod_range_mul_of_not_subset (hf₀ : ∀ i, 0 ≤ f i) (hf : Antitone f)
    {s : Finset ℕ} {n : ℕ} (hs : #s = n + 1) (hsub : ¬s ⊆ range (n + 1)) :
    ∏ i ∈ s, f i ≤ (∏ i ∈ range n, f i) * f (n + 1) := by
  obtain ⟨m, hms, hm⟩ := not_subset.1 hsub
  rw [mem_range, not_lt] at hm
  rw [← mul_prod_erase s f hms, mul_comm]
  have herase := prod_le_prod_range_card hf₀ hf (s.erase m)
  rw [card_erase_of_mem hms, hs, Nat.add_sub_cancel] at herase
  exact mul_le_mul herase (hf hm) (hf₀ m) (prod_nonneg fun i _ ↦ hf₀ i)

end Finset
