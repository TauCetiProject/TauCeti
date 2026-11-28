/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Column multiplicities and bounds for regular integer parameters

A finite injective family of integers `v : ι → ℤ` bounded below by `g` can be encoded by column
multiplicities `κ : ℕ → ℕ` (recording the gaps between consecutive sorted values, minus one)
agreeing with any prescribed function `f` above `#S`. Applying this to parity-constrained doubled
Harish-Chandra parameters `l : n → ℤ` produces column multiplicities realising `l` with arbitrary
tail above `card n`, and bounding the parameter entries by `β` controls both the total number of
boxes below height `N` and the determinant shift `e`.

## Main results

* `TauCeti.exists_eq_add_card_add_sum_Ioc`: encodes an injective integer family on a finite set
  `S` by column multiplicities `κ` matching a prescribed tail `f` above `#S`.
* `TauCeti.exists_doubled_hcParam_of_parity`: realises an injective parity-constrained family
  `l : n → ℤ` bounded below via `e₀` by column multiplicities `κ` matching `κ₀` above `card n`.
* `TauCeti.sum_Ioo_le_mul_of_abs_hcParam_le`: a uniform bound `β` on the doubled Harish-Chandra
  parameter bounds the total number of boxes `∑ p < N, ∑ k ∈ Ioo p N, κ k` by `N * β`.
* `TauCeti.natAbs_le_of_abs_hcParam_le`: for `0 < N`, the same bound gives `e.natAbs ≤ β`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Determinant/AuxiliaryForms/RegularParameters.lean`
(`New.Exchange.exists_eq_add_card_add_sum_Ioc`, `New.Exchange.exists_isHCParam_of_le`,
`New.Exchange.boxes_le_card_mul_of_isHCParam`, `New.Exchange.natAbs_le_of_isHCParam`).
-/

public section

open Finset Fintype

namespace TauCeti

/-- Let `v : ι → ℤ` be injective and bounded below by `g` on a finite set `S`. There exist column
multiplicities `κ : ℕ → ℕ`, equal to a given `f` above `#S`, such that each `v i` (`i ∈ S`) equals
`g + (#S + ∑ k ∈ Ioc p #S, κ k : ℕ) - p - 1` for some position `p < #S`. -/
theorem exists_eq_add_card_add_sum_Ioc {ι : Type*} {v : ι → ℤ} (hv : v.Injective) (S : Finset ι)
    (g : ℤ) (f : ℕ → ℕ) (hg : ∀ i ∈ S, g ≤ v i) :
    ∃ κ : ℕ → ℕ, (∀ k > #S, κ k = f k) ∧
      ∀ i ∈ S, ∃ p < #S, v i + p + 1 = g + (#S + ∑ k ∈ Ioc p #S, κ k : ℕ) := by
  classical
  induction hcard : #S generalizing S g f with
  | zero =>
    rw [Finset.card_eq_zero] at hcard; subst hcard
    exact ⟨f, fun _ _ ↦ rfl, by simp⟩
  | succ m ih =>
    obtain ⟨a, ha, hmin⟩ := S.exists_min_image v (card_pos.mp (by omega))
    let S' := S.erase a
    have hS'_card : #S' = m := by rw [card_erase_of_mem ha, hcard, Nat.add_sub_cancel]
    have hS'_ge : ∀ i ∈ S', v a + 1 ≤ v i := fun i hi ↦ by
      have hne : v a ≠ v i := hv.ne (ne_of_mem_erase hi).symm
      have hle : v a ≤ v i := hmin i (mem_of_mem_erase hi)
      omega
    obtain ⟨κ, h_high, h_pos⟩ :=
      ih S' (v a + 1) (Function.update f (m + 1) (v a - g).toNat) hS'_ge hS'_card
    have hκ : (κ (m + 1) : ℤ) = v a - g := by
      rw [h_high (m + 1) (by omega), Function.update_self,
        Int.toNat_of_nonneg (by linarith [hg a ha])]
    refine ⟨κ, fun k hk ↦ ?_, fun i hi ↦ ?_⟩
    · rw [h_high k (by omega), Function.update_of_ne (by omega)]
    · by_cases hia : i = a
      · subst hia
        refine ⟨m, by omega, ?_⟩
        rw [Nat.Ioc_succ_singleton, sum_singleton]
        push_cast
        linarith
      · obtain ⟨p, hp_lt, hp_eq⟩ := h_pos i (mem_erase.mpr ⟨hia, hi⟩)
        refine ⟨p, by omega, ?_⟩
        have hsum : ∑ k ∈ Ioc p (m + 1), κ k = ∑ k ∈ Ioc p m, κ k + κ (m + 1) := by
          rw [← sum_Ioc_succ_top (by omega)]
        rw [hsum]
        push_cast at hp_eq ⊢
        linarith

/-- Let `l : n → ℤ` be injective with every `l i` having the parity of `card n - 1`, and let
`e₀ ≤ l i / 2 + card n / 2` for all `i`. For any prescribed tail `κ₀ : ℕ → ℕ`, there exist column
multiplicities `κ : ℕ → ℕ` agreeing with `κ₀` above `card n` such that every `l i` equals
`2 * (e₀ + κ (card n) + ∑ k ∈ Ioo p (card n), κ k) + card n - 1 - 2 * p` for some `p < card n`. -/
theorem exists_doubled_hcParam_of_parity {n : Type*} [Fintype n] (κ₀ : ℕ → ℕ) {e₀ : ℤ}
    {l : n → ℤ} (hl_inj : l.Injective) (hpar : ∀ i : n, (l i + Fintype.card n - 1) % 2 = 0)
    (he_le : ∀ i : n, e₀ ≤ l i / 2 + Fintype.card n / 2) :
    ∃ κ : ℕ → ℕ, (∀ k > Fintype.card n, κ k = κ₀ k) ∧
      ∀ i : n, ∃ p < Fintype.card n,
        l i = 2 * (e₀ + κ (Fintype.card n) + ∑ k ∈ Ioo p (Fintype.card n), κ k) +
          Fintype.card n - 1 - 2 * (p : ℤ) := by
  have h_half : Function.Injective fun i : n ↦ l i / 2 := fun i j hij ↦
    hl_inj (by dsimp at hij; have := hpar i; have := hpar j; omega)
  obtain ⟨κ, h_high, h_pos⟩ := exists_eq_add_card_add_sum_Ioc h_half univ
    (e₀ - Fintype.card n / 2) κ₀ fun i _ ↦ by have := he_le i; omega
  refine ⟨κ, by simpa using h_high, fun i ↦ ?_⟩
  obtain ⟨p, hp_lt, hp_eq⟩ := h_pos i (mem_univ i)
  rw [card_univ] at hp_lt hp_eq
  refine ⟨p, hp_lt, ?_⟩
  have h_split : ∑ k ∈ Ioo p (Fintype.card n), κ k + κ (Fintype.card n) =
      ∑ k ∈ Ioc p (Fintype.card n), κ k := sum_Ioo_add_eq_sum_Ioc hp_lt
  have hi_par := hpar i
  push_cast at hp_eq
  omega

/-- If every doubled Harish-Chandra parameter entry
`2 * (e + ∑ k ∈ Ioo p N, κ k) + N - 1 - 2 * p` (`p < N`) has absolute value at most `β`, then the
total number of boxes `∑ p ∈ range N, ∑ k ∈ Ioo p N, κ k` in columns of height below `N` is at
most `N * β`. -/
theorem sum_Ioo_le_mul_of_abs_hcParam_le {κ : ℕ → ℕ} {e : ℤ} {N β : ℕ}
    (hβ : ∀ p < N, |2 * (e + (∑ k ∈ Ioo p N, κ k : ℕ)) + (N : ℤ) - 1 - 2 * (p : ℤ)| ≤ β) :
    ∑ p ∈ range N, ∑ k ∈ Ioo p N, κ k ≤ N * β := by
  refine (sum_le_card_nsmul (range N) _ β fun p hp ↦ ?_).trans_eq (by simp)
  have hp_lt : p < N := mem_range.mp hp
  have h1 := abs_le.mp (hβ p hp_lt)
  have h2 := abs_le.mp (hβ (N - 1) (Nat.sub_one_lt_of_lt hp_lt))
  have hempty : Ioo (N - 1) N = ∅ := by
    ext k
    simp only [mem_Ioo, notMem_empty, iff_false]
    omega
  rw [hempty, Finset.sum_empty, Nat.cast_zero, add_zero] at h2
  omega

/-- For `0 < N`, if every doubled Harish-Chandra parameter entry
`2 * (e + ∑ k ∈ Ioo p N, κ k) + N - 1 - 2 * p` (`p < N`) has absolute value at most `β`, then the
determinant power satisfies `e.natAbs ≤ β`. -/
theorem natAbs_le_of_abs_hcParam_le {κ : ℕ → ℕ} {e : ℤ} {N β : ℕ} (hN : 0 < N)
    (hβ : ∀ p < N, |2 * (e + (∑ k ∈ Ioo p N, κ k : ℕ)) + (N : ℤ) - 1 - 2 * (p : ℤ)| ≤ β) :
    e.natAbs ≤ β := by
  have h_first := abs_le.mp (hβ 0 hN)
  have h_last := abs_le.mp (hβ (N - 1) (Nat.sub_one_lt hN.ne'))
  have hempty : Ioo (N - 1) N = ∅ := by
    ext k
    simp only [mem_Ioo, notMem_empty, iff_false]
    omega
  rw [hempty, Finset.sum_empty, Nat.cast_zero, add_zero] at h_last
  omega

end TauCeti
