/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Geometric tail and near-pair truncation bounds for partner-minimum sums

For an index type `Φ`, a partner map `pr : ℕ → Φ → Φ`, an active-exponent predicate `I : ℕ → Prop`,
a nonnegative weight function `w : Φ → ℝ`, and a real base `p`, the `e`-th partner-minimum term at
`τ` is `min (w τ / p ^ e) (w (pr e τ))` when `I e` holds and `0` otherwise.

When `w ≤ M` globally, `w ≤ a` outside a distinguished set `B : Set Φ`, and `2 ≤ p`, we bound the
tail from `n` onwards by `2 * M / p ^ n`, bound every non-near-pair term by `a`, and combine them
into a total upper bound for `∑' e, partnerMinTerm`.

## Main definitions and results

* `TauCeti.partnerMinTerm`: the `e`-th partner-minimum term at `τ`.
* `TauCeti.summable_partnerMinTerm`: summability of `partnerMinTerm` for `1 < p`.
* `TauCeti.tsum_partnerMinTerm_add_le`: geometric tail bound `∑' e, term (e + n) ≤ 2 * M / p ^ n`.
* `TauCeti.partnerMinTerm_le_of_not_nearPair`: non-near-pair terms are at most `a`.
* `TauCeti.tsum_partnerMinTerm_le`: combined upper bound with at most one near pair below `n`.

## Provenance

Adapted from `New.Data.partnerMinTerm`, `New.Data.tsum_partnerMinTerm_add_le`,
`New.Data.partnerMinTerm_le_of_not_isNearPair`, and `New.Data.partnerMinSum_le` in
`src/New/Derivatives/Sharpness/NearPairs.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Finset

section PartnerMin

variable {Φ : Type*} (I : ℕ → Prop) [DecidablePred I] (pr : ℕ → Φ → Φ) (w : Φ → ℝ) (p : ℝ)

/-- The `e`-th partner-minimum term at `τ`: `min (w τ / p ^ e) (w (pr e τ))` if `I e`, else `0`. -/
noncomputable def partnerMinTerm (τ : Φ) (e : ℕ) : ℝ :=
  if I e then min (w τ / p ^ e) (w (pr e τ)) else 0

/-- For `1 < p` and a nonnegative weight function `w`, `partnerMinTerm` is summable in `e`. -/
theorem summable_partnerMinTerm {p : ℝ} (hp : 1 < p) (hw : ∀ σ, 0 ≤ w σ) (τ : Φ) :
    Summable (partnerMinTerm I pr w p τ) := by
  refine ((summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp)).mul_left
    (w τ)).of_nonneg_of_le (fun e ↦ ?_) fun e ↦ ?_
  · unfold partnerMinTerm
    split_ifs
    · exact le_min (div_nonneg (hw τ) (by positivity)) (hw _)
    · exact le_rfl
  · unfold partnerMinTerm
    rw [inv_pow, ← div_eq_mul_inv]
    split_ifs
    · exact min_le_left _ _
    · exact div_nonneg (hw τ) (by positivity)

/-- For `2 ≤ p` and `0 ≤ w ≤ M`, the tail of `partnerMinTerm` starting at `n` is at most
`2 * M / p ^ n`. -/
theorem tsum_partnerMinTerm_add_le {p M : ℝ} (hp : 2 ≤ p) (hw : ∀ σ, 0 ≤ w σ)
    (hwM : ∀ σ, w σ ≤ M) (τ : Φ) (n : ℕ) :
    ∑' e : ℕ, partnerMinTerm I pr w p τ (e + n) ≤ 2 * M / p ^ n := by
  have hM : 0 ≤ M := (hw τ).trans (hwM τ)
  have h_geom : HasSum (fun e : ℕ ↦ (M / p ^ n) * (2 : ℝ)⁻¹ ^ e) (2 * M / p ^ n) := by
    have h := (hasSum_geometric_of_lt_one (by positivity) (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left
      (M / p ^ n)
    convert h using 1
    ring
  refine hasSum_le (fun e ↦ ?_)
    (((summable_nat_add_iff n).mpr (summable_partnerMinTerm I pr w (by linarith) hw τ)).hasSum)
    h_geom
  unfold partnerMinTerm
  split_ifs
  · refine (min_le_left _ _).trans ?_
    rw [pow_add, mul_comm (p ^ e), ← div_div, div_eq_mul_inv (w τ / p ^ n), ← inv_pow]
    have h_inv : p⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by positivity) hp
    gcongr
    exact hwM τ
  · positivity

/-- If `w ≤ a` outside `B` and `(τ, e)` is not a near pair (i.e. not `I e ∧ τ ∈ B ∧ pr e τ ∈ B`),
then `partnerMinTerm I pr w p τ e ≤ a`. -/
theorem partnerMinTerm_le_of_not_nearPair {p a : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a)
    (hw : ∀ σ, 0 ≤ w σ) {B : Set Φ} (hwB : ∀ σ, σ ∉ B → w σ ≤ a) {τ : Φ} {e : ℕ}
    (h_not : ¬(I e ∧ τ ∈ B ∧ pr e τ ∈ B)) :
    partnerMinTerm I pr w p τ e ≤ a := by
  unfold partnerMinTerm
  split_ifs with hI
  · by_cases hτ : τ ∈ B
    · have hpr : pr e τ ∉ B := fun h ↦ h_not ⟨hI, hτ, h⟩
      exact (min_le_right _ _).trans (hwB _ hpr)
    · exact (min_le_left _ _).trans
        ((div_le_self (hw τ) (one_le_pow₀ hp)).trans (hwB τ hτ))
  · exact ha

/-- Combined truncation bound: if `2 ≤ p`, `0 ≤ w ≤ M`, `w ≤ a` outside `B`, and among `e < n`
a near pair occurs only at `e₀` with `w τ / p ^ e₀ ≤ c`, then
`∑' e, partnerMinTerm I pr w p τ e ≤ c + n * a + 2 * M / p ^ n`. -/
theorem tsum_partnerMinTerm_le {p M a c : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hw : ∀ σ, 0 ≤ w σ) (hwM : ∀ σ, w σ ≤ M) {B : Set Φ} (hwB : ∀ σ, σ ∉ B → w σ ≤ a)
    {τ : Φ} {n e₀ : ℕ}
    (h_near : ∀ e < n, I e ∧ τ ∈ B ∧ pr e τ ∈ B → e = e₀ ∧ w τ / p ^ e ≤ c) :
    ∑' e : ℕ, partnerMinTerm I pr w p τ e ≤ c + n * a + 2 * M / p ^ n := by
  have h_sum := (summable_partnerMinTerm I pr w (p := p) (by linarith) hw τ).sum_add_tsum_nat_add n
  rw [← h_sum]
  have h_head : ∑ e ∈ range n, partnerMinTerm I pr w p τ e ≤ c + n * a := by
    have h_term (e : ℕ) (he : e ∈ range n) :
        partnerMinTerm I pr w p τ e ≤ (if e = e₀ then c else 0) + a := by
      by_cases hnp : I e ∧ τ ∈ B ∧ pr e τ ∈ B
      · obtain ⟨rfl, hle⟩ := h_near e (mem_range.mp he) hnp
        rw [ite_eq_left rfl]
        have : partnerMinTerm I pr w p τ e ≤ w τ / p ^ e := by
          unfold partnerMinTerm; rw [ite_eq_left hnp.left]; exact min_le_left _ _
        linarith
      · have := partnerMinTerm_le_of_not_nearPair I pr w (p := p) (by linarith) ha hw hwB hnp
        have : (0 : ℝ) ≤ if e = e₀ then c else 0 := by split_ifs <;> linarith
        linarith
    calc ∑ e ∈ range n, partnerMinTerm I pr w p τ e
        ≤ ∑ e ∈ range n, ((if e = e₀ then c else 0) + a) := sum_le_sum h_term
      _ = (∑ e ∈ range n, if e = e₀ then c else 0) + n * a := by
          simp [sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ c + n * a := by
          have : ∑ e ∈ range n, (if e = e₀ then c else 0) ≤ c := by
            by_cases h : e₀ ∈ range n <;> simp [h, hc]
          linarith
  linarith [tsum_partnerMinTerm_add_le I pr w hp hw hwM τ n]

end PartnerMin

end TauCeti
