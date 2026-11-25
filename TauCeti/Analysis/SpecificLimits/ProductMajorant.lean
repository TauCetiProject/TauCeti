/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric decay from product majorants

Let `r : ι → ℝ` be a nonnegative family, and let `x` be a real number bounded by every
nonnegative bound for the products `∏ i ∈ s, r i` over the `n`-element finite sets `s`. Such
numbers arise as norms of the coefficients of Fredholm determinants and resolvents, which are
controlled by products of row bounds. This file turns that hypothesis into tail estimates.

## Main results

* `TauCeti.exists_geometric_bound_of_tendsto_cofinite`: after rescaling by any real `ρ`, a null
  family is bounded by some `B ≥ 1`, and by any prescribed `q ∈ (0, 1)` off a finite set `T`.
* `TauCeti.mul_pow_le_of_forall_prod_le`: if `ρ * r i ≤ q` off a finite set `T`, with `0 ≤ ρ`,
  `0 ≤ q` and `1 ≤ B`, and `ρ * r i ≤ B` everywhere, then `x * ρ ^ n ≤ B ^ #T * q ^ (n - #T)`.
* `TauCeti.tendsto_mul_pow_of_forall_prod_le`: if `r` tends to zero along the cofinite filter,
  then `x n * |ρ| ^ n` tends to zero for every real `ρ`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- A null family admits a uniform bound and a finite exceptional set outside which its rescaling
is at most any prescribed `q ∈ (0, 1)`. The associated geometric tail tends to zero. -/
theorem exists_geometric_bound_of_tendsto_cofinite {ι : Type*}
    {r : ι → ℝ} (hr : Tendsto r cofinite (𝓝 0)) (ρ : ℝ) {q : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ (T : Finset ι) (B : ℝ), 1 ≤ B ∧ (∀ i ∉ T, ρ * r i ≤ q) ∧
      (∀ i, ρ * r i ≤ B) ∧
      Tendsto (fun n : ℕ ↦ B ^ T.card * q ^ (n - T.card)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := (hr.const_mul ρ).bddAbove_range_of_cofinite
  have hfinite : {i | ¬ρ * r i ≤ q}.Finite := eventually_cofinite.mp <|
    (hr.const_mul ρ).eventually (ge_mem_nhds (by simpa using hq₀))
  let T := hfinite.toFinset
  let B := max 1 M
  refine ⟨T, B, le_max_left _ _, fun i hi ↦ ?_, fun i ↦ ?_, ?_⟩
  · simpa [T] using hi
  · exact (hM ⟨i, rfl⟩).trans (le_max_right _ _)
  · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁).comp
      (tendsto_sub_atTop_nat T.card)).const_mul (B ^ T.card)

/-- **Tail bound from product majorants.** Let `r` be nonnegative, and let `x` be bounded by
every nonnegative bound for the products `∏ i ∈ s, r i` over the `n`-element sets `s`. If
`0 ≤ ρ`, `0 ≤ q`, `1 ≤ B`, and `T` is a finite set of indices with `ρ * r i ≤ q` off `T` and
`ρ * r i ≤ B` everywhere, then `x * ρ ^ n ≤ B ^ #T * q ^ (n - #T)`, with truncated subtraction in
the exponent. This is the estimate behind the entirety of Fredholm determinants and resolvents. -/
theorem mul_pow_le_of_forall_prod_le {ι : Type*} {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {n : ℕ}
    {x : ℝ} (hx : ∀ c, 0 ≤ c → (∀ s : Finset ι, s.card = n → ∏ i ∈ s, r i ≤ c) → x ≤ c)
    {ρ q B : ℝ} (hρ : 0 ≤ ρ) (hq₀ : 0 ≤ q) (hB : 1 ≤ B) (T : Finset ι)
    (hT : ∀ i ∉ T, ρ * r i ≤ q) (hrB : ∀ i, ρ * r i ≤ B) :
    x * ρ ^ n ≤ B ^ T.card * q ^ (n - T.card) := by
  classical
  -- If `ρ ^ n = 0` the left side vanishes; otherwise divide by `ρ ^ n > 0`.
  rcases (pow_nonneg hρ n).eq_or_lt with hρn | hρn
  · rw [← hρn, mul_zero]
    positivity
  rw [mul_comm x, ← le_div_iff₀' hρn]
  refine hx _ (by positivity) fun s hs ↦ ?_
  rw [le_div_iff₀' hρn, ← hs, ← prod_const ρ, ← prod_mul_distrib]
  -- Each factor is at most `B` on `T`, and at most `min q B` off `T`.
  have hprod : ∏ i ∈ s, ρ * r i ≤ ∏ i ∈ s, if i ∈ T then B else min q B :=
    prod_le_prod₀ (fun i _ ↦ mul_nonneg hρ (hr i)) fun i _ ↦ by
      split_ifs with hi
      exacts [hrB i, le_min (hT i hi) (hrB i)]
  rw [prod_ite, prod_const, prod_const] at hprod
  refine hprod.trans ?_
  -- Of the `k` factors in `T` and the `d` factors off `T`, write `d = e + (#s - #T)` with
  -- `k + e ≤ #T`: the `e` factors are bounded by `B` and the remaining ones by `q`.
  have hcard := card_filter_add_card_filter_not (s := s) (· ∈ T)
  have hk : (s.filter (· ∈ T)).card ≤ T.card := card_le_card fun i hi ↦ (mem_filter.mp hi).2
  generalize (s.filter (· ∈ T)).card = k at hcard hk
  generalize (s.filter (· ∉ T)).card = d at hcard
  obtain ⟨e, rfl, he⟩ : ∃ e, d = e + (s.card - T.card) ∧ k + e ≤ T.card :=
    ⟨d - (s.card - T.card), by omega, by omega⟩
  calc B ^ k * min q B ^ (e + (s.card - T.card))
      ≤ B ^ k * (B ^ e * q ^ (s.card - T.card)) := by
        rw [pow_add]
        gcongr
        exacts [min_le_right _ _, min_le_left _ _]
    _ = B ^ (k + e) * q ^ (s.card - T.card) := by ring
    _ ≤ B ^ T.card * q ^ (s.card - T.card) := by gcongr

/-- **Geometric decay from null product majorants.** Let `r` tend to zero along the cofinite
filter, and let `x n ≥ 0` be bounded by every nonnegative bound for the products `∏ i ∈ s, r i`
over the `n`-element sets `s`. Then `x n * |ρ| ^ n` tends to zero for every real `ρ`. -/
theorem tendsto_mul_pow_of_forall_prod_le {ι : Type*} {r : ι → ℝ}
    (hr : Tendsto r cofinite (𝓝 0)) {x : ℕ → ℝ} (hx₀ : ∀ n, 0 ≤ x n)
    (hx : ∀ n c, 0 ≤ c → (∀ s : Finset ι, s.card = n → ∏ i ∈ s, r i ≤ c) → x n ≤ c) (ρ : ℝ) :
    Tendsto (fun n ↦ x n * |ρ| ^ n) atTop (𝓝 0) := by
  have hr' : Tendsto (fun i ↦ |r i|) cofinite (𝓝 0) := by simpa using hr.abs
  obtain ⟨T, B, hB, hT, hrB, hlim⟩ :=
    exists_geometric_bound_of_tendsto_cofinite hr' (|ρ| + 1)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  refine squeeze_zero (fun n ↦ by have := hx₀ n; positivity) (fun n ↦ ?_) hlim
  have hx' : ∀ c, 0 ≤ c → (∀ s : Finset ι, s.card = n → ∏ i ∈ s, |r i| ≤ c) → x n ≤ c :=
    fun c hc hs ↦ hx n c hc fun s hcard ↦
      (le_abs_self _).trans ((Finset.abs_prod _ _).trans_le (hs s hcard))
  have := hx₀ n -- discharges the side goal `0 ≤ x n` of `gcongr`
  calc x n * |ρ| ^ n ≤ x n * (|ρ| + 1) ^ n := by gcongr; linarith
    _ ≤ _ := mul_pow_le_of_forall_prod_le (fun i ↦ abs_nonneg (r i)) hx' (by positivity)
      (by norm_num) hB T hT hrB

end TauCeti
