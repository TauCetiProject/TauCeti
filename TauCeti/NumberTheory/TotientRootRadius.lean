/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Order.Filter.AtTopBot.Defs

import Mathlib.Analysis.PSeries
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Order.Interval.Finset.Nat

/-!
# Totient root radii `1 / φ(ℓ ^ h)` and harmonic divergence

For a prime `ℓ` and exponent `h : ℕ`, the radius `TauCeti.totientRootRadius ℓ h = (φ(ℓ ^ h))⁻¹`
is the normalised `ℓ`-adic valuation `v(ζ - 1)` of a primitive `ℓ ^ h`-th root of unity `ζ`. For
`h ≥ 1`, these radii are pairwise distinct (`TauCeti.totientRootRadius_injOn`) and tend to `0`, so
they are eventually at most any positive rational `ρ` (`TauCeti.eventually_totientRootRadius_le`).

Let `TauCeti.totientRadiusExponents ℓ ρ h₀` be the finite set of exponents `1 ≤ h ≤ h₀` with
`totientRootRadius ℓ h ≤ ρ`. Because the harmonic series diverges, for any `ρ > 0`, `δ > 0`, and
`B : ℝ≥0`, there exists `h₀ : ℕ` such that `B < δ * ∑ h ∈ totientRadiusExponents ℓ ρ h₀, (h + 1)⁻¹`
(`TauCeti.exists_lt_mul_sum_totientRadiusExponents`).

## Main results

* `TauCeti.totientRootRadius`: the rational radius `(Nat.totient (ℓ ^ h) : ℚ≥0)⁻¹`.
* `TauCeti.totientRadiusExponents`: the finset `{h ∈ Icc 1 h₀ | totientRootRadius ℓ h ≤ ρ}`.
* `TauCeti.totientRootRadius_injOn`: injectivity of `h ↦ totientRootRadius ℓ h` on `Set.Ici 1`.
* `TauCeti.eventually_totientRootRadius_le`: `totientRootRadius ℓ h ≤ ρ` for all large `h`.
* `TauCeti.exists_lt_mul_sum_totientRadiusExponents`: the tail harmonic sum over
  `totientRadiusExponents ℓ ρ h₀` exceeds `B / δ` for large `h₀`.

## Provenance

Adapted from grh-lean (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Congruences/Selmer/RootsOfUnity.lean`, declarations `New.Selmer.rootRadius`,
`New.Selmer.rootRadius_injOn`, `New.Selmer.eventually_rootRadius_le`,
`New.Selmer.radiusExponents`, and `New.Selmer.exists_lt_mul_sum_radiusExponents`, taking an
explicit `hℓ : ℓ.Prime` hypothesis instead of a `Fact` class.
-/

public section

open scoped NNReal NNRat

namespace TauCeti

/-- The rational radius `1 / φ(ℓ ^ h)`, equal to `v(ζ - 1)` for a primitive `ℓ ^ h`-th root of
unity `ζ` when `ℓ` is prime and `h ≥ 1`. -/
def totientRootRadius (ℓ h : ℕ) : ℚ≥0 := (Nat.totient (ℓ ^ h) : ℚ≥0)⁻¹

/-- The exponents `1 ≤ h ≤ h₀` whose totient root radius `1 / φ(ℓ ^ h)` is at most `ρ`. -/
def totientRadiusExponents (ℓ : ℕ) (ρ : ℚ≥0) (h₀ : ℕ) : Finset ℕ :=
  (Finset.Icc 1 h₀).filter fun h ↦ totientRootRadius ℓ h ≤ ρ

/-- For a prime `ℓ`, the radii `1 / φ(ℓ ^ h)` with `h ≥ 1` are pairwise distinct. -/
theorem totientRootRadius_injOn {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Set.InjOn (totientRootRadius ℓ) (Set.Ici 1) := by
  have hmono : StrictMono fun k : ℕ ↦ Nat.totient (ℓ ^ (k + 1)) := by
    simp only [Nat.totient_prime_pow_succ hℓ]
    exact (pow_right_strictMono₀ hℓ.one_lt).mul_const (Nat.sub_pos_of_lt hℓ.one_lt)
  intro h hh h' hh' heq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hh'
  exact congrArg (· + 1) (hmono.injective (by simpa [totientRootRadius] using heq))

/-- For a prime `ℓ` and positive `ρ : ℚ≥0`, `totientRootRadius ℓ h ≤ ρ` holds for all large `h`. -/
theorem eventually_totientRootRadius_le {ℓ : ℕ} (hℓ : ℓ.Prime) {ρ : ℚ≥0} (hρ : 0 < ρ) :
    ∀ᶠ h : ℕ in Filter.atTop, totientRootRadius ℓ h ≤ ρ := by
  have hmono : StrictMono fun k : ℕ ↦ Nat.totient (ℓ ^ (k + 1)) := by
    simp only [Nat.totient_prime_pow_succ hℓ]
    exact (pow_right_strictMono₀ hℓ.one_lt).mul_const (Nat.sub_pos_of_lt hℓ.one_lt)
  filter_upwards [Filter.eventually_ge_atTop (⌈ρ⁻¹⌉₊ + 1)] with h hh
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right hh)
  have htot : ⌈ρ⁻¹⌉₊ ≤ Nat.totient (ℓ ^ (k + 1)) :=
    (Nat.le_of_succ_le_succ hh).trans hmono.le_apply
  exact inv_le_of_inv_le₀ hρ ((Nat.le_ceil _).trans (Nat.cast_le.mpr htot))

/-- For a prime `ℓ`, `ρ > 0`, `δ > 0`, and `B : ℝ≥0`, there exists `h₀ : ℕ` such that
`B < δ * ∑ h ∈ totientRadiusExponents ℓ ρ h₀, (h + 1)⁻¹`. -/
theorem exists_lt_mul_sum_totientRadiusExponents {ℓ : ℕ} (hℓ : ℓ.Prime) {ρ : ℚ≥0} {δ : ℝ≥0}
    (hρ : 0 < ρ) (B : ℝ≥0) (hδ : 0 < δ) :
    ∃ h₀ : ℕ, B < δ * ∑ h ∈ totientRadiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ h ≥ N, 1 ≤ h ∧ totientRootRadius ℓ h ≤ ρ :=
    Filter.eventually_atTop.mp
      ((Filter.eventually_ge_atTop 1).and (eventually_totientRootRadius_le hℓ hρ))
  have hdiv : ∀ᶠ n : ℕ in Filter.atTop,
      (B : ℝ) / δ + ∑ h ∈ Finset.range N, 1 / ((h : ℝ) + 1) <
        ∑ h ∈ Finset.range n, 1 / ((h : ℝ) + 1) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop _
  obtain ⟨h₀, hlarge, hNh₀⟩ := (hdiv.and (Filter.eventually_ge_atTop N)).exists
  have htail : B / δ < ∑ h ∈ Finset.Ico N h₀, ((h : ℝ≥0) + 1)⁻¹ := by
    rw [← Finset.sum_range_add_sum_Ico _ hNh₀, add_comm, add_lt_add_iff_left] at hlarge
    simpa [← NNReal.coe_lt_coe] using hlarge
  have hsub : Finset.Ico N h₀ ⊆ totientRadiusExponents ℓ ρ h₀ := fun h hh ↦ by
    obtain ⟨hNh, hh₀⟩ := Finset.mem_Ico.mp hh
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(hN h hNh).left, hh₀.le⟩, (hN h hNh).right⟩
  exact ⟨h₀, (div_lt_iff₀' hδ).mp (htail.trans_le (Finset.sum_le_sum_of_subset hsub))⟩

end TauCeti
