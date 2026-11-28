/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Geometric and dyadic shell summation for Lebesgue integrals

When the support of a function `f : α → ℝ≥0∞` is covered by a countable family of shells `S i`
(`i : ℕ`) on which the restricted Lebesgue integral decays geometrically, the global integral is
bounded by the geometric series times the common envelope:

* `TauCeti.mul_lintegral_le_of_shells`: if `f.support ⊆ ⋃ i, S i` and
  `c * ∫⁻ x in S i, f x ∂μ ≤ r ^ i * B` for all `i : ℕ`, then
  `c * ∫⁻ x, f x ∂μ ≤ (1 - r)⁻¹ * B`.
* `TauCeti.lintegral_le_of_shells`: the `c = 1` case.
* `TauCeti.mul_lintegral_le_of_dyadic_shells`: the dyadic case `r = 2⁻¹`, giving
  `c * ∫⁻ x, f x ∂μ ≤ 2 * B`.
* `TauCeti.lintegral_le_of_dyadic_shells`: the `c = 1`, dyadic case `∫⁻ x, f x ∂μ ≤ 2 * B`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Spanning/Frames/Shells.lean`,
declaration `New.Floors.Gauge.lintegral_le_of_shells`, abstracted from `PlaceData`/`Gauge` to an
arbitrary measure space `(α, μ)` and arbitrary geometric ratio `r : ℝ≥0∞`.
-/

@[expose] public section

namespace TauCeti

open MeasureTheory ENNReal

/-- If `f.support ⊆ ⋃ i, S i` and `c * ∫⁻ x in S i, f x ∂μ ≤ r ^ i * B` for every `i : ℕ`, then
`c * ∫⁻ x, f x ∂μ ≤ (1 - r)⁻¹ * B`. -/
theorem mul_lintegral_le_of_shells {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {S : ℕ → Set α} {c r B : ℝ≥0∞} (h_cover : f.support ⊆ ⋃ i : ℕ, S i)
    (h_shell : ∀ i : ℕ, c * ∫⁻ x in S i, f x ∂μ ≤ r ^ i * B) :
    c * ∫⁻ x, f x ∂μ ≤ (1 - r)⁻¹ * B := by
  calc c * ∫⁻ x, f x ∂μ
      = c * ∫⁻ x in ⋃ i, S i, f x ∂μ := by
        rw [setLIntegral_eq_of_support_subset h_cover]
    _ ≤ c * ∑' i : ℕ, ∫⁻ x in S i, f x ∂μ :=
        mul_le_mul_right (lintegral_iUnion_le S f) c
    _ = ∑' i : ℕ, c * ∫⁻ x in S i, f x ∂μ := (ENNReal.tsum_mul_left).symm
    _ ≤ ∑' i : ℕ, r ^ i * B := tsum_le_tsum h_shell
    _ = (∑' i : ℕ, r ^ i) * B := ENNReal.tsum_mul_right
    _ = (1 - r)⁻¹ * B := by rw [ENNReal.tsum_geometric]

/-- If `f.support ⊆ ⋃ i, S i` and `∫⁻ x in S i, f x ∂μ ≤ r ^ i * B` for every `i : ℕ`, then
`∫⁻ x, f x ∂μ ≤ (1 - r)⁻¹ * B`. -/
theorem lintegral_le_of_shells {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {S : ℕ → Set α} {r B : ℝ≥0∞} (h_cover : f.support ⊆ ⋃ i : ℕ, S i)
    (h_shell : ∀ i : ℕ, ∫⁻ x in S i, f x ∂μ ≤ r ^ i * B) :
    ∫⁻ x, f x ∂μ ≤ (1 - r)⁻¹ * B := by
  simpa using mul_lintegral_le_of_shells (c := 1) h_cover (by simpa using h_shell)

/-- Dyadic shell summation: if `f.support ⊆ ⋃ i, S i` and
`c * ∫⁻ x in S i, f x ∂μ ≤ (2 ^ i)⁻¹ * B` for every `i : ℕ`, then `c * ∫⁻ x, f x ∂μ ≤ 2 * B`. -/
theorem mul_lintegral_le_of_dyadic_shells {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {S : ℕ → Set α} {c B : ℝ≥0∞} (h_cover : f.support ⊆ ⋃ i : ℕ, S i)
    (h_shell : ∀ i : ℕ, c * ∫⁻ x in S i, f x ∂μ ≤ ((2 : ℝ≥0∞) ^ i)⁻¹ * B) :
    c * ∫⁻ x, f x ∂μ ≤ 2 * B := by
  have h_inv : (1 - (2 : ℝ≥0∞)⁻¹)⁻¹ = 2 := by
    have h_sub : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
      conv_lhs => rw [← ENNReal.add_halves 1]
      simp [one_div]
    rw [h_sub, inv_inv]
  rw [← h_inv]
  refine mul_lintegral_le_of_shells h_cover fun i ↦ ?_
  simpa [ENNReal.inv_pow] using h_shell i

/-- Dyadic shell summation: if `f.support ⊆ ⋃ i, S i` and
`∫⁻ x in S i, f x ∂μ ≤ (2 ^ i)⁻¹ * B` for every `i : ℕ`, then `∫⁻ x, f x ∂μ ≤ 2 * B`. -/
theorem lintegral_le_of_dyadic_shells {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {S : ℕ → Set α} {B : ℝ≥0∞} (h_cover : f.support ⊆ ⋃ i : ℕ, S i)
    (h_shell : ∀ i : ℕ, ∫⁻ x in S i, f x ∂μ ≤ ((2 : ℝ≥0∞) ^ i)⁻¹ * B) :
    ∫⁻ x, f x ∂μ ≤ 2 * B := by
  simpa using mul_lintegral_le_of_dyadic_shells (c := 1) h_cover (by simpa using h_shell)

end TauCeti
