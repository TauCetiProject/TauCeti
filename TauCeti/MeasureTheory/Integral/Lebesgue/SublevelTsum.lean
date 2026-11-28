/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.MeasureTheory.Integral.Lebesgue.SublevelGrowth

/-!
# Weighted infinite sums under polynomial sublevel growth

Applying the layer-cake bound `TauCeti.lintegral_ofReal_rpow_neg_le_of_measure_le_rpow` to the
counting measure weighted by `w : α → ℝ≥0∞` converts a polynomial sublevel bound on
`∑' p, {p | u p ≤ R}.indicator w p` into a bound on `∑' p, w p * ENNReal.ofReal (u p ^ (-A))`.

## Main results

* `TauCeti.tsum_mul_ofReal_rpow_neg_le_of_indicator_le`: if `1 ≤ u p` for all `p` and
  `∑' p, {p | u p ≤ R}.indicator w p ≤ ENNReal.ofReal (R ^ ε) * C` for all `R ≥ 1`, then for
  `0 < A` and `ε < A`,
  `∑' p, w p * ENNReal.ofReal (u p ^ (-A)) ≤ ENNReal.ofReal (A / (A - ε)) * C`.
* `TauCeti.tsum_mul_inv_pow_le_of_layers`: if `1 ≤ u p` for all `p`,
  `∑' p, {p | u p ≤ R}.indicator w p ≤ ENNReal.ofReal ((K * R ^ e) ^ d)` for all `R ≥ 1`, and
  `2 * (e * d) < i`, then `∑' p, w p * ENNReal.ofReal ((u p)⁻¹ ^ i) ≤ ENNReal.ofReal (2 * K ^ d)`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Spanning/Unfolding/AmplitudeSums.lean`, declaration
`New.Filling.tsum_mul_inv_pow_le_of_layers`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- **Weighted sums under polynomial sublevel growth.** If `1 ≤ u p` for all `p` and
`∑' p, {p | u p ≤ R}.indicator w p ≤ ENNReal.ofReal (R ^ ε) * C` for every `R ≥ 1`, then for
`0 < A` and `ε < A`, `∑' p, w p * ENNReal.ofReal (u p ^ (-A)) ≤ ENNReal.ofReal (A / (A - ε)) * C`.
-/
theorem tsum_mul_ofReal_rpow_neg_le_of_indicator_le {α : Type*} {w : α → ℝ≥0∞} {u : α → ℝ}
    {ε A : ℝ} {C : ℝ≥0∞} (hu : ∀ p : α, 1 ≤ u p) (hA : 0 < A) (hεA : ε < A)
    (h_count : ∀ R ≥ (1 : ℝ), ∑' p : α, {p : α | u p ≤ R}.indicator w p ≤
      ENNReal.ofReal (R ^ ε) * C) :
    ∑' p : α, w p * ENNReal.ofReal (u p ^ (-A)) ≤ ENNReal.ofReal (A / (A - ε)) * C := by
  let _ : MeasurableSpace α := ⊤
  let μ : Measure α := Measure.count.withDensity w
  have h_vol (R : ℝ) (hR : 1 ≤ R) : μ {p | u p ≤ R} ≤ ENNReal.ofReal (R ^ ε) * C := by
    rw [withDensity_apply _ MeasurableSpace.measurableSet_top,
      ← lintegral_indicator MeasurableSpace.measurableSet_top, lintegral_count]
    exact h_count R hR
  calc ∑' p : α, w p * ENNReal.ofReal (u p ^ (-A))
      = ∫⁻ p, ENNReal.ofReal (u p ^ (-A)) ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ measurable_from_top measurable_from_top,
          lintegral_count]
        rfl
    _ ≤ ENNReal.ofReal (A / (A - ε)) * C :=
        lintegral_ofReal_rpow_neg_le_of_measure_le_rpow (ae_of_all _ hu) hA hεA h_vol

/-- **Layered decay bound for weighted sums.** If `1 ≤ u p` for all `p`, the total weight
of `{p | u p ≤ R}` is at most `(K * R ^ e) ^ d` for all `R ≥ 1`, and `2 * (e * d) < i`, then
`∑' p, w p * ENNReal.ofReal ((u p)⁻¹ ^ i) ≤ ENNReal.ofReal (2 * K ^ d)`. -/
theorem tsum_mul_inv_pow_le_of_layers {α : Type*} {w : α → ℝ≥0∞} {u : α → ℝ} {K : ℝ} {e d i : ℕ}
    (hu : ∀ p : α, 1 ≤ u p)
    (h_count : ∀ R ≥ (1 : ℝ),
      ∑' p : α, {p : α | u p ≤ R}.indicator w p ≤ ENNReal.ofReal ((K * R ^ e) ^ d))
    (hi : 2 * (e * d) < i) :
    ∑' p : α, w p * ENNReal.ofReal ((u p)⁻¹ ^ i) ≤ ENNReal.ofReal (2 * K ^ d) := by
  have hi_real : 2 * ((e : ℝ) * d) < i := by exact_mod_cast hi
  have h_ed : 0 ≤ (e : ℝ) * d := by positivity
  have h_sub : ∀ R ≥ (1 : ℝ), ∑' p : α, {p : α | u p ≤ R}.indicator w p ≤
      ENNReal.ofReal (R ^ ((e : ℝ) * d)) * ENNReal.ofReal (K ^ d) := fun R hR ↦ by
    refine (h_count R hR).trans_eq ?_
    rw [mul_pow, ← pow_mul, mul_comm (K ^ d), ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [← Real.rpow_natCast, Nat.cast_mul]
  have h_main := tsum_mul_ofReal_rpow_neg_le_of_indicator_le hu (by linarith : (0 : ℝ) < i)
    (by linarith : (e : ℝ) * d < i) h_sub
  have h_ratio : (i : ℝ) / (i - (e : ℝ) * d) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc ∑' p : α, w p * ENNReal.ofReal ((u p)⁻¹ ^ i)
      = ∑' p : α, w p * ENNReal.ofReal (u p ^ (-(i : ℝ))) := by
        congr 1; ext p
        rw [Real.rpow_neg (zero_le_one.trans (hu p)), Real.rpow_natCast, inv_pow]
    _ ≤ ENNReal.ofReal ((i : ℝ) / (i - (e : ℝ) * d)) * ENNReal.ofReal (K ^ d) := h_main
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (K ^ d) := by gcongr
    _ = ENNReal.ofReal (2 * K ^ d) := (ENNReal.ofReal_mul zero_le_two).symm

end TauCeti
