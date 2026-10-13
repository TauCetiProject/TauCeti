/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The tail integral of a negative power of the distance

In a pseudometric measure space whose closed balls satisfy the growth bound
`μ (closedBall y r) ≤ A rⁿ` (with `A : ℝ≥0∞`), the tail integral of `x ↦ dist x y ^ (-s)` obeys,
for `0 ≤ s`, `n < s` and `R > 0`, the extended-valued bound

`∫_{dist x y > R} dist x y ^ (-s) dx ≤ A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))`

(`TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`). When `A < ∞` the right-hand side is finite, so
`dist x y ^ (-s)` is integrable on `{x | R < dist x y}`. The exponent `n` need not be an integer.

The proof splits the region `dist x y > R` into the dyadic annuli `2ᵏ R ≤ dist x y < 2ᵏ⁺¹ R`.
On the `k`-th annulus `dist x y ^ (-s)` is at most `(2ᵏ R) ^ (-s)`, and the annulus lies in a
ball of measure at most `A (2ᵏ⁺¹ R)ⁿ`, so the annuli contribute a convergent geometric series
with ratio `2 ^ (n - s)`.

## Main declarations

* `TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`: the tail bound for `dist x y ^ (-s)`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X}

/-- **The tail of a power of the distance.** If the closed balls about `y` satisfy the growth
bound `μ (closedBall y r) ≤ A rⁿ`, then for `0 ≤ s`, `n < s` and `R > 0`,

`∫_{dist x y > R} dist x y ^ (-s) dx ≤ A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))`. -/
theorem setLIntegral_ofReal_dist_rpow_neg_le {y : X} {A : ℝ≥0∞} {n s : ℝ}
    (hμ : ∀ r, 0 < r → μ (closedBall y r) ≤ A * ENNReal.ofReal (r ^ n)) (hs : 0 ≤ s)
    (hns : n < s) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in {x | R < dist x y}, ENNReal.ofReal (dist x y ^ (-s)) ∂μ ≤
      A * ENNReal.ofReal (2 ^ n / (1 - 2 ^ (n - s)) * R ^ (n - s)) := by
  set q : ℝ := 2 ^ (n - s)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  -- The dyadic annuli `2ᵏ R ≤ dist x y < 2ᵏ⁺¹ R` cover the region `R < dist x y`.
  set S : ℕ → Set X := fun k => (fun x => dist x y) ⁻¹' Ico (2 ^ k * R) (2 ^ (k + 1) * R)
  have hcover : {x | R < dist x y} ⊆ ⋃ k, S k := by
    intro x hx
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((one_le_div hR).2 (le_of_lt hx))
      one_lt_two
    refine mem_iUnion.2 ⟨k, ?_, ?_⟩
    · exact (le_div_iff₀ hR).1 hk
    · rw [pow_succ] at hk' ⊢
      exact (div_lt_iff₀ hR).1 hk'
  -- On the `k`-th annulus the integrand is at most `(2ᵏ R) ^ (-s)`, and the annulus lies in a
  -- ball of measure at most `A (2ᵏ⁺¹ R)ⁿ`.
  have hS (k : ℕ) : ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ ≤
      A * ENNReal.ofReal (2 ^ n * R ^ (n - s) * q ^ k) := by
    set u : ℝ := 2 ^ k * R
    have hu : 0 < u := by positivity
    have hmeas : MeasurableSet (S k) :=
      measurableSet_Ico.preimage (continuous_id.dist continuous_const).measurable
    -- The scalar identity `u ^ (-s) (2u)ⁿ = 2ⁿ R ^ (n - s) qᵏ` for `u = 2ᵏ R`.
    have hpow : u ^ (-s) * (2 * u) ^ n = 2 ^ n * R ^ (n - s) * q ^ k := by
      have hqk : q ^ k * R ^ (n - s) = u ^ (n - s) := by
        rw [Real.rpow_pow_comm zero_le_two, ← Real.mul_rpow (by positivity) hR.le]
      rw [mul_assoc, mul_comm (R ^ _), hqk, sub_eq_add_neg, Real.rpow_add hu,
        Real.mul_rpow zero_le_two hu.le]
      ring
    calc ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ
        ≤ ∫⁻ _ in S k, ENNReal.ofReal (u ^ (-s)) ∂μ :=
          setLIntegral_mono' hmeas fun x hx => ENNReal.ofReal_le_ofReal <|
            Real.rpow_le_rpow_of_nonpos hu hx.1 (neg_nonpos.2 hs)
      _ ≤ ENNReal.ofReal (u ^ (-s)) * (A * ENNReal.ofReal ((2 * u) ^ n)) := by
          rw [setLIntegral_const]
          gcongr
          refine (measure_mono fun x hx => mem_closedBall.2 ?_).trans (hμ _ (by positivity))
          exact hx.2.le.trans_eq (by ring)
      _ = A * ENNReal.ofReal (2 ^ n * R ^ (n - s) * q ^ k) := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), hpow]
  have hsum : Summable fun k : ℕ => 2 ^ n * R ^ (n - s) * q ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∫⁻ x in {x | R < dist x y}, ENNReal.ofReal (dist x y ^ (-s)) ∂μ
      ≤ ∫⁻ x in ⋃ k, S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' k, A * ENNReal.ofReal (2 ^ n * R ^ (n - s) * q ^ k) := ENNReal.tsum_le_tsum hS
    _ = A * ENNReal.ofReal (∑' k, 2 ^ n * R ^ (n - s) * q ^ k) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsum]
    _ = A * ENNReal.ofReal (2 ^ n / (1 - q) * R ^ (n - s)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
        congr 2
        ring

end TauCeti
