/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Improper-integral asymptotics and logarithmic decay

This file extends Mathlib's improper-integral estimates with an asymptotic estimate for weighted
integrals and integrability at infinity of `(t (1 + log t) ^ 2)⁻¹`.

## Main declarations

* `TauCeti.integrableAtFilter_inv_mul_one_add_log_sq`: the function
  `t ↦ (t (1 + log t) ^ 2)⁻¹` is integrable at infinity.
* `TauCeti.isLittleO_integral_rpow_sub_one_mul`: a remainder `E t = o(t)` has
  `∫ t in 1..x, t ^ (τ - 1) * E t = o(x ^ (τ + 1))`.
-/

public section

namespace TauCeti

open Asymptotics Filter MeasureTheory Set

/-- **A remainder `o(t)` integrates to `o(x ^ (τ + 1))` against `t ^ (τ - 1)`.** If `E` is
interval integrable above `1` and `E t = o(t)`, then for every exponent `τ > -1` the weighted
integral `∫ t in 1..x, t ^ (τ - 1) * E t` is `o(x ^ (τ + 1))`. -/
theorem isLittleO_integral_rpow_sub_one_mul {E : ℝ → ℝ} {τ : ℝ} (hτ : -1 < τ)
    (hE_int : ∀ x, 1 ≤ x → IntervalIntegrable E volume 1 x) (hE : E =o[atTop] id) :
    (fun x : ℝ ↦ ∫ t in (1 : ℝ)..x, t ^ (τ - 1) * E t) =o[atTop] fun x ↦ x ^ (τ + 1) := by
  have hτ1 : 0 < τ + 1 := by linarith
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t ↦ t ^ (τ - 1) * E t) volume a b := by
    have hE' : IntervalIntegrable E volume a b := (hE_int b (ha.trans hab)).mono_set <| by
      rw [uIcc_of_le (ha.trans hab), uIcc_of_le hab]
      exact Icc_subset_Icc ha le_rfl
    refine hE'.continuousOn_mul fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
  rw [isLittleO_iff]
  intro ε hε
  -- Beyond a cutoff `T`, `|E t| ≤ ε' t` with `ε' = ε (τ + 1) / 2`.
  set ε' := ε * (τ + 1) / 2 with hε'
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((isLittleO_iff.mp hE (by positivity : 0 < ε')).and (eventually_ge_atTop (1 : ℝ)))
  have hT1 : 1 ≤ T := (hT T le_rfl).2
  have hbound (t : ℝ) (ht : T ≤ t) : |E t| ≤ ε' * t := by
    have h := (hT t ht).1
    have ht0 : 0 ≤ t := by linarith [(hT t ht).2]
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg ht0] at h
  -- The initial segment `∫ t in 1..T` is a constant, eventually below `ε / 2 * x ^ (τ + 1)`.
  set M := |∫ t in (1 : ℝ)..T, t ^ (τ - 1) * E t|
  filter_upwards [eventually_ge_atTop T,
    (tendsto_rpow_atTop hτ1).eventually_ge_atTop (2 * M / ε)] with x hx hxM
  have hxpow : 0 ≤ x ^ (τ + 1) := Real.rpow_nonneg (by linarith) _
  have hTpow : 0 ≤ T ^ (τ + 1) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxpow,
    ← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl hT1) (hint hT1 hx)]
  have htail : |∫ t in T..x, t ^ (τ - 1) * E t| ≤
      ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) := by
    calc |∫ t in T..x, t ^ (τ - 1) * E t|
        ≤ ∫ t in T..x, |t ^ (τ - 1) * E t| := intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in T..x, ε' * t ^ τ := by
          refine intervalIntegral.integral_mono_on hx (hint hT1 hx).abs
            ((intervalIntegral.intervalIntegrable_rpow' hτ).const_mul ε') fun t ht ↦ ?_
          have ht0 : 0 < t := by linarith [ht.1]
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
          calc t ^ (τ - 1) * |E t| ≤ t ^ (τ - 1) * (ε' * t) := by
                gcongr
                exact hbound t ht.1
            _ = ε' * t ^ τ := by
                rw [Real.rpow_sub_one ht0.ne']
                field_simp
      _ = ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hτ)]
  have hM : M ≤ ε / 2 * x ^ (τ + 1) := by
    rw [div_le_iff₀ hε] at hxM
    linarith
  have hε'x : ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) ≤ ε / 2 * x ^ (τ + 1) := by
    have : ε' * ((x ^ (τ + 1) - T ^ (τ + 1)) / (τ + 1)) =
        ε / 2 * (x ^ (τ + 1) - T ^ (τ + 1)) := by
      rw [hε']
      field_simp
    rw [this]
    nlinarith
  calc |(∫ t in (1 : ℝ)..T, t ^ (τ - 1) * E t) + ∫ t in T..x, t ^ (τ - 1) * E t|
      ≤ M + |∫ t in T..x, t ^ (τ - 1) * E t| := abs_add_le _ _
    _ ≤ ε * x ^ (τ + 1) := by linarith

/-- The function `(t (1 + log t) ^ 2)⁻¹` is integrable at infinity. On `Ioi 1` it is dominated
by Mathlib's log-Cauchy density `(t (1 + (log t) ^ 2))⁻¹`. -/
theorem integrableAtFilter_inv_mul_one_add_log_sq :
    IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + Real.log u) ^ 2)⁻¹) atTop := by
  refine ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  have hmaj : IntegrableOn (fun u : ℝ ↦ (u * (1 + Real.log u ^ 2))⁻¹) (Ioi (1 : ℝ)) :=
    ((integrableOn_Ioi_zero_inv_mul_one_add_log_sq (b := 1) one_ne_zero).congr_fun
      (fun u _ ↦ by rw [one_mul]) measurableSet_Ioi).mono_set (Ioi_subset_Ioi zero_le_one)
  refine MeasureTheory.Integrable.mono hmaj (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
  have hL : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1.le
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  nlinarith

end TauCeti
