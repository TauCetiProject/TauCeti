/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.Analysis.SpecialFunctions.LogIntegral

/-!
# The exact remainder between `π` and `Li`, and the transfer of `θ`-bounds

For real `x > 1` the prime-counting function `π(x) = Nat.primeCounting ⌊x⌋₊` and the offset
logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` (`TauCeti.Real.logIntegral`) differ by an
exact expression in the error `θ(t) - t` of the Chebyshev function `θ = Chebyshev.theta`:

`π(x) - Li x = (θ(x) - x) / log x + ∫ t in 2..x, (θ(t) - t) / (t log² t) + 2 / log 2`.

It comes from subtracting the antiderivative identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, (log t ^ 2)⁻¹`
(`TauCeti.Real.logIntegral_eq_div_log_sub_add`) from Mathlib's Abel-summation formula
`π(x) = θ(x) / log x + ∫ t in 2..x, θ(t) / (t log² t)`
(`Chebyshev.primeCounting_eq_theta_div_log_add_integral`). It is the rational counterpart of the
number-field identity `TauCeti.primeCount_sub_mul_logIntegral_eq` at density `1`, stated directly
for Mathlib's `Nat.primeCounting` and `Chebyshev.theta`.

Every explicit bound for `θ` becomes an explicit bound for `π` through this identity, without
repeating the partial summation. The integrals it produces are estimated by the comparisons for the
weight `(t log² t)⁻¹` in `TauCeti/Analysis/SpecialFunctions/LogIntegral.lean`: a bound
`|θ(t) - t| ≤ t ε(t)` turns `∫ (θ(t) - t) / (t log² t)` into `∫ ε(t) / log² t`, and constant bounds
on the pieces of a partition turn it into increments of `x ↦ Li x - x / log x`
(`TauCeti.Real.abs_integral_div_mul_log_sq_le_sum`).

## Main results

* `Chebyshev.primeCounting_eq_theta_div_log_add_integral'`: Mathlib's Abel-summation formula for
  `π`, extended from `x ≥ 2` to every real `x`.
* `Chebyshev.primeCounting_sub_logIntegral_eq`: the exact remainder identity above.
* `Chebyshev.primeCounting_sub_logIntegral_sub_primeCounting_sub_logIntegral_eq`: its difference
  form between two points `x₀, x > 1`.
* `Chebyshev.abs_primeCounting_sub_logIntegral_sub_div_log_le`: the combined-endpoint transfer,
  which keeps `π(x) - Li x` together with its boundary term `(θ(x) - x) / log x`.
* `Chebyshev.abs_primeCounting_sub_logIntegral_sub_theta_sub_id_div_log_le_const`: the
  combined-endpoint transfer with the remainder integral evaluated for constant relative error.
* `Chebyshev.abs_primeCounting_sub_logIntegral_le_combined`,
  `Chebyshev.abs_primeCounting_sub_logIntegral_le`: two-sided bounds for `|π(x) - Li x|`,
  keeping the initial endpoint terms together or estimating them separately.
* `Chebyshev.primeCounting_le_logIntegral_add`, `Chebyshev.logIntegral_add_sub_le_primeCounting`:
  the one-sided transfers from the base point `2`, where the constant `2 / log 2` of the identity
  is exact and no boundary term at a second point appears.

## References

* J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962), (4.17).
* D. J. Platt, T. S. Trudgian, *The error term in the prime number theorem*, Math. Comp. 90
  (2021), §5 (the one-sided transfers from `2`).
* A. Fiori, H. Kadiri, J. Swidinsky, *Sharper bounds for the error term in the prime number
  theorem*, Res. Number Theory 9 (2023), article 63, (30) (the combined-endpoint transfer).
-/

public section

open MeasureTheory Set
open scoped Chebyshev Nat.Prime

namespace Chebyshev

open TauCeti.Real (logIntegral intervalIntegrable_div_mul_log_sq integral_div_mul_log_sq_eq_sub_add
  integral_inv_log_sq_eq_logIntegral_sub_div_log_sub integral_div_mul_log_sq_le_integral_div_log_sq
  neg_integral_div_log_sq_le_integral_div_mul_log_sq
  abs_integral_div_mul_log_sq_le_integral_div_log_sq)

/-- The error `θ(t) - t` of the Chebyshev function is interval integrable: `θ` is monotone and the
identity is continuous. -/
theorem intervalIntegrable_theta_sub_id (a b : ℝ) :
    IntervalIntegrable (fun t ↦ θ t - t) volume a b :=
  theta_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b)

/-- Mathlib's Abel-summation formula `Chebyshev.primeCounting_eq_theta_div_log_add_integral`,
`π(x) = θ(x) / log x + ∫ t in 2..x, θ(t) / (t log² t)`, holds for every real `x`: for `x < 2` both
`π(x)` and `θ(x)` vanish, and so does `θ` on `(x, 2)`. -/
theorem primeCounting_eq_theta_div_log_add_integral' (x : ℝ) :
    (π ⌊x⌋₊ : ℝ) = θ x / Real.log x + ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2) := by
  rcases le_or_gt 2 x with h2 | h2
  · exact primeCounting_eq_theta_div_log_add_integral h2
  have hπ : π ⌊x⌋₊ = 0 := Nat.primeCounting_eq_zero_iff.mpr <|
    Nat.lt_succ_iff.mp <| (Nat.floor_lt' two_ne_zero).mpr (by exact_mod_cast h2)
  have hint : ∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (0 : ℝ)), intervalIntegral.integral_zero]
    filter_upwards [volume.ae_ne 2] with t ht htI
    rw [uIoc_of_ge h2.le] at htI
    rw [theta_eq_zero_of_lt_two (lt_of_le_of_ne htI.2 ht), zero_div]
  simp [hπ, theta_eq_zero_of_lt_two h2, hint]

/-- **The exact remainder between `π` and `Li`.**  For `x > 1`,
`π(x) - Li x = (θ(x) - x) / log x + ∫ t in 2..x, (θ(t) - t) / (t log² t) + 2 / log 2`.

The constant `2 / log 2` comes from the base point `2` of `Li`. -/
theorem primeCounting_sub_logIntegral_eq {x : ℝ} (hx : 1 < x) :
    (π ⌊x⌋₊ : ℝ) - logIntegral x =
      (θ x - x) / Real.log x + (∫ t in (2 : ℝ)..x, (θ t - t) / (t * Real.log t ^ 2)) +
        2 / Real.log 2 := by
  have hsplit := integral_div_mul_log_sq_eq_sub_add 1 one_lt_two hx theta_mono.intervalIntegrable
  simp only [one_mul] at hsplit
  have hLi := integral_inv_log_sq_eq_logIntegral_sub_div_log_sub one_lt_two hx
  rw [TauCeti.Real.logIntegral_two] at hLi
  rw [primeCounting_eq_theta_div_log_add_integral' x, hsplit, hLi, sub_div]
  ring

/-- **The difference form of the remainder identity.**  For `x₀, x > 1`,
`(π(x) - Li x) - (π(x₀) - Li x₀)` equals
`(θ(x) - x) / log x - (θ(x₀) - x₀) / log x₀ + ∫ t in x₀..x, (θ(t) - t) / (t log² t)`. -/
theorem primeCounting_sub_logIntegral_sub_primeCounting_sub_logIntegral_eq {x₀ x : ℝ}
    (hx₀ : 1 < x₀) (hx : 1 < x) :
    ((π ⌊x⌋₊ : ℝ) - logIntegral x) - ((π ⌊x₀⌋₊ : ℝ) - logIntegral x₀) =
      (θ x - x) / Real.log x - (θ x₀ - x₀) / Real.log x₀ +
        ∫ t in x₀..x, (θ t - t) / (t * Real.log t ^ 2) := by
  rw [primeCounting_sub_logIntegral_eq hx, primeCounting_sub_logIntegral_eq hx₀,
    ← intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_div_mul_log_sq one_lt_two hx (intervalIntegrable_theta_sub_id 2 x))
      (intervalIntegrable_div_mul_log_sq one_lt_two hx₀ (intervalIntegrable_theta_sub_id 2 x₀))]
  ring

/-- **The combined-endpoint transfer of a `θ`-bound.**  If `|θ(t) - t| ≤ t ε(t)` on `[x₀, x]` with
`1 < x₀ ≤ x`, then the absolute value of `π(x) - Li x - (θ(x) - x) / log x` is at most its value at
`x₀` plus `∫ t in x₀..x, ε(t) / log² t`.

Keeping `π - Li` together with its boundary term avoids bounding the two separately, which is
sharper than `Chebyshev.abs_primeCounting_sub_logIntegral_le` when they nearly cancel. -/
theorem abs_primeCounting_sub_logIntegral_sub_div_log_le {ε : ℝ → ℝ} {x₀ x : ℝ} (hx₀ : 1 < x₀)
    (hx₀x : x₀ ≤ x) (hε : IntervalIntegrable ε volume x₀ x)
    (h : ∀ t ∈ Icc x₀ x, |θ t - t| ≤ t * ε t) :
    |(π ⌊x⌋₊ : ℝ) - logIntegral x - (θ x - x) / Real.log x| ≤
      |(π ⌊x₀⌋₊ : ℝ) - logIntegral x₀ - (θ x₀ - x₀) / Real.log x₀| +
        ∫ t in x₀..x, ε t / Real.log t ^ 2 := by
  have hdiff :=
    primeCounting_sub_logIntegral_sub_primeCounting_sub_logIntegral_eq hx₀ (hx₀.trans_le hx₀x)
  have hint := abs_integral_div_mul_log_sq_le_integral_div_log_sq hx₀ hx₀x
    (intervalIntegrable_theta_sub_id x₀ x) hε h
  rw [show (π ⌊x⌋₊ : ℝ) - logIntegral x - (θ x - x) / Real.log x =
      ((π ⌊x₀⌋₊ : ℝ) - logIntegral x₀ - (θ x₀ - x₀) / Real.log x₀) +
        ∫ t in x₀..x, (θ t - t) / (t * Real.log t ^ 2) by linarith]
  exact (abs_add_le _ _).trans (add_le_add_right hint _)

/-- For a constant relative `θ`-error, the combined-endpoint transfer has an explicit remainder:
`ε` times the increment of `t ↦ Li t - t / log t`. -/
theorem abs_primeCounting_sub_logIntegral_sub_theta_sub_id_div_log_le_const {ε x₀ x : ℝ}
    (hx₀ : 1 < x₀) (hx₀x : x₀ ≤ x) (h : ∀ t ∈ Icc x₀ x, |θ t - t| ≤ t * ε) :
    |(π ⌊x⌋₊ : ℝ) - logIntegral x - (θ x - x) / Real.log x| ≤
      |(π ⌊x₀⌋₊ : ℝ) - logIntegral x₀ - (θ x₀ - x₀) / Real.log x₀| +
        ε * (logIntegral x - x / Real.log x - (logIntegral x₀ - x₀ / Real.log x₀)) := by
  have hcomb := abs_primeCounting_sub_logIntegral_sub_div_log_le (ε := fun _ ↦ ε)
    hx₀ hx₀x intervalIntegrable_const h
  simpa only [div_eq_mul_inv ε, intervalIntegral.integral_const_mul,
    integral_inv_log_sq_eq_logIntegral_sub_div_log_sub hx₀ (hx₀.trans_le hx₀x)] using hcomb

/-- A pointwise bound `|θ(x) - x| ≤ x ε(x)` bounds the boundary term of the remainder identity. -/
private theorem abs_theta_sub_div_log_le {ε : ℝ → ℝ} {x : ℝ} (hx : 1 < x)
    (h : |θ x - x| ≤ x * ε x) : |(θ x - x) / Real.log x| ≤ x * ε x / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [abs_div, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right h hlog.le

/-- A two-sided bound for `π(x) - Li x` that keeps the initial prime-counting and `θ` errors
inside a single absolute value, allowing them to cancel. -/
theorem abs_primeCounting_sub_logIntegral_le_combined {ε : ℝ → ℝ} {x₀ x : ℝ} (hx₀ : 1 < x₀)
    (hx₀x : x₀ ≤ x) (hε : IntervalIntegrable ε volume x₀ x)
    (h : ∀ t ∈ Icc x₀ x, |θ t - t| ≤ t * ε t) :
    |(π ⌊x⌋₊ : ℝ) - logIntegral x| ≤
      |(π ⌊x₀⌋₊ : ℝ) - logIntegral x₀ - (θ x₀ - x₀) / Real.log x₀| + x * ε x / Real.log x +
        ∫ t in x₀..x, ε t / Real.log t ^ 2 := by
  have hcomb := abs_primeCounting_sub_logIntegral_sub_div_log_le hx₀ hx₀x hε h
  have hbx := abs_theta_sub_div_log_le (hx₀.trans_le hx₀x) (h x ⟨hx₀x, le_rfl⟩)
  have htri := abs_sub_abs_le_abs_sub ((π ⌊x⌋₊ : ℝ) - logIntegral x) ((θ x - x) / Real.log x)
  linarith

/-- **The transfer of a `θ`-bound to `π`.**  If `|θ(t) - t| ≤ t ε(t)` on `[x₀, x]` with
`1 < x₀ ≤ x`, then `|π(x) - Li x|` is at most
`|π(x₀) - Li x₀| + x ε(x) / log x + x₀ ε(x₀) / log x₀ + ∫ t in x₀..x, ε(t) / log² t`.

For a constant `ε`, the integral is `ε` times the increment of `t ↦ Li t - t / log t` from `x₀` to
`x` (`TauCeti.Real.integral_inv_log_sq_eq_logIntegral_sub_div_log_sub`). -/
theorem abs_primeCounting_sub_logIntegral_le {ε : ℝ → ℝ} {x₀ x : ℝ} (hx₀ : 1 < x₀)
    (hx₀x : x₀ ≤ x) (hε : IntervalIntegrable ε volume x₀ x)
    (h : ∀ t ∈ Icc x₀ x, |θ t - t| ≤ t * ε t) :
    |(π ⌊x⌋₊ : ℝ) - logIntegral x| ≤
      |(π ⌊x₀⌋₊ : ℝ) - logIntegral x₀| + x * ε x / Real.log x + x₀ * ε x₀ / Real.log x₀ +
        ∫ t in x₀..x, ε t / Real.log t ^ 2 := by
  have hcomb := abs_primeCounting_sub_logIntegral_le_combined hx₀ hx₀x hε h
  have hbx₀ := abs_theta_sub_div_log_le hx₀ (h x₀ ⟨le_rfl, hx₀x⟩)
  have htri := abs_sub ((π ⌊x₀⌋₊ : ℝ) - logIntegral x₀) ((θ x₀ - x₀) / Real.log x₀)
  linarith

/-- **The one-sided upper transfer from `2`.**  If `θ(t) - t ≤ t ε(t)` on `[2, x]`, then
`π(x) ≤ Li x + 2 / log 2 + x ε(x) / log x + ∫ t in 2..x, ε(t) / log² t`.

The constant `2 / log 2` of the remainder identity is exact, so no boundary term at a second point
appears; `Li x + 2 / log 2 = x / log x + ∫ t in 2..x, (log t ^ 2)⁻¹` by
`TauCeti.Real.logIntegral_eq_div_log_sub_add`. -/
theorem primeCounting_le_logIntegral_add {ε : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hε : IntervalIntegrable ε volume 2 x) (h : ∀ t ∈ Icc 2 x, θ t - t ≤ t * ε t) :
    (π ⌊x⌋₊ : ℝ) ≤
      logIntegral x + 2 / Real.log 2 + x * ε x / Real.log x +
        ∫ t in (2 : ℝ)..x, ε t / Real.log t ^ 2 := by
  have hid := primeCounting_sub_logIntegral_eq (one_lt_two.trans_le hx)
  have hint := integral_div_mul_log_sq_le_integral_div_log_sq one_lt_two hx
    (intervalIntegrable_theta_sub_id 2 x) hε h
  have hb : (θ x - x) / Real.log x ≤ x * ε x / Real.log x :=
    div_le_div_of_nonneg_right (h x ⟨hx, le_rfl⟩) (Real.log_pos (by linarith)).le
  linarith

/-- **The one-sided lower transfer from `2`.**  If `-(t ε(t)) ≤ θ(t) - t` on `[2, x]`, then
`Li x + 2 / log 2 - x ε(x) / log x - ∫ t in 2..x, ε(t) / log² t ≤ π(x)`. -/
theorem logIntegral_add_sub_le_primeCounting {ε : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hε : IntervalIntegrable ε volume 2 x) (h : ∀ t ∈ Icc 2 x, -(t * ε t) ≤ θ t - t) :
    logIntegral x + 2 / Real.log 2 - x * ε x / Real.log x -
        ∫ t in (2 : ℝ)..x, ε t / Real.log t ^ 2 ≤ (π ⌊x⌋₊ : ℝ) := by
  have hid := primeCounting_sub_logIntegral_eq (one_lt_two.trans_le hx)
  have hint := neg_integral_div_log_sq_le_integral_div_mul_log_sq one_lt_two hx
    (intervalIntegrable_theta_sub_id 2 x) hε h
  have hb : -(x * ε x) / Real.log x ≤ (θ x - x) / Real.log x :=
    div_le_div_of_nonneg_right (h x ⟨hx, le_rfl⟩) (Real.log_pos (by linarith)).le
  rw [neg_div] at hb
  linarith

end Chebyshev
