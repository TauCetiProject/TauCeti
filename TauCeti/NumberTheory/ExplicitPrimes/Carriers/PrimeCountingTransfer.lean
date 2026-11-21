/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.Analysis.SpecialFunctions.LogIntegral

/-!
# Exact transfer of Chebyshev errors to prime-counting errors

The partial-summation formula for `Chebyshev.theta` gives an exact identity for
`Nat.primeCounting ⌊x⌋₊ - Real.logIntegral x`. Its difference form transfers a bound for
`|Chebyshev.theta t - t|` on a finite interval to a prime-counting bound on that interval.
Keeping the two errors at the initial endpoint together can improve the resulting estimate.

Here `Real.logIntegral` is the offset integral starting at `2`, not the principal-value
logarithmic integral. Consequently the absolute identity includes the constant `2 / log 2`;
the constant cancels in the difference identity.

The identities follow Mathlib's `Chebyshev.primeCounting_eq_theta_div_log_add_integral` and
`TauCeti.Real.logIntegral_eq_div_log_sub_add`. The same cancellation for prime ideals appears
in `TauCeti.primeCount_sub_mul_logIntegral_eq`.

## References

* J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962), equation (4.17).
* A. Fiori, H. Kadiri and J. Swidinsky, *Sharper bounds for the error term in the prime number
  theorem*, Research in Number Theory 9 (2023), equation (30).
-/

public section

namespace TauCeti

open MeasureTheory Set

/-- The theta error, weighted by `(t * log t ^ 2)⁻¹`, is interval integrable to the right of `1`.
Both orientations of the interval are allowed. -/
theorem intervalIntegrable_theta_sub_id_div_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t ↦ (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) volume a b :=
  Real.intervalIntegrable_div_mul_log_sq ha hb
    (Chebyshev.theta_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b))

/-- The exact remainder identity for the inclusive prime count and the offset logarithmic
integral. The constant comes from the lower endpoint `2` of the integral. -/
theorem primeCounting_sub_logIntegral_eq {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x =
      (Chebyshev.theta x - x) / Real.log x +
        (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
        2 / Real.log 2 := by
  have hx1 : 1 < x := one_lt_two.trans_le hx
  have hsplit : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
        ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_sub
      (Real.intervalIntegrable_div_mul_log_sq one_lt_two hx1
        (Chebyshev.theta_mono.intervalIntegrable))
      (Real.intervalIntegrable_inv_log_pow 2 one_lt_two hx1)]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    field_simp
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx,
    Real.logIntegral_eq_div_log_sub_add hx, hsplit]
  ring

/-- Difference form of the exact remainder identity. The interval integral is signed, so the
endpoints need not be ordered. -/
theorem primeCounting_sub_logIntegral_sub_eq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ((Nat.primeCounting ⌊b⌋₊ : ℝ) - Real.logIntegral b) -
        ((Nat.primeCounting ⌊a⌋₊ : ℝ) - Real.logIntegral a) =
      (Chebyshev.theta b - b) / Real.log b - (Chebyshev.theta a - a) / Real.log a +
        ∫ t in a..b, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_theta_sub_id_div_mul_log_sq one_lt_two (one_lt_two.trans_le ha))
    (intervalIntegrable_theta_sub_id_div_mul_log_sq
      (one_lt_two.trans_le ha) (one_lt_two.trans_le hb))
  rw [primeCounting_sub_logIntegral_eq ha, primeCounting_sub_logIntegral_eq hb]
  linarith

/-- A pointwise theta error bounds its weighted remainder integral. Only the majorant that is
actually integrated needs to be interval integrable. -/
theorem abs_integral_theta_sub_id_div_mul_log_sq_le {a b : ℝ} {ε : ℝ → ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hε : IntervalIntegrable (fun t ↦ ε t / Real.log t ^ 2) volume a b)
    (hbound : ∀ t ∈ Icc a b, |Chebyshev.theta t - t| ≤ t * ε t) :
    |∫ t in a..b, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      ∫ t in a..b, ε t / Real.log t ^ 2 := by
  rw [← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall ?_) hε
  intro t ht
  have ht0 : 0 < t := (zero_lt_one.trans ha).trans ht.1
  have hlog : 0 < Real.log t := Real.log_pos (ha.trans ht.1)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlog)),
    div_le_div_iff₀ (mul_pos ht0 (sq_pos_of_pos hlog)) (sq_pos_of_pos hlog)]
  nlinarith [hbound t ⟨ht.1.le, ht.2⟩]

/-- Transfer a theta bound while keeping the initial prime-counting and theta errors together.
This avoids estimating two potentially cancelling endpoint terms separately. -/
theorem abs_primeCounting_sub_logIntegral_sub_theta_div_log_le {a b : ℝ} {ε : ℝ → ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hε : IntervalIntegrable (fun t ↦ ε t / Real.log t ^ 2) volume a b)
    (hbound : ∀ t ∈ Icc a b, |Chebyshev.theta t - t| ≤ t * ε t) :
    |(Nat.primeCounting ⌊b⌋₊ : ℝ) - Real.logIntegral b -
        (Chebyshev.theta b - b) / Real.log b| ≤
      |(Nat.primeCounting ⌊a⌋₊ : ℝ) - Real.logIntegral a -
        (Chebyshev.theta a - a) / Real.log a| + ∫ t in a..b, ε t / Real.log t ^ 2 := by
  have hid := primeCounting_sub_logIntegral_sub_eq ha (ha.trans hab)
  have hrewrite : (Nat.primeCounting ⌊b⌋₊ : ℝ) - Real.logIntegral b -
      (Chebyshev.theta b - b) / Real.log b =
      ((Nat.primeCounting ⌊a⌋₊ : ℝ) - Real.logIntegral a -
        (Chebyshev.theta a - a) / Real.log a) +
        ∫ t in a..b, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by linarith
  rw [hrewrite]
  exact (abs_add_le _ _).trans (add_le_add_right
    (abs_integral_theta_sub_id_div_mul_log_sq_le (one_lt_two.trans_le ha) hab hε hbound) _)

/-- Transfer a theta error on `[a, b]` to a prime-counting error at `b`, with the exact initial
endpoint combination retained. -/
theorem abs_primeCounting_sub_logIntegral_le {a b : ℝ} {ε : ℝ → ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hε : IntervalIntegrable (fun t ↦ ε t / Real.log t ^ 2) volume a b)
    (hbound : ∀ t ∈ Icc a b, |Chebyshev.theta t - t| ≤ t * ε t) :
    |(Nat.primeCounting ⌊b⌋₊ : ℝ) - Real.logIntegral b| ≤
      |(Nat.primeCounting ⌊a⌋₊ : ℝ) - Real.logIntegral a -
        (Chebyshev.theta a - a) / Real.log a| + b * ε b / Real.log b +
        ∫ t in a..b, ε t / Real.log t ^ 2 := by
  have hb1 : 1 < b := one_lt_two.trans_le (ha.trans hab)
  have hend : |(Chebyshev.theta b - b) / Real.log b| ≤ b * ε b / Real.log b := by
    rw [abs_div, abs_of_pos (Real.log_pos hb1)]
    exact div_le_div_of_nonneg_right (hbound b ⟨hab, le_rfl⟩) (Real.log_pos hb1).le
  have hmain := abs_primeCounting_sub_logIntegral_sub_theta_div_log_le ha hab hε hbound
  have htri := abs_add_le
    ((Nat.primeCounting ⌊b⌋₊ : ℝ) - Real.logIntegral b -
      (Chebyshev.theta b - b) / Real.log b)
    ((Chebyshev.theta b - b) / Real.log b)
  rw [sub_add_cancel] at htri
  linarith

/-- For a constant relative theta error, the combined-endpoint transfer has an explicit
logarithmic-integral remainder and needs no separate integrability assumption. -/
theorem abs_primeCounting_sub_logIntegral_sub_theta_div_log_le_const {a b ε : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, |Chebyshev.theta t - t| ≤ t * ε) :
    |(Nat.primeCounting ⌊b⌋₊ : ℝ) - Real.logIntegral b -
        (Chebyshev.theta b - b) / Real.log b| ≤
      |(Nat.primeCounting ⌊a⌋₊ : ℝ) - Real.logIntegral a -
        (Chebyshev.theta a - a) / Real.log a| +
        ε * (Real.logIntegral b - b / Real.log b - Real.logIntegral a + a / Real.log a) := by
  have ha1 : 1 < a := one_lt_two.trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have hε : IntervalIntegrable (fun t : ℝ ↦ ε / Real.log t ^ 2) volume a b := by
    simpa only [div_eq_mul_inv] using
      (Real.intervalIntegrable_inv_log_pow 2 ha1 hb1).const_mul ε
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (Real.intervalIntegrable_inv_log_pow 2 one_lt_two ha1)
    (Real.intervalIntegrable_inv_log_pow 2 ha1 hb1)
  have hid : (∫ t in a..b, ε / Real.log t ^ 2) =
      ε * (Real.logIntegral b - b / Real.log b - Real.logIntegral a + a / Real.log a) := by
    simp_rw [div_eq_mul_inv ε]
    rw [intervalIntegral.integral_const_mul]
    have hA := Real.logIntegral_eq_div_log_sub_add ha
    have hB := Real.logIntegral_eq_div_log_sub_add (ha.trans hab)
    congr 1
    linarith
  simpa only [hid] using
    abs_primeCounting_sub_logIntegral_sub_theta_div_log_le ha hab hε hbound

end TauCeti
