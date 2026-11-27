/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Weighted prime sums and the Chebyshev remainder

Partial summation expresses a weighted prime sum as its integral main term, a boundary
term involving `θ(x) - x`, and an integral of the same Chebyshev remainder. For a weight
`f`, the function differentiated in this formula is `g(t) = f(t) / log t`.
The base point is `2`, and primes at the upper endpoint are included.

If `(θ(t) - t) g'(t)` is absolutely integrable at infinity, its full integral gives the
constant term, while its tail gives the remaining error. This identity underlies the
explicit transfer of bounds for `θ` to Mertens sums, by taking `f(t) = 1/t` or
`f(t) = log t/t`. The hypotheses use an integrable derivative rather than requiring it
to be continuous.

## Main results

* `TauCeti.sum_primesLE_mul_log_eq_integral_add`: the finite remainder identity in terms of `g`.
* `TauCeti.sum_primesLE_eq_integral_div_log_add`: the identity for a weight `f`.
* `TauCeti.sum_primesLE_eq_integral_div_log_add_integral_Ioi`: the exact tail identity.
* `TauCeti.tendsto_sum_primesLE_sub_integral_div_log`: identification of the constant when
  the boundary remainder tends to zero.

## References

* J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962), (4.13)–(4.16).
-/

public section

namespace TauCeti

open Finset MeasureTheory Set Filter
open scoped Topology

/-- Partial summation with the Chebyshev main term removed. The sum includes the prime `2`
and any prime at `x`; this accounts for the term `2 * g 2`. -/
theorem sum_primesLE_mul_log_eq_integral_add {g g' : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hg : ∀ t ∈ Icc 2 x, HasDerivAt g (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, g p * Real.log p =
      (∫ t in (2 : ℝ)..x, g t) + 2 * g 2 + (Chebyshev.theta x - x) * g x -
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t := by
  have hgc : ContinuousOn g (Icc 2 x) := fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt
  have hderiv : IntegrableOn (deriv g) (Icc 2 x) := by
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hg').congr_fun
      (fun t ht ↦ (hg t ht).deriv.symm) measurableSet_Icc
  have hab := sum_mul_eq_sub_integral_mul₁
    (fun n : ℕ ↦ if n.Prime then Real.log n else 0) (by simp) (by simp) x
    (fun t ht ↦ (hg t ht).differentiableAt) hderiv
  simp only [mul_ite, mul_zero, ← sum_filter, ← Nat.primesLE_eq_filter_Icc_zero] at hab
  simp_rw [← Chebyshev.theta_eq_sum_primesLE] at hab
  rw [← intervalIntegral.integral_of_le hx] at hab
  have hab' : ∑ p ∈ Nat.primesLE ⌊x⌋₊, g p * Real.log p =
      g x * Chebyshev.theta x - ∫ t in (2 : ℝ)..x, g' t * Chebyshev.theta t := by
    rw [hab]
    congr 1
    exact intervalIntegral.integral_congr fun t ht ↦ by
      rw [(hg t (uIcc_of_le hx ▸ ht)).deriv]
  have ht : IntervalIntegrable (fun t : ℝ ↦ t * g' t) volume 2 x :=
    hg'.continuousOn_mul (continuousOn_id)
  have hθ : IntervalIntegrable (fun t : ℝ ↦ g' t * Chebyshev.theta t) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    simpa only [Chebyshev.theta_eq_sum_Icc, sum_filter] using
      integrableOn_mul_sum_Icc (m := 0)
        (fun n : ℕ ↦ if n.Prime then Real.log n else 0) (by norm_num : (0 : ℝ) ≤ 2)
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hg')
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ ↦ t) (u' := fun _ ↦ (1 : ℝ)) continuousOn_id
    (uIcc_of_le hx ▸ hgc) (fun t _ ↦ hasDerivAt_id t)
    (fun t ht ↦ hg t (by simpa [min_eq_left hx, max_eq_right hx] using Ioo_subset_Icc_self ht))
    intervalIntegrable_const hg'
  simp only [one_mul] at hparts
  have hsplit : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t) =
      (∫ t in (2 : ℝ)..x, g' t * Chebyshev.theta t) - ∫ t in (2 : ℝ)..x, t * g' t := by
    rw [← intervalIntegral.integral_sub hθ ht]
    exact intervalIntegral.integral_congr fun _ _ ↦ by ring
  rw [hab', hsplit]
  linarith

/-- The exact remainder for a weighted prime sum. Differentiation is applied to `f / log`,
so both the main integral and the boundary term retain the source's weight `f`. -/
theorem sum_primesLE_eq_integral_div_log_add {f g' : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hg : ∀ t ∈ Icc 2 x, HasDerivAt (fun u ↦ f u / Real.log u) (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p =
      (∫ t in (2 : ℝ)..x, f t / Real.log t) + 2 * f 2 / Real.log 2 +
        (Chebyshev.theta x - x) * (f x / Real.log x) -
          ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t := by
  have h := sum_primesLE_mul_log_eq_integral_add hx hg hg'
  have hs : ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p / Real.log p * Real.log p =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
    refine sum_congr rfl fun p hp ↦ ?_
    exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast
      (Nat.prime_of_mem_primesLE hp).one_lt)).ne'
  simpa only [hs, mul_div_assoc] using h

/-- The tail form of the weighted prime-sum identity, with `g = f / log`. The constant is
`2 f(2) / log 2 - ∫₂^∞ (θ(t) - t) g'(t) dt`. -/
theorem sum_primesLE_eq_integral_div_log_add_integral_Ioi {f g' : ℝ → ℝ} {x : ℝ}
    (hx : 2 ≤ x)
    (hg : ∀ t ∈ Icc 2 x, HasDerivAt (fun u ↦ f u / Real.log u) (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x)
    (hE : IntegrableOn (fun t ↦ (Chebyshev.theta t - t) * g' t) (Ioi 2)) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p =
      (∫ t in (2 : ℝ)..x, f t / Real.log t) +
        (2 * f 2 / Real.log 2 - ∫ t in Ioi (2 : ℝ), (Chebyshev.theta t - t) * g' t) +
        (Chebyshev.theta x - x) * (f x / Real.log x) +
          ∫ t in Ioi x, (Chebyshev.theta t - t) * g' t := by
  rw [sum_primesLE_eq_integral_div_log_add hx hg hg',
    ← intervalIntegral.integral_Ioi_sub_Ioi hE hx]
  ring

/-- The full-integral constant in the weighted identity is the limit of the centered prime
sum whenever the boundary remainder tends to zero. -/
theorem tendsto_sum_primesLE_sub_integral_div_log {f g' : ℝ → ℝ}
    (hg : ∀ t ∈ Ici (2 : ℝ), HasDerivAt (fun u ↦ f u / Real.log u) (g' t) t)
    (hg' : ∀ x, 2 ≤ x → IntervalIntegrable g' volume 2 x)
    (hE : IntegrableOn (fun t ↦ (Chebyshev.theta t - t) * g' t) (Ioi 2))
    (hboundary : Tendsto (fun x ↦ (Chebyshev.theta x - x) * (f x / Real.log x))
      atTop (𝓝 0)) :
    Tendsto (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, f p) -
      ∫ t in (2 : ℝ)..x, f t / Real.log t) atTop
        (𝓝 (2 * f 2 / Real.log 2 -
          ∫ t in Ioi (2 : ℝ), (Chebyshev.theta t - t) * g' t)) := by
  have htail : Tendsto (fun x : ℝ ↦ ∫ t in Ioi x, (Chebyshev.theta t - t) * g' t)
      atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hlim := (hboundary.add htail).const_add
    (2 * f 2 / Real.log 2 - ∫ t in Ioi (2 : ℝ), (Chebyshev.theta t - t) * g' t)
  simp only [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [sum_primesLE_eq_integral_div_log_add_integral_Ioi hx
    (fun t ht ↦ hg t ht.1) (hg' x hx) hE]
  ring

end TauCeti
