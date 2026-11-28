/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import TauCeti.NumberTheory.Chebyshev.AbelSummation
import TauCeti.NumberTheory.Chebyshev.Integrability
import TauCeti.NumberTheory.PrimeCounting

/-!
# Weighted prime sums and the Chebyshev remainder

Partial summation expresses a weighted prime sum as its integral main term, the lower
boundary contribution `2 * g 2 = 2 * f 2 / log 2`, a boundary term involving `θ(x) - x`,
and an integral of the same Chebyshev remainder. For a weight `f`, the function
differentiated in this formula is `g(t) = f(t) / log t`. The base point is `2`, and
primes at the upper endpoint are included.

The uncentered identity is the prime-weighted form of Mathlib's
`sum_mul_eq_sub_integral_mul₁`. Continuity at the endpoints and an integrable interior
derivative suffice by `TauCeti.sum_filter_primesLE_mul_log_eq_sub_sub_integral`.

If `(θ(t) - t) g'(t)` is absolutely integrable on `(2, ∞)`, its full integral enters the
constant term and its tail enters the remaining error. This identity underlies the
explicit transfer of bounds for `θ` to Mertens sums, by taking `f(t) = 1/t` or
`f(t) = log t/t`.

## Main results

* `TauCeti.sum_primesLE_mul_log_eq_sub_integral`: the uncentered Abel identity.
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

/-- The uncentered Abel identity for a continuous weight with an integrable interior derivative.
Taking `g = f / log` makes the summand equal to `f p` at each prime. -/
theorem sum_primesLE_mul_log_eq_sub_integral {g g' : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hc : ContinuousOn g (Icc 2 x)) (hg : ∀ t ∈ Ioo 2 x, HasDerivAt g (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, g p * Real.log p =
      g x * Chebyshev.theta x - ∫ t in (2 : ℝ)..x, g' t * Chebyshev.theta t := by
  have h := sum_filter_primesLE_mul_log_eq_sub_sub_integral
    (by norm_num : (0 : ℝ) ≤ 2) hx hc hg hg'
  have hfloor : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  have htwo : Nat.primesLE ⌊(2 : ℝ)⌋₊ = {2} := by
    rw [hfloor]
    decide
  have hθ₂ : Chebyshev.theta 2 = Real.log 2 := by
    simp only [Chebyshev.theta_eq_sum_primesLE, htwo, sum_singleton, Nat.cast_ofNat]
  rw [Nat.sum_primesLE_floor_eq_add_filter_gt (fun p ↦ g p * Real.log p) hx,
    htwo, sum_singleton, Nat.cast_ofNat, h, hθ₂]
  ring

/-- Partial summation with the Chebyshev main term removed. The sum includes the prime `2`
and any prime at `x`. The term `2 * g 2` is the lower boundary contribution from
integrating `t * g' t` by parts. -/
theorem sum_primesLE_mul_log_eq_integral_add {g g' : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hc : ContinuousOn g (Icc 2 x)) (hg : ∀ t ∈ Ioo 2 x, HasDerivAt g (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, g p * Real.log p =
      (∫ t in (2 : ℝ)..x, g t) + 2 * g 2 + (Chebyshev.theta x - x) * g x -
        ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t := by
  have ht : IntervalIntegrable (fun t : ℝ ↦ t * g' t) volume 2 x :=
    hg'.continuousOn_mul (continuousOn_id)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ ↦ t) (u' := fun _ ↦ (1 : ℝ)) continuousOn_id (uIcc_of_le hx ▸ hc)
    (fun t _ ↦ hasDerivAt_id t) (by simpa only [min_eq_left hx, max_eq_right hx] using hg)
    intervalIntegrable_const hg'
  simp only [one_mul] at hparts
  have hsplit : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t) =
      (∫ t in (2 : ℝ)..x, g' t * Chebyshev.theta t) - ∫ t in (2 : ℝ)..x, t * g' t := by
    rw [← intervalIntegral.integral_sub hg'.mul_chebyshev_theta ht]
    exact intervalIntegral.integral_congr fun _ _ ↦ by ring
  rw [sum_primesLE_mul_log_eq_sub_integral hx hc hg hg', hsplit]
  linarith

/-- The exact remainder for a weighted prime sum. Differentiation is applied to `f / log`,
so both the main integral and the boundary term retain the source's weight `f`. -/
theorem sum_primesLE_eq_integral_div_log_add {f g' : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x)
    (hc : ContinuousOn (fun t ↦ f t / Real.log t) (Icc 2 x))
    (hg : ∀ t ∈ Ioo 2 x, HasDerivAt (fun u ↦ f u / Real.log u) (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p =
      (∫ t in (2 : ℝ)..x, f t / Real.log t) + 2 * f 2 / Real.log 2 +
        (Chebyshev.theta x - x) * (f x / Real.log x) -
          ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t := by
  have h := sum_primesLE_mul_log_eq_integral_add hx hc hg hg'
  have hs : ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p / Real.log p * Real.log p =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
    refine sum_congr rfl fun p hp ↦ ?_
    exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast
      (Nat.prime_of_mem_primesLE hp).one_lt)).ne'
  simpa only [hs, mul_div_assoc] using h

/-- The tail form of `sum_primesLE_eq_integral_div_log_add`, with `g = f / log`.
In addition to the finite-interval hypotheses, it assumes `(θ(t) - t) g'(t)` is
absolutely integrable on `(2, ∞)`. The constant is
`2 f(2) / log 2 - ∫₂^∞ (θ(t) - t) g'(t) dt`. -/
theorem sum_primesLE_eq_integral_div_log_add_integral_Ioi {f g' : ℝ → ℝ} {x : ℝ}
    (hx : 2 ≤ x)
    (hc : ContinuousOn (fun t ↦ f t / Real.log t) (Icc 2 x))
    (hg : ∀ t ∈ Ioo 2 x, HasDerivAt (fun u ↦ f u / Real.log u) (g' t) t)
    (hg' : IntervalIntegrable g' volume 2 x)
    (hE : IntegrableOn (fun t ↦ (Chebyshev.theta t - t) * g' t) (Ioi 2)) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p =
      (∫ t in (2 : ℝ)..x, f t / Real.log t) +
        (2 * f 2 / Real.log 2 - ∫ t in Ioi (2 : ℝ), (Chebyshev.theta t - t) * g' t) +
        (Chebyshev.theta x - x) * (f x / Real.log x) +
          ∫ t in Ioi x, (Chebyshev.theta t - t) * g' t := by
  rw [sum_primesLE_eq_integral_div_log_add hx hc hg hg',
    ← intervalIntegral.integral_Ioi_sub_Ioi hE hx]
  ring

/-- Assume `g = f / log` is continuous on `[2, ∞)` and has derivative `g'` on `(2, ∞)`,
with `g'` interval integrable on every `[2, x]`. If `(θ(t) - t) g'(t)` is absolutely
integrable on `(2, ∞)` and the boundary remainder tends to zero, then the centered prime
sum tends to the full-integral constant. -/
theorem tendsto_sum_primesLE_sub_integral_div_log {f g' : ℝ → ℝ}
    (hc : ContinuousOn (fun t ↦ f t / Real.log t) (Ici 2))
    (hg : ∀ t ∈ Ioi (2 : ℝ), HasDerivAt (fun u ↦ f u / Real.log u) (g' t) t)
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
    (hc.mono Icc_subset_Ici_self) (fun t ht ↦ hg t ht.1) (hg' x hx) hE]
  ring

end TauCeti
