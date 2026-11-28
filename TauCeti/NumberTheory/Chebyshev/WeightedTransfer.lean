/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Weighted prime sums and the Chebyshev remainder

Partial summation expresses a weighted prime sum as its integral main term, a boundary
term involving `θ(x) - x`, and an integral of the same Chebyshev remainder. For a weight
`f`, the function differentiated in this formula is `g(t) = f(t) / log t`.
The base point is `2`, and primes at the upper endpoint are included.

The uncentered identity is the prime-weighted form of Mathlib's
`sum_mul_eq_sub_integral_mul₁`. The proof integrates the contribution of each prime
separately, so continuity at the endpoints and an integrable interior derivative suffice.

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
  let S := Nat.primesLE ⌊x⌋₊
  let F (p : ℕ) := (Ici (p : ℝ)).indicator (fun t ↦ g' t * Real.log p)
  have hθ (t : ℝ) (ht : t ∈ uIcc 2 x) : g' t * Chebyshev.theta t = ∑ p ∈ S, F p t := by
    have ht' : t ∈ Icc 2 x := uIcc_of_le hx ▸ ht
    have hfilter : S.filter (fun p : ℕ ↦ (p : ℝ) ≤ t) = Nat.primesLE ⌊t⌋₊ := by
      ext p
      have ht₀ : 0 ≤ t := zero_le_two.trans ht'.1
      simp only [mem_filter]
      exact ⟨fun hp ↦ Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff ht₀).mpr hp.2, (Nat.mem_primesLE.mp hp.1).2⟩, fun hp ↦
        ⟨Nat.primesLE_mono (Nat.floor_le_floor ht'.2) hp,
          (Nat.le_floor_iff ht₀).mp (Nat.mem_primesLE.mp hp).1⟩⟩
    rw [Chebyshev.theta_eq_sum_primesLE, ← hfilter, mul_sum, sum_filter]
    simp only [F, indicator_apply, Set.mem_Ici]
  have hF (p : ℕ) (_ : p ∈ S) : IntervalIntegrable (F p) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (((intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hg').mul_const
        (Real.log p) |>.indicator measurableSet_Ici)
  rw [intervalIntegral.integral_congr hθ, intervalIntegral.integral_finsetSum hF,
    Chebyshev.theta_eq_sum_primesLE, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  obtain ⟨hpx, hprime⟩ := Nat.mem_primesLE.mp hp
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  have hpₓ : (p : ℝ) ≤ x := (Nat.le_floor_iff (zero_le_two.trans hx)).mp hpx
  have hset : Ici (p : ℝ) ∩ Icc 2 x = Icc (p : ℝ) x := by
    ext t
    exact ⟨fun ht ↦ ⟨ht.1, ht.2.2⟩, fun ht ↦ ⟨ht.1, hp₂.trans ht.1, ht.2⟩⟩
  have hsub : Icc (p : ℝ) x ⊆ Icc 2 x := Icc_subset_Icc_left hp₂
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpₓ (hc.mono hsub)
    (fun t ht ↦ hg t ⟨hp₂.trans_lt ht.1, ht.2⟩)
    (hg'.mono_set (by simpa only [uIcc_of_le hx, uIcc_of_le hpₓ] using hsub))
  simp only [F]
  rw [intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpₓ,
    intervalIntegral.integral_mul_const, hFTC]
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
  have hθ : IntervalIntegrable (fun t : ℝ ↦ g' t * Chebyshev.theta t) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    simpa only [Chebyshev.theta_eq_sum_Icc, sum_filter] using
      integrableOn_mul_sum_Icc (m := 0)
        (fun n : ℕ ↦ if n.Prime then Real.log n else 0) (by norm_num : (0 : ℝ) ≤ 2)
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hg')
  have hparts : (∫ t in (2 : ℝ)..x, g t + t * g' t) = x * g x - 2 * g 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx (continuousOn_id.mul hc)
      (fun t ht ↦ by simpa only [id, one_mul] using (hasDerivAt_id t).mul (hg t ht))
      ((hc.intervalIntegrable_of_Icc hx).add ht)
  rw [intervalIntegral.integral_add (hc.intervalIntegrable_of_Icc hx) ht] at hparts
  have hsplit : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) * g' t) =
      (∫ t in (2 : ℝ)..x, g' t * Chebyshev.theta t) - ∫ t in (2 : ℝ)..x, t * g' t := by
    rw [← intervalIntegral.integral_sub hθ ht]
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

/-- The tail form of the weighted prime-sum identity, with `g = f / log`, assuming
`(θ(t) - t) g'(t)` is absolutely integrable on `(2, ∞)`. The constant is
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

/-- Under absolute integrability of `(θ(t) - t) g'(t)` on `(2, ∞)`, where `g = f / log`,
the full-integral constant is the limit of the centered prime sum if the boundary
remainder also tends to zero. -/
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
