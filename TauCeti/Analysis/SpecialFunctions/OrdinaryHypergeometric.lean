/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# The ordinary hypergeometric function on the unit ball

Mathlib computes the radius of convergence of the series of `₂F₁(a, b; c; ·)`: it is `1`, unless
one of the parameters is a nonpositive integer, in which case the series is finite or its
coefficients take the junk value `0`, and the radius is `⊤`. This file records the uniform
consequence that the radius is always at least `1`, so `₂F₁(a, b; c; ·)` is analytic on the open
unit ball for all parameters.

Over `ℝ` or `ℂ`, the series can be differentiated termwise inside its disc of convergence. This
gives the Taylor coefficients `(a)ₙ (b)ₙ / (c)ₙ` of `₂F₁(a, b; c; ·)` at `0`, and shows that, when
`c` is not a nonpositive integer, `y = ₂F₁(a, b; c; ·)` solves **Gauss's hypergeometric equation**
`x (1 - x) y'' + (c - (a + b + 1) x) y' - a b y = 0` (DLMF 15.10.1) on the open unit disc, and on
the whole field when the series terminates. The equation is equivalent to the recurrence
`(n + 1) (c + n) cₙ₊₁ = (a + n) (b + n) cₙ` for the coefficients `cₙ` of the series.

## Main statements

* `TauCeti.one_le_radius_ordinaryHypergeometricSeries`: the radius of convergence of
  `ordinaryHypergeometricSeries 𝔸 a b c` is at least `1`.
* `TauCeti.analyticOnNhd_ordinaryHypergeometric`: `₂F₁ a b c` is analytic on the open unit ball.
* `TauCeti.ordinaryHypergeometricCoefficient_add_one`: the coefficient recurrence.
* `TauCeti.iteratedDeriv_ordinaryHypergeometric_zero`: the Taylor coefficients at `0`; in
  particular `TauCeti.deriv_ordinaryHypergeometric_zero` gives `(₂F₁ a b c)' 0 = a b / c`.
* `TauCeti.ordinaryHypergeometric_gaussEquation`: Gauss's hypergeometric equation inside the disc
  of convergence, with the special cases
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one` (the open unit disc) and
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_neg_nat` (terminating series, everywhere).

## References

* NIST Digital Library of Mathematical Functions, §15.2 and equation 15.10.1.
-/

public section

namespace TauCeti

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- The radius of convergence of the hypergeometric series `₂F₁(a, b; c; ·)` is at least `1`, for
all parameters. -/
theorem one_le_radius_ordinaryHypergeometricSeries (a b c : 𝕂) :
    1 ≤ (ordinaryHypergeometricSeries 𝔸 a b c).radius := by
  by_cases h : ∀ k : ℕ, (k : 𝕂) ≠ -a ∧ (k : 𝕂) ≠ -b ∧ (k : 𝕂) ≠ -c
  · exact (ordinaryHypergeometricSeries_radius_eq_one 𝔸 a b c h).ge
  · push Not at h
    obtain ⟨k, hk⟩ := h
    by_cases ha : (k : 𝕂) = -a
    · have ha' : a = -(k : 𝕂) := by rw [ha, neg_neg]
      rw [ha', ordinaryHypergeometric_radius_top_of_neg_nat₁]
      exact le_top
    by_cases hb : (k : 𝕂) = -b
    · have hb' : b = -(k : 𝕂) := by rw [hb, neg_neg]
      rw [hb', ordinaryHypergeometric_radius_top_of_neg_nat₂]
      exact le_top
    · have hc : c = -(k : 𝕂) := by rw [hk ha hb, neg_neg]
      rw [hc, ordinaryHypergeometric_radius_top_of_neg_nat₃]
      exact le_top

/-- The ordinary hypergeometric function `₂F₁(a, b; c; ·)` is analytic on the open unit ball, for
all parameters. -/
theorem analyticOnNhd_ordinaryHypergeometric [CompleteSpace 𝔸] (a b c : 𝕂) :
    AnalyticOnNhd 𝕂 (₂F₁ a b c : 𝔸 → 𝔸) (Metric.ball 0 1) := by
  intro x hx
  have h1 := one_le_radius_ordinaryHypergeometricSeries 𝔸 a b c
  exact ((ordinaryHypergeometricSeries 𝔸 a b c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le h1)).analyticAt_of_mem
      (Metric.eball_subset_eball h1 (by
        simpa only [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one, Metric.mem_ball] using hx))

/-- The ordinary hypergeometric function is the sum of the scalar power series with the
hypergeometric coefficients. -/
theorem ordinaryHypergeometric_eq_ofScalarsSum (a b c : 𝕂) :
    (₂F₁ a b c : 𝔸 → 𝔸) =
      FormalMultilinearSeries.ofScalarsSum (ordinaryHypergeometricCoefficient a b c) :=
  rfl

/-- **The hypergeometric coefficient recurrence.** The coefficients `cₙ = (a)ₙ (b)ₙ / ((c)ₙ n!)`
of `₂F₁(a, b; c; ·)` satisfy `cₙ₊₁ = (a + n) (b + n) / ((n + 1) (c + n)) cₙ` whenever
`c + n ≠ 0`. -/
theorem ordinaryHypergeometricCoefficient_add_one {K : Type*} [Field K] [CharZero K]
    (a b c : K) {n : ℕ} (hc : c + n ≠ 0) :
    ordinaryHypergeometricCoefficient a b c (n + 1) =
      (a + n) * (b + n) / ((n + 1) * (c + n)) * ordinaryHypergeometricCoefficient a b c n := by
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ, Nat.cast_mul,
    ascPochhammer_succ_eval, mul_inv]
  by_cases h : (ascPochhammer K n).eval c = 0
  · simp [h]
  · field_simp
    push_cast
    ring

section Scalar

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The iterated derivatives of `₂F₁(a, b; c; ·)` at `0` are `(a)ₙ (b)ₙ / (c)ₙ`, for all
parameters. -/
@[simp]
theorem iteratedDeriv_ordinaryHypergeometric_zero (a b c : 𝕂) (n : ℕ) :
    iteratedDeriv n (₂F₁ a b c : 𝕂 → 𝕂) 0 =
      (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b / (ascPochhammer 𝕂 n).eval c := by
  have hr := zero_lt_one.trans_le (one_le_radius_ordinaryHypergeometricSeries 𝕂 a b c)
  rw [ordinaryHypergeometric_eq_ofScalarsSum,
    FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero _ hr, ordinaryHypergeometricCoefficient]
  simp only [mul_assoc]
  rw [mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), div_eq_mul_inv, mul_assoc]

/-- The derivative of `₂F₁(a, b; c; ·)` at `0` is `a b / c`, for all parameters. -/
@[simp]
theorem deriv_ordinaryHypergeometric_zero (a b c : 𝕂) :
    deriv (₂F₁ a b c : 𝕂 → 𝕂) 0 = a * b / c := by
  rw [← iteratedDeriv_one, iteratedDeriv_ordinaryHypergeometric_zero]
  simp

/-- **Gauss's hypergeometric differential equation.** If the lower parameter `c` is not a
nonpositive integer, then `y = ₂F₁(a, b; c; ·)` satisfies
`x (1 - x) y'' + (c - (a + b + 1) x) y' - a b y = 0` at every `x` inside the disc of convergence of
its series. -/
theorem ordinaryHypergeometric_gaussEquation (a b c : 𝕂) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂}
    (hx : ‖x‖ₑ < (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c)) x + (c - (a + b + 1) * x) * deriv (₂F₁ a b c) x -
      a * b * ₂F₁ a b c x = 0 := by
  set C := ordinaryHypergeometricCoefficient a b c with hC
  set f : 𝕂 → 𝕂 := ₂F₁ a b c
  -- by definition, `₂F₁ a b c` is the sum of `ordinaryHypergeometricSeries 𝕂 a b c`, which is the
  -- scalar series `ofScalars 𝕂 C`
  have hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕂 C) 0
      (ordinaryHypergeometricSeries 𝕂 a b c).radius :=
    (ordinaryHypergeometricSeries 𝕂 a b c).hasFPowerSeriesOnBall
      (zero_lt_one.trans_le (one_le_radius_ordinaryHypergeometricSeries 𝕂 a b c))
  have hf' := hf.deriv_ofScalars
  have hxb : x ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius :=
    mem_eball_zero_iff.mpr hx
  -- the series of `f`, `f'`, `x f'`, `x f''` and `x² f''` at `x`, all indexed by powers `x ^ n`
  have h0 : HasSum (fun n : ℕ ↦ C n * x ^ n) (f x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hf.hasSum hxb
  have h1 : HasSum (fun n : ℕ ↦ (n + 1) * C (n + 1) * x ^ n) (deriv f x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hf'.hasSum hxb
  have h2 := hf.hasSum_mul_deriv_ofScalars hx
  have h3 := hf'.hasSum_mul_deriv_ofScalars hx
  have h4 : HasSum (fun n : ℕ ↦ ((n : 𝕂) - 1) * n * C n * x ^ n) (x * (x * deriv (deriv f) x)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h3.mul_left x
  have hsum := (h3.add (h1.mul_left c)).sub ((h4.add (h2.mul_left (a + b + 1))).add
    (h0.mul_left (a * b)))
  -- by the coefficient recurrence, every term of the combined series vanishes
  have hzero : (fun n : ℕ ↦ n * ((n + 1) * C (n + 1)) * x ^ n + c * ((n + 1) * C (n + 1) * x ^ n) -
      (((n : 𝕂) - 1) * n * C n * x ^ n + (a + b + 1) * (n * C n * x ^ n) + a * b * (C n * x ^ n))) =
      0 := by
    funext n
    have hcn : c + n ≠ 0 := fun h ↦ hc n (eq_neg_of_add_eq_zero_right h)
    have hrec : (n + 1) * (c + n) * C (n + 1) = (a + n) * (b + n) * C n := by
      rw [hC, ordinaryHypergeometricCoefficient_add_one a b c hcn]
      field_simp
    rw [Pi.zero_apply]
    linear_combination x ^ n * hrec
  rw [hzero] at hsum
  linear_combination hsum.unique hasSum_zero

/-- **Gauss's hypergeometric differential equation** on the open unit disc. -/
theorem ordinaryHypergeometric_gaussEquation_of_norm_lt_one (a b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c)) x + (c - (a + b + 1) * x) * deriv (₂F₁ a b c) x -
      a * b * ₂F₁ a b c x = 0 :=
  ordinaryHypergeometric_gaussEquation a b c hc <|
    (by rw [← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hx : ‖x‖ₑ < 1).trans_le
      (one_le_radius_ordinaryHypergeometricSeries 𝕂 a b c)

/-- **Gauss's hypergeometric differential equation for a terminating series.** If `a` or `b` is a
nonpositive integer, `₂F₁(a, b; c; ·)` is a polynomial, and it satisfies Gauss's equation at every
point, provided `c` is not a nonpositive integer. -/
theorem ordinaryHypergeometric_gaussEquation_of_neg_nat (a b c : 𝕂) {k : ℕ}
    (hab : (k : 𝕂) = -a ∨ (k : 𝕂) = -b) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) (x : 𝕂) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c)) x + (c - (a + b + 1) * x) * deriv (₂F₁ a b c) x -
      a * b * ₂F₁ a b c x = 0 := by
  refine ordinaryHypergeometric_gaussEquation a b c hc ?_
  rcases hab with ha | hb
  · rw [← neg_neg a, ← ha, ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact eNorm_lt_top
  · rw [← neg_neg b, ← hb, ordinaryHypergeometric_radius_top_of_neg_nat₂]
    exact eNorm_lt_top

end Scalar

end TauCeti
