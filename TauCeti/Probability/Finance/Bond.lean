/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The deterministic money-market account

For a deterministic short rate `r` and initial bond price `β₀`, `bondPrice r β₀ t` is
`β₀ * exp (∫ u in 0..t, r u)`. Positive initial prices stay positive. For continuous rates,
the account solves `β' = r β`, both in differential and integral form. Its growth between
any two dates is the exponential of the accumulated short rate between those dates.

The finite-horizon uniqueness theorem requires only continuity of a candidate account and
its right derivative before the terminal date. In particular, it does not impose an
extension of the candidate beyond the trading horizon. A constant number of bond shares
has gains equal to the time integral of its interest income; the number may be negative,
representing borrowing.

These are deterministic asset identities, not a definition of stochastic self-financing
strategies or an assertion of market completeness.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Finance

/-- The deterministic bond price with short rate `r` and initial value `β₀`.
The financial model uses a continuous rate and `β₀ > 0`. -/
def bondPrice (r : ℝ → ℝ) (β₀ t : ℝ) : ℝ :=
  β₀ * exp (∫ u in 0..t, r u)

/-- The exponential formula for the bond price. -/
theorem bondPrice_def (r : ℝ → ℝ) (β₀ t : ℝ) :
    bondPrice r β₀ t = β₀ * exp (∫ u in 0..t, r u) :=
  (rfl)

/-- The account starts at its prescribed initial price. -/
@[simp]
theorem bondPrice_zero (r : ℝ → ℝ) (β₀ : ℝ) : bondPrice r β₀ 0 = β₀ := by
  simp [bondPrice_def]

/-- A zero initial balance remains zero. -/
@[simp]
theorem bondPrice_zero_initial (r : ℝ → ℝ) (t : ℝ) : bondPrice r 0 t = 0 := by
  simp [bondPrice_def]

/-- The account is positive exactly when its initial price is positive. -/
@[simp]
theorem bondPrice_pos_iff (r : ℝ → ℝ) (β₀ t : ℝ) :
    0 < bondPrice r β₀ t ↔ 0 < β₀ := by
  rw [bondPrice_def, mul_pos_iff_of_pos_right (exp_pos _)]

/-- A nonzero initial price never vanishes. -/
@[simp]
theorem bondPrice_ne_zero_iff (r : ℝ → ℝ) (β₀ t : ℝ) :
    bondPrice r β₀ t ≠ 0 ↔ β₀ ≠ 0 := by
  simp [bondPrice_def, exp_ne_zero]

/-- A constant short rate gives the usual exponential account, including the zero rate. -/
@[simp]
theorem bondPrice_const (r β₀ t : ℝ) :
    bondPrice (fun _ => r) β₀ t = β₀ * exp (r * t) := by
  simp [bondPrice_def, mul_comm]

/-- Scaling the initial balance scales the account at every date. -/
theorem bondPrice_mul_initial (r : ℝ → ℝ) (c β₀ t : ℝ) :
    bondPrice r (c * β₀) t = c * bondPrice r β₀ t := by
  simp [bondPrice_def, mul_assoc]

/-- Between two dates, the account grows by the exponential of the integrated short rate.
The dates need not be ordered. -/
theorem bondPrice_eq_mul_exp_integral {r : ℝ → ℝ} {a b : ℝ}
    (hr₀a : IntervalIntegrable r volume 0 a) (hrab : IntervalIntegrable r volume a b) (β₀ : ℝ) :
    bondPrice r β₀ b = bondPrice r β₀ a * exp (∫ u in a..b, r u) := by
  rw [bondPrice_def, bondPrice_def, mul_assoc, ← exp_add,
    intervalIntegral.integral_add_adjacent_intervals hr₀a hrab]

/-- The bond accrues interest at the short rate: `β'(t) = r(t) β(t)`. -/
theorem hasDerivAt_bondPrice {r : ℝ → ℝ} (hr : Continuous r) (β₀ t : ℝ) :
    HasDerivAt (bondPrice r β₀) (r t * bondPrice r β₀ t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
    hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  convert hi.exp.const_mul β₀ using 1
  · ext u
    exact bondPrice_def r β₀ u
  · rw [bondPrice_def]
    ring

/-- The derivative of the bond price is its instantaneous interest income. -/
@[simp]
theorem deriv_bondPrice {r : ℝ → ℝ} (hr : Continuous r) (β₀ t : ℝ) :
    deriv (bondPrice r β₀) t = r t * bondPrice r β₀ t :=
  (hasDerivAt_bondPrice hr β₀ t).deriv

/-- A continuous short rate gives a continuous bond price. -/
@[fun_prop]
theorem continuous_bondPrice {r : ℝ → ℝ} (hr : Continuous r) (β₀ : ℝ) :
    Continuous (bondPrice r β₀) :=
  Differentiable.continuous (fun t => (hasDerivAt_bondPrice hr β₀ t).differentiableAt)

/-- The accumulated interest income is exactly the change in the bond price. -/
theorem integral_mul_bondPrice {r : ℝ → ℝ} (hr : Continuous r) (β₀ a b : ℝ) :
    ∫ u in a..b, r u * bondPrice r β₀ u = bondPrice r β₀ b - bondPrice r β₀ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_bondPrice hr β₀ t)
    ((hr.mul (continuous_bondPrice hr β₀)).intervalIntegrable a b)

/-- Holding a fixed number `b` of bond shares finances itself by its interest income.
No sign restriction on `b` is required. -/
theorem mul_bondPrice_eq_initial_add_integral {r : ℝ → ℝ} (hr : Continuous r)
    (β₀ b t : ℝ) :
    b * bondPrice r β₀ t = b * β₀ + ∫ u in 0..t, b * (r u * bondPrice r β₀ u) := by
  rw [intervalIntegral.integral_const_mul, integral_mul_bondPrice hr, bondPrice_zero]
  ring

/-- On a finite horizon, a continuous account with the prescribed initial balance and
right derivative `r(t) B(t)` is the exponential bond price. No positivity assumption on
the candidate or the initial balance is needed for uniqueness. -/
theorem eqOn_bondPrice_of_hasDerivWithinAt {r B : ℝ → ℝ} {β₀ T : ℝ}
    (hr : Continuous r) (hB : ContinuousOn B (Icc 0 T)) (hB₀ : B 0 = β₀)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt B (r t * B t) (Ici t) t) :
    EqOn B (bondPrice r β₀) (Icc 0 T) := by
  -- Discount by the unit-initial account. The quotient has zero right derivative.
  have hne (t : ℝ) : bondPrice r 1 t ≠ 0 := (bondPrice_ne_zero_iff r 1 t).2 one_ne_zero
  have hc : ContinuousOn (fun t => B t / bondPrice r 1 t) (Icc 0 T) :=
    hB.div (continuous_bondPrice hr 1).continuousOn (fun t _ => hne t)
  have hz : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun u => B u / bondPrice r 1 u) 0 (Ici t) t := by
    intro t ht
    convert (hd t ht).div (hasDerivAt_bondPrice hr 1 t).hasDerivWithinAt (hne t) using 1
    ring
  intro t ht
  have heq := constant_of_has_deriv_right_zero hc hz t ht
  simp only [bondPrice_zero, div_one, hB₀] at heq
  rw [div_eq_iff (hne t)] at heq
  simpa [bondPrice_def] using heq

end TauCeti.Finance
