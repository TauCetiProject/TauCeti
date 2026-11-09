/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Topology.Order.ProjIcc

/-!
# The deterministic money-market account

In a market with a deterministic short rate `r : ℝ → ℝ`, one share of the bond (the
money-market account) started at price `β₀` is worth

`β_t = β₀ exp (∫₀ᵗ r_u du)`

at time `t` (`TauCeti.Finance.bondPrice`). It is the riskless asset against which a stock is
traded: a strategy holding `b_t` bond shares has bond wealth `b_t β_t`. Since `dβ = r β dt`,
gains from the bond are ordinary time integrals against `r β`.

Between two dates the account grows by the exponential of the accumulated short rate, so
`β_t / β_T = exp (-∫ₜᵀ r_u du)` is the discount factor from `T` back to `t`; for a constant rate
this is the factor `e^{-r (T - t)}` of the Black–Scholes formulas.

On a horizon `[0, T]` on which the rate is continuous, the account solves `β' = r β`, in
differential and in integral form, and it is the unique continuous solution of that equation
with initial value `β₀`. Uniqueness needs only a right derivative before `T` and makes no
positivity assumption on the solution. None of the horizon statements needs the rate outside
`[0, T]`.

Since `dβ = r β dt`, trading the bond is pathwise integration against a function of finite
variation: for a simple bond holding `b` starting at a nonnegative date, the elementary integral
`∫₀ᵗ b dβ` of `TauCeti.Finance.simpleGains` is the time integral `∫₀ᵗ b_u r_u β_u du`. This is the
bond part `∫₀ᵗ b_u dβ_u` of the self-financing equation `V_t = V₀ + ∫₀ᵗ a_u dS_u + ∫₀ᵗ b_u dβ_u`.

## Main declarations

* `TauCeti.Finance.bondPrice`: the money-market account `β₀ exp (∫₀ᵗ r)`.
* `TauCeti.Finance.bondPrice_eq_mul_exp_integral`, `TauCeti.Finance.bondPrice_div_bondPrice`:
  growth and discounting between two dates.
* `TauCeti.Finance.hasDerivAt_bondPrice`, `TauCeti.Finance.hasDerivWithinAt_bondPrice`: the
  account accrues interest at the short rate, `β' = r β`.
* `TauCeti.Finance.integral_mul_bondPrice`: the integral form `∫ₐᵇ r β = β_b - β_a`.
* `TauCeti.Finance.eqOn_bondPrice_of_hasDerivWithinAt`: uniqueness of the account as the
  solution of `β' = r β` on a finite horizon.
* `TauCeti.Finance.simpleGains_bondPrice`: the gains `∫₀ᵗ b dβ` of a simple bond holding are
  `∫₀ᵗ b_u r_u β_u du`.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.
* I. Karatzas, S. E. Shreve, *Methods of Mathematical Finance*, Springer, 1998, §1.1.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Finance

variable {r : ℝ → ℝ} {β₀ a b t T : ℝ}

/-- The deterministic money-market account: one bond share with initial price `β₀`, accruing
interest at the short rate `r`, is worth `β₀ exp (∫₀ᵗ r_u du)` at time `t`. -/
def bondPrice (r : ℝ → ℝ) (β₀ t : ℝ) : ℝ :=
  β₀ * exp (∫ u in 0..t, r u)

theorem bondPrice_def (r : ℝ → ℝ) (β₀ t : ℝ) :
    bondPrice r β₀ t = β₀ * exp (∫ u in 0..t, r u) :=
  (rfl)

/-- The account starts at its initial price. -/
@[simp]
theorem bondPrice_zero (r : ℝ → ℝ) (β₀ : ℝ) : bondPrice r β₀ 0 = β₀ := by
  simp [bondPrice_def]

/-- A constant short rate gives the account `β₀ e^{r t}`. -/
@[simp]
theorem bondPrice_const (r β₀ t : ℝ) : bondPrice (fun _ ↦ r) β₀ t = β₀ * exp (r * t) := by
  simp [bondPrice_def, mul_comm]

/-- The account is linear in its initial price. -/
theorem bondPrice_mul_left (r : ℝ → ℝ) (c β₀ t : ℝ) :
    bondPrice r (c * β₀) t = c * bondPrice r β₀ t := by
  simp only [bondPrice_def, mul_assoc]

/-- The account is positive exactly when its initial price is. -/
@[simp]
theorem bondPrice_pos_iff : 0 < bondPrice r β₀ t ↔ 0 < β₀ := by
  rw [bondPrice_def, mul_pos_iff_of_pos_right (exp_pos _)]

/-- A positive initial price stays positive. -/
theorem bondPrice_pos (hβ₀ : 0 < β₀) (r : ℝ → ℝ) (t : ℝ) : 0 < bondPrice r β₀ t :=
  bondPrice_pos_iff.2 hβ₀

/-- The account vanishes exactly when its initial price does. -/
@[simp]
theorem bondPrice_eq_zero_iff : bondPrice r β₀ t = 0 ↔ β₀ = 0 := by
  simp [bondPrice_def]

/-- The account at time `t` depends only on the short rate between `0` and `t`. -/
theorem bondPrice_congr {ρ : ℝ → ℝ} (h : EqOn ρ r (uIcc 0 t)) (β₀ : ℝ) :
    bondPrice ρ β₀ t = bondPrice r β₀ t := by
  rw [bondPrice_def, bondPrice_def, intervalIntegral.integral_congr h]

/-! ### Growth and discounting between two dates -/

/-- Between two dates `a` and `b`, in either order, the account grows by the exponential of
the short rate accumulated between them. -/
theorem bondPrice_eq_mul_exp_integral (h₀ : IntervalIntegrable r volume 0 a)
    (h : IntervalIntegrable r volume a b) (β₀ : ℝ) :
    bondPrice r β₀ b = bondPrice r β₀ a * exp (∫ u in a..b, r u) := by
  rw [bondPrice_def, bondPrice_def, mul_assoc, ← exp_add,
    intervalIntegral.integral_add_adjacent_intervals h₀ h]

/-- The ratio of the account at two dates is the exponential of the short rate accumulated
between them. With the dates `T` and `t ≤ T`, `β_t / β_T = exp (-∫ₜᵀ r)` is the discount factor
from `T` back to `t`. -/
theorem bondPrice_div_bondPrice (h₀ : IntervalIntegrable r volume 0 a)
    (h : IntervalIntegrable r volume a b) (hβ₀ : β₀ ≠ 0) :
    bondPrice r β₀ b / bondPrice r β₀ a = exp (∫ u in a..b, r u) := by
  rw [bondPrice_eq_mul_exp_integral h₀ h, mul_div_cancel_left₀ _ (by simpa using hβ₀)]

/-! ### The account solves `β' = r β` -/

/-- For a continuous short rate, the account accrues interest at that rate:
`β'(t) = r(t) β(t)`. -/
theorem hasDerivAt_bondPrice (hr : Continuous r) (β₀ t : ℝ) :
    HasDerivAt (bondPrice r β₀) (r t * bondPrice r β₀ t) t := by
  have hi := (hr.integral_hasStrictDerivAt 0 t).hasDerivAt
  convert hi.exp.const_mul β₀ using 1
  · exact funext (bondPrice_def r β₀)
  · rw [bondPrice_def]
    ring

/-- The derivative of the account is its instantaneous interest income. -/
theorem deriv_bondPrice (hr : Continuous r) (β₀ t : ℝ) :
    deriv (bondPrice r β₀) t = r t * bondPrice r β₀ t :=
  (hasDerivAt_bondPrice hr β₀ t).deriv

@[fun_prop]
theorem differentiable_bondPrice (hr : Continuous r) (β₀ : ℝ) :
    Differentiable ℝ (bondPrice r β₀) :=
  fun t ↦ (hasDerivAt_bondPrice hr β₀ t).differentiableAt

@[fun_prop]
theorem continuous_bondPrice (hr : Continuous r) (β₀ : ℝ) : Continuous (bondPrice r β₀) :=
  (differentiable_bondPrice hr β₀).continuous

/-! ### The account on a finite horizon

The horizon statements extend the rate continuously from `[0, T]`
(`ContinuousOn.exists_continuous_eqOn_Icc`). By `bondPrice_congr` the extension gives the same
account on `[0, T]`, so the statements for a continuous rate apply. -/

private theorem bondPrice_eq_of_eqOn {ρ : ℝ → ℝ} (hρ : EqOn ρ r (Icc 0 T)) (ht : t ∈ Icc 0 T)
    (β₀ : ℝ) : bondPrice ρ β₀ t = bondPrice r β₀ t :=
  bondPrice_congr (hρ.mono (uIcc_subset_Icc (left_mem_Icc.2 (ht.1.trans ht.2)) ht)) β₀

/-- On a horizon `[0, T]` on which the short rate is continuous, the account accrues interest
at that rate: `β'(t) = r(t) β(t)` for every `t ∈ [0, T]`, as a derivative within `[0, T]`.
The rate outside the horizon is irrelevant. -/
theorem hasDerivWithinAt_bondPrice (hr : ContinuousOn r (Icc 0 T)) (β₀ : ℝ)
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (bondPrice r β₀) (r t * bondPrice r β₀ t) (Icc 0 T) t := by
  obtain ⟨ρ, hρc, hρ⟩ := hr.exists_continuous_eqOn_Icc (ht.1.trans ht.2)
  have h := (hasDerivAt_bondPrice hρc β₀ t).hasDerivWithinAt (s := Icc 0 T)
  rw [hρ ht, bondPrice_eq_of_eqOn hρ ht] at h
  exact h.congr_of_mem (fun u hu ↦ (bondPrice_eq_of_eqOn hρ hu β₀).symm) ht

theorem continuousOn_bondPrice (hr : ContinuousOn r (Icc 0 T)) (β₀ : ℝ) :
    ContinuousOn (bondPrice r β₀) (Icc 0 T) :=
  fun _ ht ↦ (hasDerivWithinAt_bondPrice hr β₀ ht).continuousWithinAt

/-- **The account in integral form.** On a horizon `[0, T]` on which the short rate is
continuous, the interest accrued between two dates of the horizon is the change in the account:
`∫ₐᵇ r_u β_u du = β_b - β_a`. -/
theorem integral_mul_bondPrice (hr : ContinuousOn r (Icc 0 T)) (β₀ : ℝ) (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) :
    ∫ u in a..b, r u * bondPrice r β₀ u = bondPrice r β₀ b - bondPrice r β₀ a := by
  obtain ⟨ρ, hρc, hρ⟩ := hr.exists_continuous_eqOn_Icc (ha.1.trans ha.2)
  have hab := uIcc_subset_Icc ha hb
  have hint : EqOn (fun u ↦ r u * bondPrice r β₀ u) (fun u ↦ ρ u * bondPrice ρ β₀ u)
      (uIcc a b) := fun u hu ↦ by
    simp only [hρ (hab hu), bondPrice_eq_of_eqOn hρ (hab hu)]
  rw [← bondPrice_eq_of_eqOn hρ ha, ← bondPrice_eq_of_eqOn hρ hb,
    intervalIntegral.integral_congr hint]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hasDerivAt_bondPrice hρc β₀ u)
    ((hρc.mul (continuous_bondPrice hρc β₀)).intervalIntegrable a b)

/-- **Uniqueness of the money-market account.** On a horizon `[0, T]` on which the short rate is
continuous, a function `B`, continuous on `[0, T]`, with `B 0 = β₀` and right derivative
`r(t) B(t)` at every `t ∈ [0, T)` is the account `bondPrice r β₀` on `[0, T]`. -/
theorem eqOn_bondPrice_of_hasDerivWithinAt {B : ℝ → ℝ} (hr : ContinuousOn r (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T)) (hB₀ : B 0 = β₀)
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt B (r t * B t) (Ici t) t) :
    EqOn B (bondPrice r β₀) (Icc 0 T) := by
  intro t ht
  obtain ⟨ρ, hρc, hρ⟩ := hr.exists_continuous_eqOn_Icc (ht.1.trans ht.2)
  -- Discounted by the unit account, `B` has zero right derivative, so it is constant.
  have hne (u : ℝ) : bondPrice ρ 1 u ≠ 0 := by simp
  have hc : ContinuousOn (fun u ↦ B u / bondPrice ρ 1 u) (Icc 0 T) :=
    hB.div (continuous_bondPrice hρc 1).continuousOn fun u _ ↦ hne u
  have hz (u : ℝ) (hu : u ∈ Ico 0 T) :
      HasDerivWithinAt (fun v ↦ B v / bondPrice ρ 1 v) 0 (Ici u) u := by
    convert (hd u hu).div (hasDerivAt_bondPrice hρc 1 u).hasDerivWithinAt (hne u) using 1
    rw [hρ (Ico_subset_Icc_self hu)]
    ring
  have heq := constant_of_has_deriv_right_zero hc hz t ht
  rw [bondPrice_zero, div_one, hB₀, div_eq_iff (hne t), bondPrice_eq_of_eqOn hρ ht] at heq
  rw [heq, ← bondPrice_mul_left, mul_one]

/-! ### Trading the bond -/

/-- Trading the bond with a simple holding `b` whose first date is nonnegative gains the time
integral of the holding against the interest rate: the elementary integral `∫₀ᵗ b dβ` is
`∫₀ᵗ b_u r_u β_u du` whenever the short rate is continuous on `[0, t]`. -/
theorem simpleGains_bondPrice {Ω : Type*} {τ : ℕ → ℝ} {n : ℕ} (hr : ContinuousOn r (Icc 0 t))
    (β₀ : ℝ) (hτ : MonotoneOn τ (Iic n)) (hτ₀ : 0 ≤ τ 0) (b : ℕ → Ω → ℝ) (ω : Ω) :
    simpleGains τ n b (fun s _ ↦ bondPrice r β₀ s) t ω =
      ∫ u in 0..t, simpleHolding τ n b u ω * (r u * bondPrice r β₀ u) := by
  refine simpleGains_eq_integral (X' := fun u _ ↦ r u * bondPrice r β₀ u) hτ hτ₀ ω
    (hr.mul (continuousOn_bondPrice hr β₀)).integrableOn_Icc (fun x hx ↦ ?_) b
  rw [integral_mul_bondPrice hr β₀ ⟨le_rfl, hx.1.trans hx.2⟩ hx, bondPrice_zero]
  ring

end TauCeti.Finance
