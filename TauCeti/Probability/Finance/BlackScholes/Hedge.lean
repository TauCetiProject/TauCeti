/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Greeks
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# The Black–Scholes delta hedge

A price `V` of an option, as a function of the spot, is replicated by the *delta hedge*: hold
`a = ∂V/∂s` shares of stock and put the rest of the value, `V - s ∂V/∂s`, into the bond. When one
bond share costs `β`, the hedge holds `b = (V - s ∂V/∂s) / β` bond shares
(`TauCeti.BlackScholes.hedgeBondHolding`), and its wealth `a s + b β` is the price `V`.

For the closed-form Black–Scholes prices the bond holdings are

* call: `b = -K e^{-rτ} Φ(d₋) / β`, which is negative (the hedge borrows);
* put: `b = K e^{-rτ} Φ(-d₋) / β`, which is positive (the hedge lends),

complementing the deltas `Φ(d₊)` and `-Φ(-d₊)` of
`TauCeti.Probability.Finance.BlackScholes.Greeks`.

Since the delta hedge holds `∂V/∂s` shares of stock, its diffusion part matches that of the
price automatically, and only the drifts can differ. Pointwise, for a price `V(s, t)` in calendar
time, a stock with drift `μ` and volatility `σ`, and a bond with `dβ = r β dt`, the Itô drift
`V_t + μ s V_s + σ² s² / 2 V_ss` of `V(S_t, t)` equals the drift `μ s a + r β b` of the hedge
portfolio exactly when `V_t + σ² s² / 2 V_ss + r (s V_s - V) = 0`
(`TauCeti.BlackScholes.itoDrift_eq_hedgeDrift_iff_pde`). Both sides of the drift identity are
deterministic functions of `(s, t)`; this file proves the algebra and does not set up the
stochastic market. Applied to the Black–Scholes equation for the call and the put, this identifies
the drift of each price with the drift of its delta hedge, for every stock drift `μ`.

## Main declarations

* `TauCeti.BlackScholes.hedgeBondHolding` — the bond holding of the delta hedge.
* `TauCeti.BlackScholes.mul_deriv_add_mul_hedgeBondHolding` — the hedge's wealth is the price.
* `TauCeti.BlackScholes.hedgeBondHolding_callPrice`,
  `TauCeti.BlackScholes.hedgeBondHolding_callPrice_neg` — the call bond holding and its sign.
* `TauCeti.BlackScholes.hedgeBondHolding_putPrice`,
  `TauCeti.BlackScholes.hedgeBondHolding_putPrice_pos` — the put bond holding and its sign.
* `TauCeti.BlackScholes.itoDrift_eq_hedgeDrift_iff_pde` — the drift of a price matches the drift
  of its delta hedge iff the price solves the Black–Scholes equation.
* `TauCeti.BlackScholes.callPrice_itoDrift_eq_hedgeDrift`,
  `TauCeti.BlackScholes.putPrice_itoDrift_eq_hedgeDrift` — the matching drifts for the call and
  the put.

## References

* F. Black, M. Scholes, *The pricing of options and corporate liabilities*, J. Polit. Econ. 81
  (1973), 637–654.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open ProbabilityTheory Real

namespace TauCeti.BlackScholes

variable {s r σ K τ β : ℝ}

/-! ### The bond holding of the delta hedge -/

/-- The bond holding of the delta hedge of a price `V` of the spot, at spot `s`, when one bond
share costs `β`. The hedge holds `deriv V s` shares of stock and finances the rest of the value,
`V s - s * deriv V s`, with `(V s - s * deriv V s) / β` bond shares. -/
def hedgeBondHolding (V : ℝ → ℝ) (s β : ℝ) : ℝ :=
  (V s - s * deriv V s) / β

/-- Unfolding lemma for `hedgeBondHolding`. -/
theorem hedgeBondHolding_def (V : ℝ → ℝ) (s β : ℝ) :
    hedgeBondHolding V s β = (V s - s * deriv V s) / β :=
  (rfl)

/-- The wealth of the delta hedge is the price: `deriv V s` shares of stock at spot `s` together
with `hedgeBondHolding V s β` bond shares at price `β` are worth `V s`. -/
theorem mul_deriv_add_mul_hedgeBondHolding (V : ℝ → ℝ) (s : ℝ) (hβ : β ≠ 0) :
    s * deriv V s + β * hedgeBondHolding V s β = V s := by
  rw [hedgeBondHolding_def, mul_div_cancel₀ _ hβ]
  ring

/-- **Call bond holding.** The delta hedge of the Black–Scholes call holds
`-K e^{-rτ} Φ(d₋) / β` bond shares. -/
@[simp]
theorem hedgeBondHolding_callPrice (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ)
    (β : ℝ) :
    hedgeBondHolding (fun x => callPrice x r σ K τ) s β =
      -(K * exp (-r * τ) * cdf (gaussianReal 0 1) (dMinus s r σ K τ)) / β := by
  rw [hedgeBondHolding_def, deriv_callPrice_spot hs hK hσ hτ, callPrice_def]
  ring

/-- The call's delta hedge is short the bond: its bond holding is negative. -/
theorem hedgeBondHolding_callPrice_neg (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ)
    (hβ : 0 < β) : hedgeBondHolding (fun x => callPrice x r σ K τ) s β < 0 := by
  rw [hedgeBondHolding_callPrice hs hK hσ hτ]
  have := TauCeti.Probability.cdf_gaussianReal_pos 0 one_ne_zero (dMinus s r σ K τ)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hβ

/-- **Put bond holding.** The delta hedge of the Black–Scholes put holds
`K e^{-rτ} Φ(-d₋) / β` bond shares. -/
@[simp]
theorem hedgeBondHolding_putPrice (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ)
    (β : ℝ) :
    hedgeBondHolding (fun x => putPrice x r σ K τ) s β =
      K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus s r σ K τ) / β := by
  rw [hedgeBondHolding_def, deriv_putPrice_spot hs hK hσ hτ, putPrice_def]
  ring

/-- The put's delta hedge is long the bond: its bond holding is positive. -/
theorem hedgeBondHolding_putPrice_pos (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ)
    (hβ : 0 < β) : 0 < hedgeBondHolding (fun x => putPrice x r σ K τ) s β := by
  rw [hedgeBondHolding_putPrice hs hK hσ hτ]
  have := TauCeti.Probability.cdf_gaussianReal_pos 0 one_ne_zero (-dMinus s r σ K τ)
  positivity

/-! ### Drift matching and the Black–Scholes equation -/

/-- **Drift matching for the delta hedge.** Let `V(s, t)` be a price in calendar time, let the
stock have drift `μ` and volatility `σ`, and let the bond, at price `β`, grow at rate `r`. The Itô
drift `V_t + μ s V_s + σ² s² / 2 V_ss` of `V(S_t, t)` equals the drift `μ s a + r β b` of the
delta hedge `a = V_s`, `b = hedgeBondHolding (V · t) s β` exactly when `V` satisfies the
Black–Scholes equation `V_t + σ² s² / 2 V_ss + r (s V_s - V) = 0` at `(s, t)`. -/
theorem itoDrift_eq_hedgeDrift_iff_pde (V : ℝ → ℝ → ℝ) (μ σ r s t : ℝ) (hβ : β ≠ 0) :
    deriv (fun u => V s u) t + μ * s * deriv (fun x => V x t) s +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => V x t) s =
      μ * s * deriv (fun x => V x t) s + r * β * hedgeBondHolding (fun x => V x t) s β ↔
    deriv (fun u => V s u) t + σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => V x t) s +
      r * (s * deriv (fun x => V x t) s - V s t) = 0 := by
  have hV := mul_deriv_add_mul_hedgeBondHolding (fun x => V x t) s hβ
  constructor <;> intro h
  · linear_combination h + r * hV
  · linear_combination h - r * hV

/-- **Drift of the call's delta hedge.** In calendar time `t < T`, the Itô drift of the
Black–Scholes call price `C(s, t) = callPrice s r σ K (T - t)` under a stock drift `μ` equals
the drift of its delta hedge with a bond at price `β ≠ 0` growing at rate `r`. -/
theorem callPrice_itoDrift_eq_hedgeDrift (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (μ : ℝ) {T t : ℝ} (ht : t < T) :
    deriv (fun u => callPrice s r σ K (T - u)) t +
        μ * s * deriv (fun x => callPrice x r σ K (T - t)) s +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => callPrice x r σ K (T - t)) s =
      μ * s * deriv (fun x => callPrice x r σ K (T - t)) s +
        r * β * hedgeBondHolding (fun x => callPrice x r σ K (T - t)) s β :=
  (itoDrift_eq_hedgeDrift_iff_pde (fun x u => callPrice x r σ K (T - u)) μ σ r s t hβ).2
    (callPrice_pde hs hK hσ ht)

/-- **Drift of the put's delta hedge.** In calendar time `t < T`, the Itô drift of the
Black–Scholes put price `P(s, t) = putPrice s r σ K (T - t)` under a stock drift `μ` equals
the drift of its delta hedge with a bond at price `β ≠ 0` growing at rate `r`. -/
theorem putPrice_itoDrift_eq_hedgeDrift (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (μ : ℝ) {T t : ℝ} (ht : t < T) :
    deriv (fun u => putPrice s r σ K (T - u)) t +
        μ * s * deriv (fun x => putPrice x r σ K (T - t)) s +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => putPrice x r σ K (T - t)) s =
      μ * s * deriv (fun x => putPrice x r σ K (T - t)) s +
        r * β * hedgeBondHolding (fun x => putPrice x r σ K (T - t)) s β :=
  (itoDrift_eq_hedgeDrift_iff_pde (fun x u => putPrice x r σ K (T - u)) μ σ r s t hβ).2
    (putPrice_pde hs hK hσ ht)

end TauCeti.BlackScholes
