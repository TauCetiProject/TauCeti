/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Geometric
public import TauCeti.Probability.Finance.BlackScholes.Basic

/-!
# Black–Scholes prices as expectations under geometric Brownian motion

`TauCeti.BlackScholes.riskNeutralPrice h s r σ τ` is defined as a Gaussian integral: the
discounted expectation of `h (terminalSpot s r σ τ Z)` for a standard Gaussian coordinate `Z`.
This file identifies it with an expectation over a probability space carrying a Brownian motion
`W`. The geometric Brownian motion `S_t = s * exp ((r - σ² / 2) t + σ W_t)` with drift equal to
the interest rate `r` has, at time `t`, the law of `terminalSpot s r σ t Z`, so

`riskNeutralPrice h s r σ t = e^{-r t} E[h (S_t)]`.

In the Black–Scholes market `W` is a Brownian motion under the risk-neutral measure, and `S` is
the stock price under that measure. Together with `TauCeti.BlackScholes.riskNeutralPrice_call`
and `TauCeti.BlackScholes.riskNeutralPrice_put`, this gives the closed-form call and put prices
as the discounted expected payoffs `e^{-r t} E[(S_t - K)⁺]` and `e^{-r t} E[(K - S_t)⁺]`. The
discounted stock `e^{-r t} S_t` is a martingale by
`TauCeti.Probability.IsFilteredPreBrownianReal.martingale_discounted_geometricBrownianMotion`.

## Main declarations

* `ProbabilityTheory.IsPreBrownianReal.hasLaw_geometricBrownianMotion_terminalSpot`: `S_t` has
  the law of `terminalSpot s r σ t Z`, `Z ∼ N(0, 1)`.
* `ProbabilityTheory.IsPreBrownianReal.riskNeutralPrice_eq_integral_geometricBrownianMotion`:
  `riskNeutralPrice h s r σ t = e^{-r t} E[h (S_t)]`.
* `ProbabilityTheory.IsPreBrownianReal.callPrice_eq_integral_geometricBrownianMotion`,
  `ProbabilityTheory.IsPreBrownianReal.putPrice_eq_integral_geometricBrownianMotion`: the
  Black–Scholes call and put prices are the discounted expected payoffs.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real TauCeti.Probability TauCeti.BlackScholes
open scoped NNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {s r σ K : ℝ} {t : ℝ≥0}

/-- A geometric Brownian motion with drift `r` has at time `t` the law of the risk-neutral
terminal spot `terminalSpot s r σ t Z`, `Z ∼ N(0, 1)`. -/
theorem hasLaw_geometricBrownianMotion_terminalSpot (hB : IsPreBrownianReal B P) (s r σ : ℝ)
    (t : ℝ≥0) :
    HasLaw (geometricBrownianMotion s r σ B t) ((gaussianReal 0 1).map (terminalSpot s r σ t))
      P := by
  set G : ℝ → ℝ := fun x ↦ s * exp ((r - σ ^ 2 / 2) * t + σ * x)
  -- `W_t ∼ N(0, t)` is the image of `Z ∼ N(0, 1)` under `z ↦ √t z`, and `G (√t z)` is the
  -- terminal spot.
  have hW : (gaussianReal 0 1).map (√(t : ℝ) * ·) = gaussianReal 0 t := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr
    simp
  have hG : HasLaw G ((gaussianReal 0 1).map (terminalSpot s r σ t)) (gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← hW, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext z
    simp only [G, Function.comp_apply, terminalSpot_def, mul_assoc]
  have hS : geometricBrownianMotion s r σ B t = G ∘ B t :=
    funext fun ω ↦ geometricBrownianMotion_def s r σ B t ω
  rw [hS]
  exact hG.comp (hB.hasLaw_eval t)

/-- **Risk-neutral prices as expectations.** The risk-neutral price of a payoff `h` at remaining
maturity `t` is the discounted expectation `e^{-r t} E[h (S_t)]` of the payoff of the geometric
Brownian motion `S` with drift `r`. -/
theorem riskNeutralPrice_eq_integral_geometricBrownianMotion (hB : IsPreBrownianReal B P)
    {h : ℝ → ℝ} (hh : AEStronglyMeasurable h (P.map (geometricBrownianMotion s r σ B t))) :
    riskNeutralPrice h s r σ t =
      exp (-r * t) * ∫ ω, h (geometricBrownianMotion s r σ B t ω) ∂P := by
  have hS := hB.hasLaw_geometricBrownianMotion_terminalSpot s r σ t
  rw [hS.map_eq] at hh
  rw [riskNeutralPrice_def, ← integral_map (measurable_terminalSpot s r σ t).aemeasurable hh]
  exact congrArg _ (hS.integral_comp hh).symm

/-- **The Black–Scholes call price as an expectation.** For `s, σ, K > 0` and maturity `t > 0`,
the call price is the discounted expected payoff `e^{-r t} E[(S_t - K)⁺]` of the geometric
Brownian motion `S` with drift `r`. -/
theorem callPrice_eq_integral_geometricBrownianMotion (hB : IsPreBrownianReal B P) (hs : 0 < s)
    (hσ : 0 < σ) (hK : 0 < K) (ht : 0 < t) :
    callPrice s r σ K t = exp (-r * t) * ∫ ω, (geometricBrownianMotion s r σ B t ω - K)⁺ ∂P := by
  rw [← riskNeutralPrice_call hs hσ hK (NNReal.coe_pos.2 ht),
    hB.riskNeutralPrice_eq_integral_geometricBrownianMotion (by fun_prop)]

/-- **The Black–Scholes put price as an expectation.** For `s, σ, K > 0` and maturity `t > 0`,
the put price is the discounted expected payoff `e^{-r t} E[(K - S_t)⁺]` of the geometric
Brownian motion `S` with drift `r`. -/
theorem putPrice_eq_integral_geometricBrownianMotion (hB : IsPreBrownianReal B P) (hs : 0 < s)
    (hσ : 0 < σ) (hK : 0 < K) (ht : 0 < t) :
    putPrice s r σ K t = exp (-r * t) * ∫ ω, (K - geometricBrownianMotion s r σ B t ω)⁺ ∂P := by
  rw [← riskNeutralPrice_put hs hσ hK (NNReal.coe_pos.2 ht),
    hB.riskNeutralPrice_eq_integral_geometricBrownianMotion (by fun_prop)]

end ProbabilityTheory.IsPreBrownianReal
