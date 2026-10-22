/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# The Black–Scholes Greeks and the Black–Scholes equation

This file differentiates the closed-form Black–Scholes prices
`C = s Φ(d₊) - K e^{-rτ} Φ(d₋)` and `P = K e^{-rτ} Φ(-d₋) - s Φ(-d₊)` of
`TauCeti.Probability.Finance.BlackScholes.Basic` in the spot `s`, the remaining maturity `τ` and
the volatility `σ`, and shows that both prices solve the Black–Scholes equation. Here `Φ` is the
standard Gaussian cdf and `φ = gaussianPDFReal 0 1` its density.

Everything rests on the identity `s φ(d₊) = K e^{-rτ} φ(d₋)`
(`TauCeti.BlackScholes.mul_gaussianPDFReal_dPlus`, proved with the formulas), which says that
the terms produced by differentiating `d₊` and `d₋` cancel. With it the Greeks of the call are

* delta `∂C/∂s = Φ(d₊)`, which lies in `(0, 1)`;
* gamma `∂²C/∂s² = φ(d₊) / (s σ √τ)`, positive for `σ > 0`;
* `∂C/∂τ = s φ(d₊) σ / (2 √τ) + r K e^{-rτ} Φ(d₋)`;
* vega `∂C/∂σ = s φ(d₊) √τ`, which is positive.

The put has delta `-Φ(-d₊) ∈ (-1, 0)`, the same gamma and vega, and
`∂P/∂τ = s φ(d₊) σ / (2 √τ) - r K e^{-rτ} Φ(-d₋)`.

In calendar time `t = T - τ` both `V(s, t) = C(s, T - t)` and `V(s, t) = P(s, T - t)` satisfy

`∂V/∂t + σ² s² / 2 ∂²V/∂s² + r (s ∂V/∂s - V) = 0`

for `s > 0` and `t < T` (`TauCeti.BlackScholes.callPrice_pde`,
`TauCeti.BlackScholes.putPrice_pde`). The formulas for the derivatives and the equation only need
`σ ≠ 0`; the signs of gamma need `σ > 0`.

## Main declarations

* `TauCeti.BlackScholes.hasDerivAt_callPrice_spot` — the call delta.
* `TauCeti.BlackScholes.hasDerivAt_deriv_callPrice_spot` — the call gamma.
* `TauCeti.BlackScholes.hasDerivAt_callPrice_maturity` — the derivative of the call in `τ`.
* `TauCeti.BlackScholes.hasDerivAt_callPrice_volatility` — the call vega.
* `TauCeti.BlackScholes.deriv_callPrice_spot_mem_Ioo` — `0 < ∂C/∂s < 1`.
* The corresponding `putPrice` statements.
* `TauCeti.BlackScholes.abs_callPrice_sub_callPrice_le` — the call is `1`-Lipschitz in the spot
  on `s > 0` (for `τ > 0`, `σ ≠ 0`, `K > 0`).
* `TauCeti.BlackScholes.callPrice_pde`, `TauCeti.BlackScholes.putPrice_pde` — the Black–Scholes
  equation.

## References

* F. Black, M. Scholes, *The pricing of options and corporate liabilities*, J. Polit. Econ. 81
  (1973), 637–654.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.5.
-/

public section

noncomputable section

open Filter ProbabilityTheory Real Set TauCeti.Probability
open scoped Topology

namespace TauCeti.BlackScholes

variable {s r σ K τ : ℝ}

/-! ### Derivatives of `d₊` and `d₋` in the spot -/

/-- The derivative of `d₊` in the spot is `1 / (s σ √τ)`. -/
private theorem hasDerivAt_dPlus_spot (hs : s ≠ 0) (hK : K ≠ 0) :
    HasDerivAt (fun x => dPlus x r σ K τ) (1 / (s * (σ * √τ))) s := by
  have h := ((((hasDerivAt_id s).div_const K).log (div_ne_zero hs hK)).add_const
    ((r + σ ^ 2 / 2) * τ)).div_const (σ * √τ)
  simp only [id_eq] at h
  simp only [dPlus_def]
  convert h using 1
  field_simp

/-- The derivative of `d₋` in the spot is `1 / (s σ √τ)`. -/
private theorem hasDerivAt_dMinus_spot (hs : s ≠ 0) (hK : K ≠ 0) :
    HasDerivAt (fun x => dMinus x r σ K τ) (1 / (s * (σ * √τ))) s := by
  simp only [dMinus_def]
  exact (hasDerivAt_dPlus_spot hs hK).sub_const _

/-! ### Greeks of the call -/

/-- **Call delta.** The derivative of the Black–Scholes call price in the spot is `Φ(d₊)`. -/
theorem hasDerivAt_callPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (fun x => callPrice x r σ K τ) (cdf (gaussianReal 0 1) (dPlus s r σ K τ)) s := by
  have hp := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp s
    (hasDerivAt_dPlus_spot (r := r) (σ := σ) (τ := τ) hs.ne' hK.ne')
  have hm := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp s
    (hasDerivAt_dMinus_spot (r := r) (σ := σ) (τ := τ) hs.ne' hK.ne')
  have h := ((hasDerivAt_id s).mul hp).sub (hm.const_mul (K * exp (-r * τ)))
  convert h using 1
  · ext x
    simp [callPrice_def]
  · simp only [id_eq, Function.comp_apply]
    linear_combination (-1 / (s * (σ * √τ))) * mul_gaussianPDFReal_dPlus (r := r) hs hK hσ hτ

/-- **Call delta.** The derivative of the Black–Scholes call price in the spot is `Φ(d₊)`. -/
@[simp]
theorem deriv_callPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    deriv (fun x => callPrice x r σ K τ) s = cdf (gaussianReal 0 1) (dPlus s r σ K τ) :=
  (hasDerivAt_callPrice_spot hs hK hσ hτ).deriv

/-- The call delta lies strictly between `0` and `1`. -/
theorem deriv_callPrice_spot_mem_Ioo (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    deriv (fun x => callPrice x r σ K τ) s ∈ Ioo 0 1 := by
  rw [deriv_callPrice_spot hs hK hσ hτ]
  exact ⟨cdf_gaussianReal_pos 0 one_ne_zero _,
    cdf_gaussianReal_lt_one 0 one_ne_zero _⟩

/-- The Black–Scholes call price is `1`-Lipschitz in the spot on `s > 0`, for `τ > 0`, `σ ≠ 0`
and `K > 0`. -/
theorem abs_callPrice_sub_callPrice_le {x : ℝ} (hx : 0 < x) (hs : 0 < s) (hK : 0 < K)
    (hσ : σ ≠ 0) (hτ : 0 < τ) :
    |callPrice x r σ K τ - callPrice s r σ K τ| ≤ |x - s| := by
  have h := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => callPrice y r σ K τ) (C := 1)
    (fun y hy => (hasDerivAt_callPrice_spot (r := r) hy hK hσ hτ).hasDerivWithinAt)
    (fun y _ => by
      rw [norm_of_nonneg (cdf_nonneg _ _)]
      exact cdf_le_one _ _) hs hx
  simpa only [norm_eq_abs, one_mul] using h

/-- **Call gamma.** The second derivative of the Black–Scholes call price in the spot is
`φ(d₊) / (s σ √τ)`. -/
theorem hasDerivAt_deriv_callPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (deriv fun x => callPrice x r σ K τ)
      (gaussianPDFReal 0 1 (dPlus s r σ K τ) / (s * (σ * √τ))) s := by
  have h := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp s
    (hasDerivAt_dPlus_spot (r := r) (σ := σ) (τ := τ) hs.ne' hK.ne')
  rw [← mul_one_div]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact deriv_callPrice_spot hx hK hσ hτ

/-- Call gamma is positive when the volatility is. -/
theorem deriv_deriv_callPrice_spot_pos (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < deriv (deriv fun x => callPrice x r σ K τ) s := by
  rw [(hasDerivAt_deriv_callPrice_spot hs hK hσ.ne' hτ).deriv]
  have := gaussianPDFReal_pos 0 1 (dPlus s r σ K τ) one_ne_zero
  positivity

/-- The derivative of the Black–Scholes call price in the remaining maturity is
`s φ(d₊) σ / (2 √τ) + r K e^{-rτ} Φ(d₋)`. -/
theorem hasDerivAt_callPrice_maturity (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (callPrice s r σ K)
      (s * gaussianPDFReal 0 1 (dPlus s r σ K τ) * σ / (2 * √τ) +
        r * K * exp (-r * τ) * cdf (gaussianReal 0 1) (dMinus s r σ K τ)) τ := by
  have hsqrt : HasDerivAt (fun u => σ * √u) (σ * (1 / (2 * √τ))) τ :=
    (hasDerivAt_sqrt hτ.ne').const_mul σ
  -- The value of `∂d₊/∂τ` is irrelevant: its two contributions cancel.
  obtain ⟨D, hd⟩ : ∃ D, HasDerivAt (dPlus s r σ K) D τ := by
    have h := (((hasDerivAt_id τ).const_mul (r + σ ^ 2 / 2)).const_add (log (s / K))).div hsqrt
      (mul_ne_zero hσ (sqrt_pos.2 hτ).ne')
    refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)⟩
    simp [dPlus_def]
  have hdm : HasDerivAt (dMinus s r σ K) (D - σ * (1 / (2 * √τ))) τ :=
    (hd.sub hsqrt).congr_of_eventuallyEq (Eventually.of_forall fun u => dMinus_def s r σ K u)
  have he : HasDerivAt (fun u => exp (-r * u)) (exp (-r * τ) * (-r * 1)) τ :=
    ((hasDerivAt_id τ).const_mul (-r)).exp
  have h := (((hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp τ hd).const_mul s).sub
    ((he.const_mul K).mul ((hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp τ hdm))
  convert h using 1
  · ext u
    simp [callPrice_def]
  · simp only [Function.comp_apply]
    linear_combination (σ * (1 / (2 * √τ)) - D) * mul_gaussianPDFReal_dPlus (r := r) hs hK hσ hτ

/-- **Call vega.** The derivative of the Black–Scholes call price in the volatility is
`s φ(d₊) √τ`. -/
theorem hasDerivAt_callPrice_volatility (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (fun v => callPrice s r v K τ)
      (s * gaussianPDFReal 0 1 (dPlus s r σ K τ) * √τ) σ := by
  have hlin : HasDerivAt (fun v => v * √τ) (1 * √τ) σ := (hasDerivAt_id σ).mul_const √τ
  -- The value of `∂d₊/∂σ` is irrelevant: its two contributions cancel.
  obtain ⟨D, hd⟩ : ∃ D, HasDerivAt (fun v => dPlus s r v K τ) D σ := by
    have h := ((((hasDerivAt_pow 2 σ).div_const 2).const_add r).mul_const τ).const_add
      (log (s / K)) |>.div hlin (mul_ne_zero hσ (sqrt_pos.2 hτ).ne')
    refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)⟩
    simp [dPlus_def]
  have hdm : HasDerivAt (fun v => dMinus s r v K τ) (D - 1 * √τ) σ := by
    simp only [dMinus_def]
    exact hd.sub hlin
  have h := (((hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp σ hd).const_mul s).sub
    (((hasDerivAt_cdf_gaussianReal 0 one_ne_zero _).comp σ hdm).const_mul
      (K * exp (-r * τ)))
  convert h using 1
  · ext v
    simp [callPrice_def]
  · linear_combination (1 * √τ - D) * mul_gaussianPDFReal_dPlus (r := r) hs hK hσ hτ

/-- Call vega is positive. -/
theorem deriv_callPrice_volatility_pos (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    0 < deriv (fun v => callPrice s r v K τ) σ := by
  rw [(hasDerivAt_callPrice_volatility hs hK hσ hτ).deriv]
  have := gaussianPDFReal_pos 0 1 (dPlus s r σ K τ) one_ne_zero
  have := sqrt_pos.2 hτ
  positivity

/-! ### Greeks of the put -/

/-- **Put delta.** The derivative of the Black–Scholes put price in the spot is `-Φ(-d₊)`. -/
theorem hasDerivAt_putPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (fun x => putPrice x r σ K τ) (-cdf (gaussianReal 0 1) (-dPlus s r σ K τ)) s := by
  have h := ((hasDerivAt_callPrice_spot (r := r) hs hK hσ hτ).sub (hasDerivAt_id s)).add_const
    (K * exp (-r * τ))
  convert h using 1
  · ext x
    simp [putPrice_eq_callPrice]
  · rw [cdf_gaussianReal_zero_one_neg]
    ring

/-- **Put delta.** The derivative of the Black–Scholes put price in the spot is `-Φ(-d₊)`. -/
@[simp]
theorem deriv_putPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    deriv (fun x => putPrice x r σ K τ) s = -cdf (gaussianReal 0 1) (-dPlus s r σ K τ) :=
  (hasDerivAt_putPrice_spot hs hK hσ hτ).deriv

/-- The put delta lies strictly between `-1` and `0`. -/
theorem deriv_putPrice_spot_mem_Ioo (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    deriv (fun x => putPrice x r σ K τ) s ∈ Ioo (-1) 0 := by
  rw [deriv_putPrice_spot hs hK hσ hτ]
  exact ⟨neg_lt_neg (cdf_gaussianReal_lt_one 0 one_ne_zero _),
    neg_neg_of_pos (cdf_gaussianReal_pos 0 one_ne_zero _)⟩

/-- **Put gamma.** The second derivative of the Black–Scholes put price in the spot is
`φ(d₊) / (s σ √τ)`, the call gamma. -/
theorem hasDerivAt_deriv_putPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (deriv fun x => putPrice x r σ K τ)
      (gaussianPDFReal 0 1 (dPlus s r σ K τ) / (s * (σ * √τ))) s := by
  refine ((hasDerivAt_deriv_callPrice_spot hs hK hσ hτ).sub_const 1).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  rw [deriv_putPrice_spot hx hK hσ hτ, deriv_callPrice_spot hx hK hσ hτ,
    cdf_gaussianReal_zero_one_neg]
  ring

/-- Put gamma equals call gamma. -/
theorem deriv_deriv_putPrice_spot (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    deriv (deriv fun x => putPrice x r σ K τ) s =
      deriv (deriv fun x => callPrice x r σ K τ) s := by
  rw [(hasDerivAt_deriv_putPrice_spot hs hK hσ hτ).deriv,
    (hasDerivAt_deriv_callPrice_spot hs hK hσ hτ).deriv]

/-- Put gamma is positive when the volatility is. -/
theorem deriv_deriv_putPrice_spot_pos (hs : 0 < s) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < deriv (deriv fun x => putPrice x r σ K τ) s := by
  rw [deriv_deriv_putPrice_spot hs hK hσ.ne' hτ]
  exact deriv_deriv_callPrice_spot_pos hs hK hσ hτ

/-- The derivative of the Black–Scholes put price in the remaining maturity is
`s φ(d₊) σ / (2 √τ) - r K e^{-rτ} Φ(-d₋)`. -/
theorem hasDerivAt_putPrice_maturity (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (putPrice s r σ K)
      (s * gaussianPDFReal 0 1 (dPlus s r σ K τ) * σ / (2 * √τ) -
        r * K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus s r σ K τ)) τ := by
  have he : HasDerivAt (fun u => exp (-r * u)) (exp (-r * τ) * (-r * 1)) τ :=
    ((hasDerivAt_id τ).const_mul (-r)).exp
  have h := ((hasDerivAt_callPrice_maturity (r := r) hs hK hσ hτ).sub_const s).add
    (he.const_mul K)
  convert h using 1
  · ext u
    simp [putPrice_eq_callPrice]
  · rw [cdf_gaussianReal_zero_one_neg]
    ring

/-- **Put vega.** The derivative of the Black–Scholes put price in the volatility is
`s φ(d₊) √τ`, the call vega. -/
theorem hasDerivAt_putPrice_volatility (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    HasDerivAt (fun v => putPrice s r v K τ)
      (s * gaussianPDFReal 0 1 (dPlus s r σ K τ) * √τ) σ := by
  have h := ((hasDerivAt_callPrice_volatility (r := r) hs hK hσ hτ).sub_const s).add_const
    (K * exp (-r * τ))
  convert h using 1
  ext v
  simp [putPrice_eq_callPrice]

/-- Put vega is positive. -/
theorem deriv_putPrice_volatility_pos (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    0 < deriv (fun v => putPrice s r v K τ) σ := by
  rw [(hasDerivAt_putPrice_volatility hs hK hσ hτ).deriv,
    ← (hasDerivAt_callPrice_volatility hs hK hσ hτ).deriv]
  exact deriv_callPrice_volatility_pos hs hK hσ hτ

/-! ### The Black–Scholes equation -/

/-- **The Black–Scholes equation for the call.** In calendar time `t < T`, the call price
`C(s, t) = callPrice s r σ K (T - t)` satisfies
`∂C/∂t + σ² s² / 2 ∂²C/∂s² + r (s ∂C/∂s - C) = 0` at every spot `s > 0`. -/
theorem callPrice_pde (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) {T t : ℝ} (ht : t < T) :
    deriv (fun u => callPrice s r σ K (T - u)) t +
      σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => callPrice x r σ K (T - t)) s +
      r * (s * deriv (fun x => callPrice x r σ K (T - t)) s - callPrice s r σ K (T - t)) = 0 := by
  have hτ : 0 < T - t := sub_pos.2 ht
  rw [((hasDerivAt_callPrice_maturity (r := r) hs hK hσ hτ).comp_const_sub T t).deriv,
    (hasDerivAt_deriv_callPrice_spot hs hK hσ hτ).deriv, deriv_callPrice_spot hs hK hσ hτ,
    callPrice_def]
  have := (sqrt_pos.2 hτ).ne'
  field_simp
  ring

/-- **The Black–Scholes equation for the put.** In calendar time `t < T`, the put price
`P(s, t) = putPrice s r σ K (T - t)` satisfies
`∂P/∂t + σ² s² / 2 ∂²P/∂s² + r (s ∂P/∂s - P) = 0` at every spot `s > 0`. -/
theorem putPrice_pde (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) {T t : ℝ} (ht : t < T) :
    deriv (fun u => putPrice s r σ K (T - u)) t +
      σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => putPrice x r σ K (T - t)) s +
      r * (s * deriv (fun x => putPrice x r σ K (T - t)) s - putPrice s r σ K (T - t)) = 0 := by
  have hτ : 0 < T - t := sub_pos.2 ht
  rw [((hasDerivAt_putPrice_maturity (r := r) hs hK hσ hτ).comp_const_sub T t).deriv,
    (hasDerivAt_deriv_putPrice_spot hs hK hσ hτ).deriv, deriv_putPrice_spot hs hK hσ hτ,
    putPrice_def]
  have := (sqrt_pos.2 hτ).ne'
  field_simp
  ring

end TauCeti.BlackScholes
