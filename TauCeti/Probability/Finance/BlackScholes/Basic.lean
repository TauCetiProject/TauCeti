/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Distributions.Tilted

/-!
# Black–Scholes call and put prices as risk-neutral expectations

In the constant-coefficient Black–Scholes market with interest rate `r` and volatility `σ`, the
spot price after a remaining maturity `τ ≥ 0`, started from spot `s`, has under the risk-neutral
measure the law of

`S_τ = s * exp ((r - σ² / 2) * τ + σ * √τ * Z)`,  `Z ∼ N(0, 1)`.

This file works in that standard Gaussian coordinate. It defines `S_τ` as a function of `Z`
(`TauCeti.BlackScholes.terminalSpot`), the discounted risk-neutral expectation
`exp (-r τ) * E[h (S_τ)]` of a payoff `h` (`TauCeti.BlackScholes.riskNeutralPrice`), and the
closed-form Black–Scholes prices

`C = s Φ(d₊) - K e^{-rτ} Φ(d₋)`,  `P = K e^{-rτ} Φ(-d₋) - s Φ(-d₊)`,

with `d₊ = (log (s / K) + (r + σ² / 2) τ) / (σ √τ)` and `d₋ = d₊ - σ √τ`, where `Φ` is the
cumulative distribution function `cdf (gaussianReal 0 1)` of the standard Gaussian law.

The main results identify the two: the risk-neutral price of the call payoff `(x - K)⁺` is `C`
and that of the put payoff `(K - x)⁺` is `P`, for `s, K, σ, τ > 0`. Along the way the discounted
stock has risk-neutral price `s`, and the closed forms satisfy put–call parity
`C - P = s - K e^{-rτ}`.

The computation splits the call payoff on the in-the-money event `{-d₋ < Z}`. The strike part is
a Gaussian tail; the stock part is an exponentially weighted Gaussian tail, which is evaluated by
exponential tilting `N(0, 1) ↦ N(σ √τ, 1)`
(`TauCeti.Probability.setIntegral_exp_mul_gaussianReal`), the change to the stock numéraire.

## Main declarations

* `TauCeti.BlackScholes.terminalSpot` — the risk-neutral terminal spot as a function of the
  standard Gaussian coordinate.
* `TauCeti.BlackScholes.riskNeutralPrice` — the discounted risk-neutral expectation of a payoff.
* `TauCeti.BlackScholes.dPlus`, `TauCeti.BlackScholes.dMinus` — the Black–Scholes `d₊`, `d₋`.
* `TauCeti.BlackScholes.mul_gaussianPDFReal_dPlus` — the density identity
  `s φ(d₊) = K e^{-rτ} φ(d₋)`, where `φ` is the standard Gaussian density.
* `TauCeti.BlackScholes.callPrice`, `TauCeti.BlackScholes.putPrice` — the closed-form prices.
* `TauCeti.BlackScholes.riskNeutralPrice_id` — the discounted stock is priced at `s`.
* `TauCeti.BlackScholes.callPrice_sub_putPrice` — put–call parity.
* `TauCeti.BlackScholes.riskNeutralPrice_call` — the risk-neutral price of a call is `callPrice`.
* `TauCeti.BlackScholes.riskNeutralPrice_put` — the risk-neutral price of a put is `putPrice`.
* `TauCeti.BlackScholes.callPrice_nonneg`, `TauCeti.BlackScholes.callPrice_le`,
  `TauCeti.BlackScholes.putPrice_nonneg`, `TauCeti.BlackScholes.putPrice_le_mul_cdf`,
  `TauCeti.BlackScholes.putPrice_le` — the no-arbitrage bounds `0 ≤ C ≤ s` and
  `0 ≤ P ≤ K e^{-rτ} Φ(-d₋) ≤ K e^{-rτ}`.

## References

* F. Black, M. Scholes, *The pricing of options and corporate liabilities*, J. Polit. Econ. 81
  (1973), 637–654.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.BlackScholes

variable {s r σ K τ : ℝ}

/-! ### The risk-neutral terminal spot and the pricing functional -/

/-- The risk-neutral spot price after remaining maturity `τ`, started from spot `s`, in a market
with interest rate `r` and volatility `σ`, written as a function of a standard Gaussian
coordinate `z`: `s * exp ((r - σ² / 2) * τ + σ * √τ * z)`. -/
def terminalSpot (s r σ τ z : ℝ) : ℝ :=
  s * exp ((r - σ ^ 2 / 2) * τ + σ * √τ * z)

/-- Unfolding lemma for `terminalSpot`. -/
theorem terminalSpot_def (s r σ τ z : ℝ) :
    terminalSpot s r σ τ z = s * exp ((r - σ ^ 2 / 2) * τ + σ * √τ * z) :=
  (rfl)

/-- At zero remaining maturity the terminal spot is the current spot. -/
@[simp]
theorem terminalSpot_zero (s r σ z : ℝ) : terminalSpot s r σ 0 z = s := by
  simp [terminalSpot_def]

/-- The terminal spot is positive when the current spot is. -/
theorem terminalSpot_pos (hs : 0 < s) (r σ τ z : ℝ) : 0 < terminalSpot s r σ τ z := by
  rw [terminalSpot_def]
  positivity

/-- The terminal spot is a measurable function of the Gaussian coordinate. -/
theorem measurable_terminalSpot (s r σ τ : ℝ) : Measurable (terminalSpot s r σ τ) := by
  unfold terminalSpot
  fun_prop

/-- The terminal spot as a constant times the exponential `exp (σ √τ z)`. -/
private theorem terminalSpot_eq_mul_exp (s r σ τ z : ℝ) :
    terminalSpot s r σ τ z = s * exp ((r - σ ^ 2 / 2) * τ) * exp (σ * √τ * z) := by
  rw [terminalSpot_def, exp_add]
  ring

/-- The terminal spot is integrable against the standard Gaussian law. -/
theorem integrable_terminalSpot (s r σ τ : ℝ) :
    Integrable (terminalSpot s r σ τ) (gaussianReal 0 1) := by
  rw [funext (terminalSpot_eq_mul_exp s r σ τ)]
  exact (integrable_exp_mul_gaussianReal (σ * √τ)).const_mul _

/-- **Change to the stock numéraire.** Over any set `A` of Gaussian coordinates, the terminal
spot integrates to its forward value `s * exp (r τ)` times the mass of `A` under the shifted law
`N(σ √τ, 1)`. -/
theorem setIntegral_terminalSpot (s r σ : ℝ) (hτ : 0 ≤ τ) (A : Set ℝ) :
    ∫ z in A, terminalSpot s r σ τ z ∂gaussianReal 0 1 =
      s * exp (r * τ) * (gaussianReal (σ * √τ) 1).real A := by
  simp_rw [terminalSpot_eq_mul_exp]
  rw [integral_const_mul, TauCeti.Probability.setIntegral_exp_mul_gaussianReal]
  have hsq : (σ * √τ) ^ 2 = σ ^ 2 * τ := by rw [mul_pow, sq_sqrt hτ]
  simp only [NNReal.coe_one, zero_mul, zero_add, one_mul, hsq]
  rw [← mul_assoc, mul_assoc s, ← exp_add]
  ring_nf

/-- The discounted risk-neutral expectation `exp (-r τ) * E[h (S_τ)]` of a payoff `h` of the
terminal spot `S_τ = terminalSpot s r σ τ Z`, `Z ∼ N(0, 1)`. For a non-integrable payoff the
Bochner integral, and hence this value, is zero. -/
def riskNeutralPrice (h : ℝ → ℝ) (s r σ τ : ℝ) : ℝ :=
  exp (-r * τ) * ∫ z, h (terminalSpot s r σ τ z) ∂gaussianReal 0 1

/-- Unfolding lemma for `riskNeutralPrice`. -/
theorem riskNeutralPrice_def (h : ℝ → ℝ) (s r σ τ : ℝ) :
    riskNeutralPrice h s r σ τ =
      exp (-r * τ) * ∫ z, h (terminalSpot s r σ τ z) ∂gaussianReal 0 1 :=
  (rfl)

/-- At zero remaining maturity a payoff is priced at its value at the current spot. -/
@[simp]
theorem riskNeutralPrice_zero (h : ℝ → ℝ) (s r σ : ℝ) : riskNeutralPrice h s r σ 0 = h s := by
  simp [riskNeutralPrice_def]

/-- A nonnegative payoff has a nonnegative risk-neutral price. -/
theorem riskNeutralPrice_nonneg {h : ℝ → ℝ} (hh : ∀ x, 0 ≤ h x) (s r σ τ : ℝ) :
    0 ≤ riskNeutralPrice h s r σ τ := by
  rw [riskNeutralPrice_def]
  exact mul_nonneg (exp_pos _).le (integral_nonneg fun z => hh _)

/-- The stock itself, as a payoff, is priced at the current spot: the discounted risk-neutral
expectation `exp (-r τ) * E[S_τ]` of the terminal spot equals `s`. -/
theorem riskNeutralPrice_id (s r σ : ℝ) (hτ : 0 ≤ τ) : riskNeutralPrice id s r σ τ = s := by
  simp only [riskNeutralPrice_def, id_eq]
  rw [← setIntegral_univ, setIntegral_terminalSpot s r σ hτ,
    probReal_univ, mul_one, mul_left_comm, ← exp_add]
  simp

/-! ### The Black–Scholes formulas -/

/-- The Black–Scholes quantity `d₊ = (log (s / K) + (r + σ² / 2) τ) / (σ √τ)`. -/
def dPlus (s r σ K τ : ℝ) : ℝ :=
  (log (s / K) + (r + σ ^ 2 / 2) * τ) / (σ * √τ)

/-- Unfolding lemma for `dPlus`. -/
theorem dPlus_def (s r σ K τ : ℝ) :
    dPlus s r σ K τ = (log (s / K) + (r + σ ^ 2 / 2) * τ) / (σ * √τ) :=
  (rfl)

/-- The Black–Scholes quantity `d₋ = d₊ - σ √τ`. -/
def dMinus (s r σ K τ : ℝ) : ℝ :=
  dPlus s r σ K τ - σ * √τ

/-- Unfolding lemma for `dMinus`. -/
theorem dMinus_def (s r σ K τ : ℝ) : dMinus s r σ K τ = dPlus s r σ K τ - σ * √τ :=
  (rfl)

/-- For `τ ≥ 0`, `d₋ = (log (s / K) + (r - σ² / 2) τ) / (σ √τ)`. When `σ √τ = 0` both sides
vanish. -/
theorem dMinus_eq (s r σ K : ℝ) (hτ : 0 ≤ τ) :
    dMinus s r σ K τ = (log (s / K) + (r - σ ^ 2 / 2) * τ) / (σ * √τ) := by
  rw [dMinus_def, dPlus_def]
  rcases eq_or_ne (σ * √τ) 0 with h | h
  · simp [h]
  · have hsq : (σ * √τ) ^ 2 = σ ^ 2 * τ := by rw [mul_pow, sq_sqrt hτ]
    rw [eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
    linear_combination -1 * hsq

/-! ### The density identity -/

/-- The standard Gaussian density at `d₋` is `φ(d₊) (s / K) e^{rτ}`. -/
private theorem gaussianPDFReal_dMinus (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    gaussianPDFReal 0 1 (dMinus s r σ K τ) =
      gaussianPDFReal 0 1 (dPlus s r σ K τ) * (s / K) * exp (r * τ) := by
  have ha : σ * √τ ≠ 0 := mul_ne_zero hσ (sqrt_pos.2 hτ).ne'
  have hsq : (σ * √τ) ^ 2 = σ ^ 2 * τ := by rw [mul_pow, sq_sqrt hτ.le]
  have hd : dPlus s r σ K τ * (σ * √τ) = log (s / K) + (r + σ ^ 2 / 2) * τ := by
    rw [dPlus_def, div_mul_cancel₀ _ ha]
  -- `-d₋² / 2 = -d₊² / 2 + log (s / K) + r τ`.
  have hexp : exp (-(dPlus s r σ K τ - σ * √τ) ^ 2 / 2) =
      exp (-dPlus s r σ K τ ^ 2 / 2) * (s / K) * exp (r * τ) := by
    rw [← exp_log (div_pos hs hK), ← exp_add, ← exp_add]
    congr 1
    linear_combination hd - hsq / 2
  simp only [gaussianPDFReal_def, dMinus_def, NNReal.coe_one, mul_one, sub_zero]
  rw [hexp]
  ring

/-- The Black–Scholes density identity `s φ(d₊) = K e^{-rτ} φ(d₋)`, where `φ` is the standard
Gaussian density. It expresses that `d₊² - d₋² = 2 (log (s / K) + r τ)`. -/
theorem mul_gaussianPDFReal_dPlus (hs : 0 < s) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    s * gaussianPDFReal 0 1 (dPlus s r σ K τ) =
      K * exp (-r * τ) * gaussianPDFReal 0 1 (dMinus s r σ K τ) := by
  rw [gaussianPDFReal_dMinus hs hK hσ hτ, neg_mul, exp_neg]
  field_simp

/-- The closed-form Black–Scholes price `s Φ(d₊) - K e^{-rτ} Φ(d₋)` of a European call with
strike `K` and remaining maturity `τ`, where `Φ = cdf (gaussianReal 0 1)`. -/
def callPrice (s r σ K τ : ℝ) : ℝ :=
  s * cdf (gaussianReal 0 1) (dPlus s r σ K τ) -
    K * exp (-r * τ) * cdf (gaussianReal 0 1) (dMinus s r σ K τ)

/-- Unfolding lemma for `callPrice`. -/
theorem callPrice_def (s r σ K τ : ℝ) :
    callPrice s r σ K τ = s * cdf (gaussianReal 0 1) (dPlus s r σ K τ) -
      K * exp (-r * τ) * cdf (gaussianReal 0 1) (dMinus s r σ K τ) :=
  (rfl)

/-- The closed-form Black–Scholes price `K e^{-rτ} Φ(-d₋) - s Φ(-d₊)` of a European put with
strike `K` and remaining maturity `τ`, where `Φ = cdf (gaussianReal 0 1)`. -/
def putPrice (s r σ K τ : ℝ) : ℝ :=
  K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus s r σ K τ) -
    s * cdf (gaussianReal 0 1) (-dPlus s r σ K τ)

/-- Unfolding lemma for `putPrice`. -/
theorem putPrice_def (s r σ K τ : ℝ) :
    putPrice s r σ K τ = K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus s r σ K τ) -
      s * cdf (gaussianReal 0 1) (-dPlus s r σ K τ) :=
  (rfl)

/-- **Put–call parity** for the closed-form prices: `C - P = s - K e^{-rτ}`. -/
theorem callPrice_sub_putPrice (s r σ K τ : ℝ) :
    callPrice s r σ K τ - putPrice s r σ K τ = s - K * exp (-r * τ) := by
  rw [callPrice_def, putPrice_def, TauCeti.Probability.cdf_gaussianReal_zero_one_neg,
    TauCeti.Probability.cdf_gaussianReal_zero_one_neg]
  ring

/-- Put–call parity, solved for the put. -/
theorem putPrice_eq_callPrice (s r σ K τ : ℝ) :
    putPrice s r σ K τ = callPrice s r σ K τ - s + K * exp (-r * τ) := by
  linear_combination -callPrice_sub_putPrice s r σ K τ

/-! ### Risk-neutral prices of calls and puts -/

/-- The call finishes in the money exactly on the event `{-d₋ < Z}`. -/
theorem lt_terminalSpot_iff (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) (z : ℝ) :
    K < terminalSpot s r σ τ z ↔ -dMinus s r σ K τ < z := by
  have ha : 0 < σ * √τ := mul_pos hσ (sqrt_pos.2 hτ)
  -- Take logarithms: `K < s e^a` iff `log (K / s) < a`.
  calc K < terminalSpot s r σ τ z ↔ log (K / s) < (r - σ ^ 2 / 2) * τ + σ * √τ * z := by
        rw [terminalSpot_def, ← div_lt_iff₀' hs, log_lt_iff_lt_exp (div_pos hK hs)]
    _ ↔ -dMinus s r σ K τ < z := by
        rw [dMinus_eq s r σ K hτ.le, neg_lt, lt_div_iff₀ ha, log_div hK.ne' hs.ne',
          log_div hs.ne' hK.ne']
        constructor <;> intro h <;> linarith

/-- The strike leg of the call: the in-the-money event `{-d₋ < Z}` has probability `Φ(d₋)`. -/
private theorem measureReal_Ioi_neg_dMinus (s r σ K τ : ℝ) :
    (gaussianReal 0 1).real (Ioi (-dMinus s r σ K τ)) =
      cdf (gaussianReal 0 1) (dMinus s r σ K τ) := by
  simp [TauCeti.Probability.measureReal_Ioi_gaussianReal_eq_cdf _ one_ne_zero]

/-- The stock leg of the call: on the in-the-money event `{-d₋ < Z}` the terminal spot integrates
to `s e^{rτ} Φ(d₊)`. -/
private theorem setIntegral_Ioi_neg_dMinus_terminalSpot (s r σ K : ℝ) (hτ : 0 ≤ τ) :
    ∫ z in Ioi (-dMinus s r σ K τ), terminalSpot s r σ τ z ∂gaussianReal 0 1 =
      s * exp (r * τ) * cdf (gaussianReal 0 1) (dPlus s r σ K τ) := by
  rw [setIntegral_terminalSpot s r σ hτ,
    TauCeti.Probability.measureReal_Ioi_gaussianReal_eq_cdf _ one_ne_zero, dMinus_def]
  congr 2
  simp

/-- **The Black–Scholes call formula.** The discounted risk-neutral expectation of the call payoff
`(S_τ - K)⁺` is `s Φ(d₊) - K e^{-rτ} Φ(d₋)`. -/
theorem riskNeutralPrice_call (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    riskNeutralPrice (fun x => (x - K)⁺) s r σ τ = callPrice s r σ K τ := by
  -- The payoff is `S_τ - K` on the in-the-money event `{-d₋ < Z}` and zero off it.
  have hpay : (fun z => (terminalSpot s r σ τ z - K)⁺) =
      (Ioi (-dMinus s r σ K τ)).indicator (fun z => terminalSpot s r σ τ z - K) := by
    ext z
    by_cases hz : -dMinus s r σ K τ < z
    · rw [indicator_of_mem hz, posPart_eq_self.2]
      exact (sub_pos.2 ((lt_terminalSpot_iff hs hσ hK hτ z).2 hz)).le
    · rw [indicator_of_notMem hz, posPart_eq_zero.2]
      exact sub_nonpos.2 (not_lt.1 (mt (lt_terminalSpot_iff hs hσ hK hτ z).1 hz))
  rw [riskNeutralPrice_def, hpay, integral_indicator measurableSet_Ioi,
    integral_sub (integrable_terminalSpot s r σ τ).integrableOn (integrable_const K),
    setIntegral_Ioi_neg_dMinus_terminalSpot s r σ K hτ.le, setIntegral_const, smul_eq_mul,
    measureReal_Ioi_neg_dMinus, callPrice_def]
  -- The discount factor cancels the forward growth of the stock leg.
  have hexp : exp (-r * τ) * exp (r * τ) = 1 := by rw [← exp_add]; simp
  linear_combination (s * cdf (gaussianReal 0 1) (dPlus s r σ K τ)) * hexp

/-- **The Black–Scholes put formula.** The discounted risk-neutral expectation of the put payoff
`(K - S_τ)⁺` is `K e^{-rτ} Φ(-d₋) - s Φ(-d₊)`. -/
theorem riskNeutralPrice_put (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    riskNeutralPrice (fun x => (K - x)⁺) s r σ τ = putPrice s r σ K τ := by
  -- `(K - x)⁺ = (x - K)⁺ - (x - K)`, so put–call parity reduces the put to the call.
  have hpay : (fun z => (K - terminalSpot s r σ τ z)⁺) =
      fun z => (terminalSpot s r σ τ z - K)⁺ - (terminalSpot s r σ τ z - K) := by
    ext z
    rw [← neg_sub, posPart_neg]
    linear_combination -1 * posPart_sub_negPart (terminalSpot s r σ τ z - K)
  have hcall := riskNeutralPrice_call (r := r) hs hσ hK hτ
  have hid := riskNeutralPrice_id s r σ hτ.le
  have hint := integrable_terminalSpot s r σ τ
  rw [riskNeutralPrice_def] at hcall ⊢
  simp only [riskNeutralPrice_def, id_eq] at hid
  have hsub : Integrable (fun z => terminalSpot s r σ τ z - K) (gaussianReal 0 1) :=
    hint.sub (integrable_const K)
  have hpos : Integrable (fun z => (terminalSpot s r σ τ z - K)⁺) (gaussianReal 0 1) := by
    simpa only [posPart_def] using hsub.pos_part
  -- Split the integral by linearity, then combine the call price, the stock price and parity.
  rw [hpay, integral_sub hpos hsub, integral_sub hint (integrable_const K), integral_const,
    probReal_univ, one_smul]
  linear_combination hcall - hid + callPrice_sub_putPrice s r σ K τ


/-! ### No-arbitrage bounds -/

/-- The Black–Scholes call price is nonnegative. -/
theorem callPrice_nonneg (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    0 ≤ callPrice s r σ K τ := by
  rw [← riskNeutralPrice_call hs hσ hK hτ]
  exact riskNeutralPrice_nonneg (fun x => posPart_nonneg _) s r σ τ

/-- The Black–Scholes put price is nonnegative. -/
theorem putPrice_nonneg (hs : 0 < s) (hσ : 0 < σ) (hK : 0 < K) (hτ : 0 < τ) :
    0 ≤ putPrice s r σ K τ := by
  rw [← riskNeutralPrice_put hs hσ hK hτ]
  exact riskNeutralPrice_nonneg (fun x => posPart_nonneg _) s r σ τ

/-- The Black–Scholes call price is at most the spot. -/
theorem callPrice_le (hs : 0 ≤ s) (hK : 0 ≤ K) : callPrice s r σ K τ ≤ s := by
  rw [callPrice_def]
  have h₁ := mul_le_mul_of_nonneg_left (cdf_le_one (gaussianReal 0 1) (dPlus s r σ K τ)) hs
  have h₂ := mul_nonneg (mul_nonneg hK (exp_pos (-r * τ)).le)
    (cdf_nonneg (gaussianReal 0 1) (dMinus s r σ K τ))
  linarith

/-- The Black–Scholes put price is at most its strike leg `K e^{-rτ} Φ(-d₋)`. -/
theorem putPrice_le_mul_cdf (hs : 0 ≤ s) :
    putPrice s r σ K τ ≤ K * exp (-r * τ) * cdf (gaussianReal 0 1) (-dMinus s r σ K τ) := by
  rw [putPrice_def]
  linarith [mul_nonneg hs (cdf_nonneg (gaussianReal 0 1) (-dPlus s r σ K τ))]

/-- The Black–Scholes put price is at most the discounted strike `K e^{-rτ}`. -/
theorem putPrice_le (hs : 0 ≤ s) (hK : 0 ≤ K) : putPrice s r σ K τ ≤ K * exp (-r * τ) :=
  (putPrice_le_mul_cdf hs).trans (mul_le_of_le_one_right (mul_nonneg hK (exp_pos _).le)
    (cdf_le_one _ _))

end TauCeti.BlackScholes
