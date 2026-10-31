/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Girsanov
public import TauCeti.Probability.Finance.BlackScholes.Extension
public import TauCeti.Probability.Finance.BlackScholes.GeometricBrownianMotion
public import TauCeti.Probability.Independence.CondExp

/-!
# Black–Scholes prices as conditional risk-neutral expectations

In a market with interest rate `r`, the price at time `u` of a claim paying `H` at a later time
`t` is the discounted conditional expectation `e^{-r (t - u)} E_Q[H | ℱ_u]` under a risk-neutral
measure `Q`. This file evaluates it for a claim `H = h (S_t)` on the Black–Scholes stock, and
identifies it with `TauCeti.BlackScholes.riskNeutralPrice` at the current spot `S_u` and the
remaining maturity `t - u`:

`e^{-r (t - u)} E_Q[h (S_t) | ℱ_u] = riskNeutralPrice h S_u r σ (t - u)`  almost surely.

For the call and put payoffs these are the extended Black–Scholes prices
`TauCeti.BlackScholes.callValue` and `TauCeti.BlackScholes.putValue`, so the closed-form price
at the current spot is the value process of the option at every time `u ≤ t`, and equals the
payoff at `u = t`.

The key input is the **Markov property** of geometric Brownian motion
`S_t = s exp ((μ - σ² / 2) t + σ W_t)`: for `u ≤ t`,
`S_t = S_u exp ((μ - σ² / 2) (t - u) + σ (W_t - W_u))`, where `S_u` is known at time `u` and the
increment `W_t - W_u ∼ N(0, t - u)` is independent of `ℱ_u`. Conditioning therefore freezes `S_u`
and integrates the increment out
(`TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep`).

The results are stated twice. First for a stock with drift `r` under a measure for which `W` is a
Brownian motion relative to `ℱ`. Then for the Black–Scholes market itself: the stock has drift
`μ` under the physical measure `P`, the market price of risk is `κ = (μ - r) / σ`, and the
risk-neutral measure is `Q = P.tilted (-κ W_T ·)`, with density `exp (-κ W_T - κ² T / 2)`. By
Girsanov's theorem `W_t + κ t` is a Brownian motion under `Q` up to the horizon `T`, and the
stock is the geometric Brownian motion with drift `r` driven by it. The conditional expectations
are under `Q`, and the identities hold `Q`-almost surely (as `Q` and `P` are equivalent, this is
the same as `P`-almost surely).

## Main declarations

All declarations are in the namespace `TauCeti.Probability.IsFilteredPreBrownianReal`.

* `condExp_comp_geometricBrownianMotion`: the Markov property of geometric Brownian motion.
* `riskNeutralPrice_eq_condExp_geometricBrownianMotion`,
  `callValue_eq_condExp_geometricBrownianMotion`, `putValue_eq_condExp_geometricBrownianMotion`:
  conditional prices for a stock with drift `r`.
* `riskNeutralPrice_eq_condExp_tilted_geometricBrownianMotion`,
  `callValue_eq_condExp_tilted_geometricBrownianMotion`,
  `putValue_eq_condExp_tilted_geometricBrownianMotion`: conditional prices under the risk-neutral
  measure of the Black–Scholes market.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  Lemma 2.3.4 (the Independence Lemma) and §5.2.4–§5.2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter TauCeti.BlackScholes
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s σ K : ℝ} {u t T : ℝ≥0} {h : ℝ → ℝ}

/-! ### The Markov property of geometric Brownian motion -/

/-- **Markov property of geometric Brownian motion.** For `u ≤ t` and a measurable `h` with
`h (S_t)` integrable, the conditional expectation of `h (S_t)` given `ℱ_u` is the Gaussian
expectation of `h` at the terminal spot started from `S_u` with remaining maturity `t - u`. -/
theorem condExp_comp_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (s μ σ : ℝ) (hh : Measurable h) (hut : u ≤ t)
    (hint : Integrable (fun ω ↦ h (geometricBrownianMotion s μ σ W t ω)) P) :
    P[fun ω ↦ h (geometricBrownianMotion s μ σ W t ω) | ℱ u] =ᵐ[P] fun ω ↦
      ∫ z, h (terminalSpot (geometricBrownianMotion s μ σ W u ω) μ σ (t - u) z)
        ∂gaussianReal 0 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hτ : ((t - u : ℝ≥0) : ℝ) = t - u := NNReal.coe_sub hut
  -- `h (S_t) = F (S_u, W_t - W_u)`.
  set F : ℝ × ℝ → ℝ := fun p ↦ h (p.1 * exp ((μ - σ ^ 2 / 2) * (t - u) + σ * p.2)) with hF_def
  have hF : StronglyMeasurable F := (hh.comp (by fun_prop)).stronglyMeasurable
  have hS : (fun ω ↦ h (geometricBrownianMotion s μ σ W t ω)) =
      fun ω ↦ F (geometricBrownianMotion s μ σ W u ω, (W t - W u) ω) := by
    ext ω
    rw [geometricBrownianMotion_eq_mul s μ σ W u t ω, hF_def, Pi.sub_apply]
  -- The increment `W_t - W_u ∼ N(0, t - u)` is the image of `N(0, 1)` under `z ↦ √(t - u) z`.
  have hlaw : P.map (W t - W u) = (gaussianReal 0 1).map (√((t - u : ℝ≥0) : ℝ) * ·) := by
    have hinc : HasLaw (W t - W u) (gaussianReal 0 (t - u)) P := by
      convert (hW.shift u).hasLaw_eval (t - u) using 1
      ext ω
      simp [add_tsub_cancel_of_le hut]
    rw [hinc.map_eq, gaussianReal_map_const_mul, mul_zero, mul_one]
    congr
    ext
    simp
  have hY : Measurable (W t - W u) :=
    ((hW.adapted t).mono (ℱ.le t) le_rfl).sub ((hW.adapted u).mono (ℱ.le u) le_rfl)
  rw [hS]
  refine (condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le u)
    (hW.adapted.stronglyAdapted_geometricBrownianMotion s μ σ u).measurable hY
    (hW.indep_sub hut) hF (hS ▸ hint)).trans (Eventually.of_forall fun ω ↦ ?_)
  have hFω : AEStronglyMeasurable (fun y ↦ F (geometricBrownianMotion s μ σ W u ω, y))
      ((gaussianReal 0 1).map (√((t - u : ℝ≥0) : ℝ) * ·)) :=
    (hF.comp_measurable measurable_prodMk_left).aestronglyMeasurable
  dsimp only
  rw [hlaw, integral_map (by fun_prop) hFω]
  simp only [hF_def, terminalSpot_def, hτ]
  ring_nf

/-! ### Conditional prices for a stock with drift `r` -/

/-- **Conditional risk-neutral price.** If `W` is a Brownian motion relative to `ℱ` and the stock
`S` is the geometric Brownian motion with drift `r`, then for `u ≤ t` the discounted conditional
expectation `e^{-r (t - u)} E[h (S_t) | ℱ_u]` is the risk-neutral price of `h` at the spot `S_u`
and remaining maturity `t - u`. -/
theorem riskNeutralPrice_eq_condExp_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (s r σ : ℝ) (hh : Measurable h) (hut : u ≤ t)
    (hint : Integrable (fun ω ↦ h (geometricBrownianMotion s r σ W t ω)) P) :
    (fun ω ↦ riskNeutralPrice h (geometricBrownianMotion s r σ W u ω) r σ (t - u)) =ᵐ[P]
      fun ω ↦ exp (-r * (t - u)) * P[fun ω ↦ h (geometricBrownianMotion s r σ W t ω) | ℱ u] ω := by
  filter_upwards [hW.condExp_comp_geometricBrownianMotion s r σ hh hut hint] with ω hω
  rw [hω, riskNeutralPrice_def]

/-- **The call value process.** For a stock with drift `r` driven by a Brownian motion relative
to `ℱ`, and `u ≤ t`, the extended Black–Scholes call price at the spot `S_u` and remaining
maturity `t - u` is the discounted conditional expected payoff `e^{-r (t - u)} E[(S_t - K)⁺ | ℱ_u]`.
-/
theorem callValue_eq_condExp_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (hs : 0 < s) (r : ℝ) (hσ : 0 < σ) (hK : 0 < K) (hut : u ≤ t) :
    (fun ω ↦ callValue (geometricBrownianMotion s r σ W u ω) r σ K (t - u)) =ᵐ[P]
      fun ω ↦ exp (-r * (t - u)) *
        P[fun ω ↦ (geometricBrownianMotion s r σ W t ω - K)⁺ | ℱ u] ω := by
  have hint : Integrable (fun ω ↦ (geometricBrownianMotion s r σ W t ω - K)⁺) P := by
    have := (hW.hasLaw_eval 0).isProbabilityMeasure
    have := (hW.integrable_geometricBrownianMotion s r σ t).sub (integrable_const K)
    simpa only [posPart_def, Pi.sub_apply] using this.pos_part
  have hh : Measurable fun x : ℝ ↦ (x - K)⁺ :=
    (by fun_prop : Continuous fun x : ℝ ↦ (x - K)⁺).measurable
  filter_upwards [hW.riskNeutralPrice_eq_condExp_geometricBrownianMotion s r σ hh hut hint]
    with ω hω
  rw [← hω, riskNeutralPrice_call_eq_callValue (geometricBrownianMotion_pos hs r σ W u ω) hσ hK
    (sub_nonneg.2 (NNReal.coe_le_coe.2 hut))]

/-- **The put value process.** For a stock with drift `r` driven by a Brownian motion relative
to `ℱ`, and `u ≤ t`, the extended Black–Scholes put price at the spot `S_u` and remaining
maturity `t - u` is the discounted conditional expected payoff `e^{-r (t - u)} E[(K - S_t)⁺ | ℱ_u]`.
-/
theorem putValue_eq_condExp_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (hs : 0 < s) (r : ℝ) (hσ : 0 < σ) (hK : 0 < K) (hut : u ≤ t) :
    (fun ω ↦ putValue (geometricBrownianMotion s r σ W u ω) r σ K (t - u)) =ᵐ[P]
      fun ω ↦ exp (-r * (t - u)) *
        P[fun ω ↦ (K - geometricBrownianMotion s r σ W t ω)⁺ | ℱ u] ω := by
  have hint : Integrable (fun ω ↦ (K - geometricBrownianMotion s r σ W t ω)⁺) P := by
    have := (hW.hasLaw_eval 0).isProbabilityMeasure
    have := (integrable_const K).sub (hW.integrable_geometricBrownianMotion s r σ t)
    simpa only [posPart_def, Pi.sub_apply] using this.pos_part
  have hh : Measurable fun x : ℝ ↦ (K - x)⁺ :=
    (by fun_prop : Continuous fun x : ℝ ↦ (K - x)⁺).measurable
  filter_upwards [hW.riskNeutralPrice_eq_condExp_geometricBrownianMotion s r σ hh hut hint]
    with ω hω
  rw [← hω, riskNeutralPrice_put_eq_putValue (geometricBrownianMotion_pos hs r σ W u ω) hσ hK
    (sub_nonneg.2 (NNReal.coe_le_coe.2 hut))]

/-! ### Conditional prices under the risk-neutral measure -/

/-- Up to the horizon `T`, the stock with drift `μ` driven by `W` is the stock with drift `r`
driven by the Brownian motion `W_t + κ t` of the risk-neutral measure, `κ = (μ - r) / σ`. -/
private theorem geometricBrownianMotion_eq_riskNeutral (s μ r : ℝ) (hσ : σ ≠ 0) {t : ℝ≥0}
    (htT : t ≤ T) (ω : Ω) :
    geometricBrownianMotion s μ σ W t ω = geometricBrownianMotion s r σ
      (fun t ω ↦ W t ω - -((μ - r) / σ) * (min t T : ℝ≥0)) t ω := by
  have hr : μ + σ * -((μ - r) / σ) = r := by
    field_simp
    ring
  rw [← geometricBrownianMotion_sub_mul_min s μ σ (-((μ - r) / σ)) W htT ω, hr]

/-- **Conditional risk-neutral price in the Black–Scholes market.** Let the stock `S` have drift
`μ` and volatility `σ ≠ 0` under `P`, let `κ = (μ - r) / σ` be the market price of risk and
`Q = P.tilted (-κ W_T ·)` the risk-neutral measure for the horizon `T`. For `u ≤ T` the discounted
conditional expectation `e^{-r (T - u)} E_Q[h (S_T) | ℱ_u]` is the risk-neutral price of `h` at the
spot `S_u` and remaining maturity `T - u`. -/
theorem riskNeutralPrice_eq_condExp_tilted_geometricBrownianMotion
    (hW : IsFilteredPreBrownianReal ℱ W P) (s μ r : ℝ) (hσ : σ ≠ 0) (hh : Measurable h)
    (huT : u ≤ T) (hint : Integrable (fun ω ↦ h (geometricBrownianMotion s μ σ W T ω))
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)) :
    (fun ω ↦ riskNeutralPrice h (geometricBrownianMotion s μ σ W u ω) r σ (T - u)) =ᵐ[
      P.tilted fun ω ↦ -((μ - r) / σ) * W T ω] fun ω ↦ exp (-r * (T - u)) *
        (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)[
          fun ω ↦ h (geometricBrownianMotion s μ σ W T ω) | ℱ u] ω := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ huT,
    geometricBrownianMotion_eq_riskNeutral s μ r hσ (le_refl T)] at hint ⊢
  exact (hW.sub_mul_min_tilted_mul_eval _ T).riskNeutralPrice_eq_condExp_geometricBrownianMotion
    s r σ hh huT hint

/-- **The call value process in the Black–Scholes market.** For a stock with drift `μ` and
volatility `σ > 0` under `P`, and `u ≤ T`, the extended Black–Scholes call price at the spot `S_u`
and remaining maturity `T - u` is the discounted conditional expected payoff
`e^{-r (T - u)} E_Q[(S_T - K)⁺ | ℱ_u]` under the risk-neutral measure
`Q = P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`. -/
theorem callValue_eq_condExp_tilted_geometricBrownianMotion
    (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s) (μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K)
    (huT : u ≤ T) :
    (fun ω ↦ callValue (geometricBrownianMotion s μ σ W u ω) r σ K (T - u)) =ᵐ[
      P.tilted fun ω ↦ -((μ - r) / σ) * W T ω] fun ω ↦ exp (-r * (T - u)) *
        (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)[
          fun ω ↦ (geometricBrownianMotion s μ σ W T ω - K)⁺ | ℱ u] ω := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' huT,
    geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' (le_refl T)]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).callValue_eq_condExp_geometricBrownianMotion
    hs r hσ hK huT

/-- **The put value process in the Black–Scholes market.** For a stock with drift `μ` and
volatility `σ > 0` under `P`, and `u ≤ T`, the extended Black–Scholes put price at the spot `S_u`
and remaining maturity `T - u` is the discounted conditional expected payoff
`e^{-r (T - u)} E_Q[(K - S_T)⁺ | ℱ_u]` under the risk-neutral measure
`Q = P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`. -/
theorem putValue_eq_condExp_tilted_geometricBrownianMotion
    (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 < s) (μ r : ℝ) (hσ : 0 < σ) (hK : 0 < K)
    (huT : u ≤ T) :
    (fun ω ↦ putValue (geometricBrownianMotion s μ σ W u ω) r σ K (T - u)) =ᵐ[
      P.tilted fun ω ↦ -((μ - r) / σ) * W T ω] fun ω ↦ exp (-r * (T - u)) *
        (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)[
          fun ω ↦ (K - geometricBrownianMotion s μ σ W T ω)⁺ | ℱ u] ω := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' huT,
    geometricBrownianMotion_eq_riskNeutral s μ r hσ.ne' (le_refl T)]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).putValue_eq_condExp_geometricBrownianMotion
    hs r hσ hK huT

end TauCeti.Probability.IsFilteredPreBrownianReal
