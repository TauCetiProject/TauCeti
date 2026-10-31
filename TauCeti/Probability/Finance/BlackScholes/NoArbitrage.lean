/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Arbitrage
public import TauCeti.Probability.Finance.BlackScholes.ConditionalPrice

/-!
# No arbitrage with simple strategies in the Black–Scholes market

The Black–Scholes market on the horizon `[0, T]` has a stock
`S_t = s exp ((μ - σ² / 2) t + σ W_t)` driven by a Brownian motion `W` relative to a filtration
`ℱ` under the physical measure `P`, and a bond `β_t = e^{r t}`. With the market price of risk
`κ = (μ - r) / σ`, the risk-neutral measure is `Q = P.tilted (-κ W_T ·)`, whose density with
respect to `P` is `exp (-κ W_T - κ² T / 2)`. It has the same null sets as `P`.

Up to the horizon the discounted stock `S_t / β_t` is a `Q`-martingale
(`condExp_discounted_geometricBrownianMotion_tilted`): by Girsanov's theorem the stock is the
geometric Brownian motion with drift `r` driven by the `Q`-Brownian motion `W_t + κ t`. The
general results of `TauCeti.Probability.Finance.Arbitrage` then apply to every self-financing
simple strategy trading at dates up to `T` whose stock holdings `a j` are chosen at the start of
their intervals and whose trades in the discounted stock have `Q`-integrable gains:

* no such strategy is an arbitrage under `P` (`not_isArbitrage_geometricBrownianMotion`);
* its discounted wealth `V_{τ k} / β_{τ k}` at each trading date `τ k` is
  `E_Q[V / β_{τ_last} | ℱ (τ k)]`, where `V` is its terminal wealth at the last trading date
  `τ_last` (`condExp_discounted_wealth_geometricBrownianMotion`), so the terminal wealth
  determines the wealth at every trading date.

General self-financing strategies, whose gains are stochastic integrals, are not treated here.

All declarations are in the namespace `TauCeti.Probability.IsFilteredPreBrownianReal`.

## References

* J. M. Harrison, S. R. Pliska, *Martingales and stochastic integrals in the theory of continuous
  trading*, Stochastic Process. Appl. 11 (1981), 215–260, §2–§3.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.4 and §5.4.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real TauCeti.Finance
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {σ : ℝ} {T : ℝ≥0}

/-- Up to the horizon `T`, the stock is integrable under the risk-neutral measure
`P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`. -/
theorem integrable_geometricBrownianMotion_tilted (hW : IsFilteredPreBrownianReal ℱ W P)
    (s μ r : ℝ) (hσ : σ ≠ 0) {t : ℝ≥0} (htT : t ≤ T) :
    Integrable (geometricBrownianMotion s μ σ W t) (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω) := by
  simp_rw [funext (geometricBrownianMotion_eq_riskNeutral s μ r hσ htT (W := W))]
  exact (hW.sub_mul_min_tilted_mul_eval _ T).integrable_geometricBrownianMotion s r σ t

/-- **The discounted stock is a risk-neutral martingale.** For `u ≤ t ≤ T`, the conditional
expectation given `ℱ u` of the discounted stock `S_t / e^{r t}` under the risk-neutral measure
`P.tilted (-κ W_T ·)`, `κ = (μ - r) / σ`, is the discounted stock `S_u / e^{r u}`. -/
theorem condExp_discounted_geometricBrownianMotion_tilted (hW : IsFilteredPreBrownianReal ℱ W P)
    (s μ r : ℝ) (hσ : σ ≠ 0) {u t : ℝ≥0} (hut : u ≤ t) (htT : t ≤ T) :
    (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)[
        fun ω ↦ geometricBrownianMotion s μ σ W t ω / exp (r * t) | ℱ u] =ᵐ[
      P.tilted fun ω ↦ -((μ - r) / σ) * W T ω]
      fun ω ↦ geometricBrownianMotion s μ σ W u ω / exp (r * u) := by
  simp_rw [geometricBrownianMotion_eq_riskNeutral s μ r hσ htT,
    geometricBrownianMotion_eq_riskNeutral s μ r hσ (hut.trans htT), div_eq_inv_mul, ← exp_neg]
  exact ((hW.sub_mul_min_tilted_mul_eval _ T).martingale_discounted_geometricBrownianMotion
    s r σ).condExp_ae_eq hut

/-- **No arbitrage with simple strategies in the Black–Scholes market.** Let the stock have drift
`μ` and volatility `σ ≠ 0`, let the bond be `e^{r t}`, and let `Q = P.tilted (-κ W_T ·)`,
`κ = (μ - r) / σ`, be the risk-neutral measure for the horizon `T`. No self-financing simple
strategy trading at dates `τ 0 ≤ ⋯ ≤ τ (n + 1) ≤ T`, whose stock holdings `a j` are chosen at
`τ j` and whose trades in the discounted stock have `Q`-integrable gains, is an arbitrage under
`P`. -/
theorem not_isArbitrage_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (s μ r : ℝ) (hσ : σ ≠ 0) {τ : ℕ → ℝ≥0} {n : ℕ} {a b : ℕ → Ω → ℝ}
    (h : IsSelfFinancing τ (n + 1) a b (geometricBrownianMotion s μ σ W) fun t _ ↦ exp (r * t))
    (hτ : MonotoneOn τ (Set.Iic (n + 1))) (hτT : τ (n + 1) ≤ T)
    (ha : ∀ j < n + 1, StronglyMeasurable[ℱ (τ j)] (a j))
    (hint : ∀ j < n + 1, Integrable (fun ω ↦ a j ω *
      (geometricBrownianMotion s μ σ W (τ (j + 1)) ω / exp (r * τ (j + 1)) -
        geometricBrownianMotion s μ σ W (τ j) ω / exp (r * τ j)))
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)) :
    ¬ IsArbitrage P
      (fun ω ↦ a 0 ω * geometricBrownianMotion s μ σ W (τ 0) ω + b 0 ω * exp (r * τ 0))
      (fun ω ↦ a n ω * geometricBrownianMotion s μ σ W (τ (n + 1)) ω +
        b n ω * exp (r * τ (n + 1))) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hexp := hW.integrable_exp_mul_eval (-((μ - r) / σ)) T
  have := isProbabilityMeasure_tilted hexp
  have hτT' : ∀ j ≤ n + 1, τ j ≤ T := fun j hj ↦ (hτ hj Set.self_mem_Iic hj).trans hτT
  exact h.not_isArbitrage (ℱ := ℱ) (absolutelyContinuous_tilted hexp)
    (tilted_absolutelyContinuous _ _) hτ (fun _ _ _ ↦ exp_pos _)
    (fun j _ ↦ (hW.adapted.stronglyAdapted_geometricBrownianMotion s μ σ (τ j)).div
      stronglyMeasurable_const)
    (fun j hj ↦ (hW.integrable_geometricBrownianMotion_tilted s μ r hσ (hτT' j hj)).div_const _)
    (fun j hj ↦ hW.condExp_discounted_geometricBrownianMotion_tilted s μ r hσ
      (hτ (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hj) (Nat.le_succ j)) (hτT' (j + 1) hj))
    ha hint

/-- **The wealth of a simple strategy in the Black–Scholes market.** Under the hypotheses of
`TauCeti.Probability.IsFilteredPreBrownianReal.not_isArbitrage_geometricBrownianMotion`, if moreover
the discounted initial cost is integrable under `Q` and known at `τ 0`, then for every `k ≤ n` the
discounted cost of the portfolio formed at `τ k` is the risk-neutral conditional expectation given
`ℱ (τ k)` of the discounted terminal wealth. -/
theorem condExp_discounted_wealth_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (s μ r : ℝ) (hσ : σ ≠ 0) {τ : ℕ → ℝ≥0} {n k : ℕ} {a b : ℕ → Ω → ℝ}
    (h : IsSelfFinancing τ (n + 1) a b (geometricBrownianMotion s μ σ W) fun t _ ↦ exp (r * t))
    (hτ : MonotoneOn τ (Set.Iic (n + 1))) (hτT : τ (n + 1) ≤ T)
    (hvm : StronglyMeasurable[ℱ (τ 0)] fun ω ↦
      (a 0 ω * geometricBrownianMotion s μ σ W (τ 0) ω + b 0 ω * exp (r * τ 0)) / exp (r * τ 0))
    (hvi : Integrable (fun ω ↦
      (a 0 ω * geometricBrownianMotion s μ σ W (τ 0) ω + b 0 ω * exp (r * τ 0)) / exp (r * τ 0))
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω))
    (ha : ∀ j < n + 1, StronglyMeasurable[ℱ (τ j)] (a j))
    (hint : ∀ j < n + 1, Integrable (fun ω ↦ a j ω *
      (geometricBrownianMotion s μ σ W (τ (j + 1)) ω / exp (r * τ (j + 1)) -
        geometricBrownianMotion s μ σ W (τ j) ω / exp (r * τ j)))
      (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)) (hk : k ≤ n) :
    (P.tilted fun ω ↦ -((μ - r) / σ) * W T ω)[fun ω ↦
        (a n ω * geometricBrownianMotion s μ σ W (τ (n + 1)) ω + b n ω * exp (r * τ (n + 1))) /
          exp (r * τ (n + 1)) | ℱ (τ k)] =ᵐ[P.tilted fun ω ↦ -((μ - r) / σ) * W T ω]
      fun ω ↦ (a k ω * geometricBrownianMotion s μ σ W (τ k) ω + b k ω * exp (r * τ k)) /
        exp (r * τ k) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have := isProbabilityMeasure_tilted (hW.integrable_exp_mul_eval (-((μ - r) / σ)) T)
  have hτT' : ∀ j ≤ n + 1, τ j ≤ T := fun j hj ↦ (hτ hj Set.self_mem_Iic hj).trans hτT
  exact h.condExp_discounted_wealth hτ (fun _ _ _ ↦ (exp_pos _).ne') hvm hvi
    (fun j _ ↦ (hW.adapted.stronglyAdapted_geometricBrownianMotion s μ σ (τ j)).div
      stronglyMeasurable_const)
    (fun j hj ↦ (hW.integrable_geometricBrownianMotion_tilted s μ r hσ (hτT' j hj)).div_const _)
    (fun j hj ↦ hW.condExp_discounted_geometricBrownianMotion_tilted s μ r hσ
      (hτ (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hj) (Nat.le_succ j)) (hτT' (j + 1) hj))
    ha hint hk

end TauCeti.Probability.IsFilteredPreBrownianReal
