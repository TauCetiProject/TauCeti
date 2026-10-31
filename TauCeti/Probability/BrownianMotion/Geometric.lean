/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.ExponentialMartingale
public import TauCeti.Probability.Distributions.LogNormal.Basic

/-!
# Geometric Brownian motion

For a Brownian motion `W`, an initial value `s`, a drift `μ` and a volatility `σ`, the
**geometric Brownian motion**

`S_t = s * exp ((μ - σ² / 2) t + σ W_t)`

(`TauCeti.Probability.geometricBrownianMotion s μ σ W`) is the explicit solution of the linear
stochastic differential equation `dS_t = μ S_t dt + σ S_t dW_t` with constant coefficients. It is
the stock price of the Black–Scholes market. This file develops it from its explicit formula; the
statement that it solves the differential equation needs Itô calculus and is not proved here.

The main tool is the factorisation `S_t = s e^{μ t} Z_t` through the exponential martingale
`Z_t = exp (σ W_t - σ² t / 2)`, and more generally, for `s ≥ 0` and every real `q`,

`S_t ^ q = s ^ q * exp ((q μ + q (q - 1) σ² / 2) t) * exp (q σ W_t - q² σ² t / 2)`.

From it we read off the moments of every real order, finite `Lᵖ` norms, the martingale property
of the discounted process `e^{-μ t} S_t` and the conditional moments `E[S_t ^ q | ℱ_u]`. For
`s > 0` the law of `S_t` is log-normal.

## Main declarations

* `TauCeti.Probability.geometricBrownianMotion`: the process `s * exp ((μ - σ² / 2) t + σ W_t)`.
* `TauCeti.Probability.rpow_geometricBrownianMotion`: real powers of `S_t` as multiples of
  exponential martingales.
* `ProbabilityTheory.IsPreBrownianReal.hasLaw_geometricBrownianMotion`: for `s > 0`, `S_t` is
  log-normal with log-mean `log s + (μ - σ² / 2) t` and log-variance `σ² t`.
* `ProbabilityTheory.IsPreBrownianReal.integral_geometricBrownianMotion`: `E[S_t] = s e^{μ t}`.
* `ProbabilityTheory.IsPreBrownianReal.memLp_geometricBrownianMotion`: `S_t ∈ Lᵖ` for `p < ∞`.
* `ProbabilityTheory.IsPreBrownianReal.integral_rpow_geometricBrownianMotion`:
  `E[S_t ^ q] = s ^ q exp ((q μ + q (q - 1) σ² / 2) t)` for `s ≥ 0` and real `q`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.martingale_discounted_geometricBrownianMotion`:
  the discounted process `e^{-μ t} S_t` is a martingale.
* `TauCeti.Probability.IsFilteredPreBrownianReal.condExp_rpow_geometricBrownianMotion`: the
  conditional moments `E[S_t ^ q | ℱ_u] = exp ((q μ + q (q - 1) σ² / 2) (t - u)) S_u ^ q`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §5.6.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §3.4.2 and §4.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {s : ℝ}

/-- The **geometric Brownian motion** `s * exp ((μ - σ² / 2) t + σ W_t)` driven by `W`, with
initial value `s`, drift `μ` and volatility `σ`. -/
def geometricBrownianMotion (s μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  s * exp ((μ - σ ^ 2 / 2) * t + σ * W t ω)

/-- Unfolding lemma for `geometricBrownianMotion`. -/
theorem geometricBrownianMotion_def (s μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    geometricBrownianMotion s μ σ W t ω = s * exp ((μ - σ ^ 2 / 2) * t + σ * W t ω) :=
  (rfl)

/-- A geometric Brownian motion with positive initial value stays positive. -/
theorem geometricBrownianMotion_pos (hs : 0 < s) (μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    0 < geometricBrownianMotion s μ σ W t ω := by
  rw [geometricBrownianMotion_def]
  positivity

/-- From time `u` to time `t` a geometric Brownian motion is multiplied by the exponential of
`(μ - σ² / 2) (t - u) + σ (W_t - W_u)`. -/
theorem geometricBrownianMotion_eq_mul (s μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u t : ℝ≥0) (ω : Ω) :
    geometricBrownianMotion s μ σ W t ω = geometricBrownianMotion s μ σ W u ω *
      exp ((μ - σ ^ 2 / 2) * (t - u) + σ * (W t ω - W u ω)) := by
  rw [geometricBrownianMotion_def, geometricBrownianMotion_def, mul_assoc, ← exp_add]
  ring_nf

/-- A geometric Brownian motion is its initial value, grown at the rate `μ`, times the exponential
martingale `exp (σ W_t - σ² t / 2)`. -/
theorem geometricBrownianMotion_eq_mul_exponentialMartingale (s μ σ : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    geometricBrownianMotion s μ σ W t ω = s * exp (μ * t) * exponentialMartingale σ W t ω := by
  rw [geometricBrownianMotion_def, exponentialMartingale_def, mul_assoc, ← exp_add]
  ring_nf

/-- For a nonnegative initial value, a real power `S_t ^ q` of a geometric Brownian motion is
`s ^ q exp ((q μ + q (q - 1) σ² / 2) t)` times the exponential martingale with parameter `q σ`. -/
theorem rpow_geometricBrownianMotion (hs : 0 ≤ s) (μ σ q : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (ω : Ω) :
    geometricBrownianMotion s μ σ W t ω ^ q = s ^ q * exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * t) *
      exponentialMartingale (q * σ) W t ω := by
  rw [geometricBrownianMotion_eq_mul_exponentialMartingale,
    mul_rpow (by positivity) (exponentialMartingale_pos σ W t ω).le, mul_rpow hs (exp_pos _).le,
    ← exp_mul, rpow_exponentialMartingale, mul_assoc, ← mul_assoc (exp _), ← exp_add, mul_assoc]
  ring_nf

end TauCeti.Probability

namespace MeasureTheory.Adapted

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- A geometric Brownian motion driven by a process adapted to `ℱ` is adapted to `ℱ`. -/
theorem stronglyAdapted_geometricBrownianMotion (hW : Adapted ℱ W) (s μ σ : ℝ) :
    StronglyAdapted ℱ (geometricBrownianMotion s μ σ W) := fun t ↦ by
  simp_rw [funext (geometricBrownianMotion_def s μ σ W t)]
  exact ((measurable_exp.comp (((hW t).const_mul σ).const_add _)).const_mul s).stronglyMeasurable

end MeasureTheory.Adapted

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {s : ℝ}

/-- A geometric Brownian motion starts almost surely at its initial value. -/
theorem ae_geometricBrownianMotion_zero (hB : IsPreBrownianReal B P) (s μ σ : ℝ) :
    ∀ᵐ ω ∂P, geometricBrownianMotion s μ σ B 0 ω = s := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  simp [geometricBrownianMotion_def, hω]

/-- **The law of geometric Brownian motion.** For `s > 0`, `S_t` is log-normal with log-mean
`log s + (μ - σ² / 2) t` and log-variance `σ² t`. -/
theorem hasLaw_geometricBrownianMotion (hB : IsPreBrownianReal B P) (hs : 0 < s) (μ σ : ℝ)
    (t : ℝ≥0) :
    HasLaw (geometricBrownianMotion s μ σ B t)
      (logNormalMeasure (log s + (μ - σ ^ 2 / 2) * t) (.mk (σ ^ 2) (sq_nonneg σ) * t)) P := by
  set m := log s + (μ - σ ^ 2 / 2) * t
  -- `S_t` is the image of `W_t ∼ N(0, t)` under `x ↦ exp (σ x + m)`.
  have hS : geometricBrownianMotion s μ σ B t = (exp ∘ (· + m) ∘ (σ * ·)) ∘ B t := by
    ext ω
    simp only [geometricBrownianMotion_def, Function.comp_apply, m, exp_add, exp_log hs]
    ring
  have hG : HasLaw (exp ∘ (· + m) ∘ (σ * ·)) (logNormalMeasure m (.mk (σ ^ 2) (sq_nonneg σ) * t))
      (gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const, logNormalMeasure_map_exp, mul_zero, zero_add]
  rw [hS]
  exact hG.comp (hB.hasLaw_eval t)

/-- A geometric Brownian motion has finite moments of every finite order. -/
theorem memLp_geometricBrownianMotion (hB : IsPreBrownianReal B P) (s μ σ : ℝ) (t : ℝ≥0)
    {p : ℝ≥0∞} (hp : p ≠ ∞) : MemLp (geometricBrownianMotion s μ σ B t) p P := by
  simp_rw [funext (geometricBrownianMotion_eq_mul_exponentialMartingale s μ σ B t)]
  exact (hB.memLp_exponentialMartingale σ t hp).const_mul _

/-- A geometric Brownian motion is integrable at every time. -/
theorem integrable_geometricBrownianMotion (hB : IsPreBrownianReal B P) (s μ σ : ℝ) (t : ℝ≥0) :
    Integrable (geometricBrownianMotion s μ σ B t) P :=
  memLp_one_iff_integrable.1 (hB.memLp_geometricBrownianMotion s μ σ t ENNReal.one_ne_top)

/-- **The mean of geometric Brownian motion.** `E[S_t] = s e^{μ t}`. -/
theorem integral_geometricBrownianMotion (hB : IsPreBrownianReal B P) (s μ σ : ℝ) (t : ℝ≥0) :
    ∫ ω, geometricBrownianMotion s μ σ B t ω ∂P = s * exp (μ * t) := by
  simp_rw [geometricBrownianMotion_eq_mul_exponentialMartingale, integral_const_mul,
    hB.integral_exponentialMartingale, mul_one]

/-- Every real power of a geometric Brownian motion with nonnegative initial value is
integrable. -/
theorem integrable_rpow_geometricBrownianMotion (hB : IsPreBrownianReal B P) (hs : 0 ≤ s)
    (μ σ q : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ geometricBrownianMotion s μ σ B t ω ^ q) P := by
  simp_rw [rpow_geometricBrownianMotion hs]
  exact (hB.integrable_exponentialMartingale _ t).const_mul _

/-- **The moments of geometric Brownian motion.** For `s ≥ 0` and every real `q`,
`E[S_t ^ q] = s ^ q exp ((q μ + q (q - 1) σ² / 2) t)`. -/
theorem integral_rpow_geometricBrownianMotion (hB : IsPreBrownianReal B P) (hs : 0 ≤ s)
    (μ σ q : ℝ) (t : ℝ≥0) :
    ∫ ω, geometricBrownianMotion s μ σ B t ω ^ q ∂P =
      s ^ q * exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * t) := by
  simp_rw [rpow_geometricBrownianMotion hs, integral_const_mul,
    hB.integral_exponentialMartingale, mul_one]

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s : ℝ}

/-- **The discounted geometric Brownian motion is a martingale.** For a Brownian motion relative
to `ℱ`, the process `e^{-μ t} S_t` is a martingale relative to `ℱ`. -/
theorem martingale_discounted_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (s μ σ : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦ exp (-(μ * t)) * geometricBrownianMotion s μ σ W t ω) ℱ P := by
  have h : (fun (t : ℝ≥0) ω ↦ exp (-(μ * t)) * geometricBrownianMotion s μ σ W t ω) =
      s • exponentialMartingale σ W := by
    ext t ω
    rw [geometricBrownianMotion_eq_mul_exponentialMartingale, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, exp_neg]
    field_simp
  rw [h]
  exact (hW.martingale_exponentialMartingale σ).smul s

/-- **The conditional moments of geometric Brownian motion.** For `s ≥ 0`, `u ≤ t` and every real
`q`, `E[S_t ^ q | ℱ_u] = exp ((q μ + q (q - 1) σ² / 2) (t - u)) S_u ^ q`. -/
theorem condExp_rpow_geometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P) (hs : 0 ≤ s)
    (μ σ q : ℝ) {u t : ℝ≥0} (hut : u ≤ t) :
    P[fun ω ↦ geometricBrownianMotion s μ σ W t ω ^ q | ℱ u] =ᵐ[P]
      fun ω ↦ exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * (t - u)) *
        geometricBrownianMotion s μ σ W u ω ^ q := by
  have h : (fun ω ↦ geometricBrownianMotion s μ σ W t ω ^ q) =
      (s ^ q * exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * t)) •
        exponentialMartingale (q * σ) W t := by
    ext ω
    rw [rpow_geometricBrownianMotion hs, Pi.smul_apply, smul_eq_mul]
  rw [h]
  filter_upwards [condExp_smul (𝕜 := ℝ) _ (exponentialMartingale (q * σ) W t) (ℱ u),
    (hW.martingale_exponentialMartingale (q * σ)).condExp_ae_eq hut] with ω h₁ h₂
  rw [h₁, Pi.smul_apply, h₂, smul_eq_mul, rpow_geometricBrownianMotion hs]
  generalize q * μ + q * (q - 1) * σ ^ 2 / 2 = c
  rw [mul_sub, exp_sub]
  field_simp

end TauCeti.Probability.IsFilteredPreBrownianReal
