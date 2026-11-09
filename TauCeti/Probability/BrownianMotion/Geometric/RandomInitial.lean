/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Geometric.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Geometric Brownian motion with a random initial value

For an initial variable `ξ` known at time zero, the explicit process
`S_t = ξ exp ((μ - σ² / 2)t + σ W_t)` has absolute moments

`E[|S_t|^q] = E[|ξ|^q] exp ((q μ + q(q-1)σ²/2)t)`.

Integrability requires only finiteness of the initial moment being estimated.
Independence from the initial sigma algebra, not a higher initial moment and
Hölder's inequality, gives integrability of the product. The unconditional integral
identity needs no moment hypothesis: nonintegrable functions have Bochner integral
zero. Signed and zero initial values and zero volatility are allowed, as are real
orders, with Mathlib's convention for real powers at zero.

The exponentially normalized absolute powers are true martingales. Consequently
the same growth factor gives conditional absolute moments between any two dates.
These statements concern the explicit exponential process; they do not assert
that it solves a stochastic differential equation.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer,
  1991, §5.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- Function-level factorization used in random-initial absolute-moment proofs. -/
private theorem abs_rpow_geometricBrownianMotion_random_initial_eq_mul {Ω : Type*}
    (ξ : Ω → ℝ) (μ σ q : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    (fun ω ↦ |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q) =
      fun ω ↦ (|ξ ω| ^ q * exponentialMartingale (q * σ) W t ω) *
        exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * t) := by
  ext ω
  rw [abs_rpow_geometricBrownianMotion]
  ring

namespace IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ξ : Ω → ℝ}

/-- Initial absolute powers are independent of Brownian exponential martingales.
This is the factorization used for random-initial-value moments. -/
private theorem indepFun_initial_abs_rpow_exponentialMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    (q θ : ℝ) (t : ℝ≥0) :
    IndepFun (fun ω ↦ |ξ ω| ^ q) (exponentialMartingale θ W t) P := by
  simp_rw [funext (exponentialMartingale_def θ W t)]
  exact ((hW.indepFun_eval_of_measurable_zero hξ t).symm.comp
    (by fun_prop : Measurable fun x : ℝ ↦ |x| ^ q)
    (by fun_prop : Measurable fun x : ℝ ↦ exp (θ * x - θ ^ 2 * t / 2)))

/-- Integrability of the independent product used in random-initial moments. -/
private theorem integrable_initial_abs_rpow_mul_exponentialMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    {q : ℝ} (hξq : Integrable (fun ω ↦ |ξ ω| ^ q) P) (θ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ |ξ ω| ^ q * exponentialMartingale θ W t ω) P :=
  (hW.indepFun_initial_abs_rpow_exponentialMartingale hξ q θ t).integrable_mul
    hξq (hW.integrable_exponentialMartingale θ t)

/-- A random-initial-value GBM has an integrable absolute power whenever its
initial value has that moment. No higher initial moment is needed. -/
theorem integrable_abs_rpow_geometricBrownianMotion_random_initial
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    {q : ℝ} (hξq : Integrable (fun ω ↦ |ξ ω| ^ q) P) (μ σ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q) P := by
  rw [abs_rpow_geometricBrownianMotion_random_initial_eq_mul]
  exact (hW.integrable_initial_abs_rpow_mul_exponentialMartingale hξ hξq (q * σ) t).mul_const _

/-- Exact absolute moments of geometric Brownian motion with an initial variable
known at time zero. No moment hypothesis is needed, using the Bochner integral's
zero value for nonintegrable functions. -/
theorem integral_abs_rpow_geometricBrownianMotion_random_initial
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    {q : ℝ} (μ σ : ℝ) (t : ℝ≥0) :
    ∫ ω, |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q ∂P =
      (∫ ω, |ξ ω| ^ q ∂P) * exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * t) := by
  have hindep := hW.indepFun_initial_abs_rpow_exponentialMartingale hξ q (q * σ) t
  have hm := ((by fun_prop : Measurable fun x : ℝ ↦ |x| ^ q).comp
    (hξ.mono (ℱ.le 0) le_rfl)).aestronglyMeasurable (μ := P)
  rw [abs_rpow_geometricBrownianMotion_random_initial_eq_mul, integral_mul_const,
    hindep.integral_fun_mul_eq_mul_integral hm
      (hW.integrable_exponentialMartingale (q * σ) t).aestronglyMeasurable,
    hW.integral_exponentialMartingale, mul_one]

/-- Finite `Lᵖ` initial data give finite `Lᵖ` values of the explicit GBM at every
date, including exponents below one. -/
theorem memLp_geometricBrownianMotion_random_initial
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    {p : ℝ≥0∞} (hp : p ≠ ∞) (hξp : MemLp ξ p P) (μ σ : ℝ) (t : ℝ≥0) :
    MemLp (fun ω ↦ geometricBrownianMotion (ξ ω) μ σ W t ω) p P := by
  have hm : Measurable (fun ω ↦ geometricBrownianMotion (ξ ω) μ σ W t ω) := by
    simp_rw [geometricBrownianMotion_def]
    exact (hξ.mono (ℱ.le 0) le_rfl).mul
      (measurable_exp.comp ((((hW.adapted t).mono (ℱ.le t) le_rfl).const_mul σ).const_add _))
  by_cases hp0 : p = 0
  · simpa [hp0] using hm.aestronglyMeasurable
  · apply (integrable_norm_rpow_iff hm.aestronglyMeasurable hp0 hp).mp
    simpa only [Real.norm_eq_abs] using
      hW.integrable_abs_rpow_geometricBrownianMotion_random_initial hξ
        (by simpa only [Real.norm_eq_abs] using hξp.integrable_norm_rpow hp0 hp) μ σ t

/-- Exponentially normalized absolute powers of a random-initial-value GBM are
true martingales when the corresponding initial absolute power is integrable. -/
theorem martingale_exp_neg_mul_abs_rpow_geometricBrownianMotion_random_initial
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    {q : ℝ} (hξq : Integrable (fun ω ↦ |ξ ω| ^ q) P) (μ σ : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦
      exp (-((q * μ + q * (q - 1) * σ ^ 2 / 2) * t)) *
        |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q) ℱ P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hfactor : (fun (t : ℝ≥0) ω ↦
      exp (-((q * μ + q * (q - 1) * σ ^ 2 / 2) * t)) *
        |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q) =
      fun t ω ↦ |ξ ω| ^ q * exponentialMartingale (q * σ) W t ω := by
    ext t ω
    rw [congrFun (abs_rpow_geometricBrownianMotion_random_initial_eq_mul ξ μ σ q W t) ω,
      exp_neg]
    field_simp
  rw [hfactor]
  have hmeas : ∀ t, StronglyMeasurable[ℱ t] (fun ω ↦ |ξ ω| ^ q) := by
    intro t
    exact ((by fun_prop : Measurable fun x : ℝ ↦ |x| ^ q).comp
      (hξ.mono (ℱ.mono (zero_le (a := t))) le_rfl)).stronglyMeasurable
  have hint : ∀ t, Integrable (fun ω ↦ |ξ ω| ^ q * exponentialMartingale (q * σ) W t ω) P :=
    fun t ↦ hW.integrable_initial_abs_rpow_mul_exponentialMartingale hξ hξq (q * σ) t
  refine ⟨fun t ↦ (hmeas t).mul
    ((hW.martingale_exponentialMartingale (q * σ)).stronglyMeasurable t), fun s t hst ↦ ?_⟩
  exact (condExp_mul_of_stronglyMeasurable_left (hmeas s) (hint t)
    (hW.integrable_exponentialMartingale (q * σ) t)).trans
      ((Filter.EventuallyEq.refl _ _).mul
        ((hW.martingale_exponentialMartingale (q * σ)).condExp_ae_eq hst))

/-- Conditional absolute moments have the usual GBM growth factor even with a
random initial value, assuming only its corresponding absolute moment. -/
theorem condExp_abs_rpow_geometricBrownianMotion_random_initial
    (hW : IsFilteredPreBrownianReal ℱ W P) (hξ : Measurable[ℱ 0] ξ)
    {q : ℝ} (hξq : Integrable (fun ω ↦ |ξ ω| ^ q) P) (μ σ : ℝ)
    {u t : ℝ≥0} (hut : u ≤ t) :
    P[fun ω ↦ |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q | ℱ u] =ᵐ[P]
      fun ω ↦ exp ((q * μ + q * (q - 1) * σ ^ 2 / 2) * (t - u)) *
        |geometricBrownianMotion (ξ ω) μ σ W u ω| ^ q := by
  let c := q * μ + q * (q - 1) * σ ^ 2 / 2
  have hmart :=
    (hW.martingale_exp_neg_mul_abs_rpow_geometricBrownianMotion_random_initial
      hξ hξq μ σ).condExp_ae_eq hut
  have hpull := condExp_smul (𝕜 := ℝ) (μ := P) (exp (-(c * t)))
    (fun ω ↦ |geometricBrownianMotion (ξ ω) μ σ W t ω| ^ q) (ℱ u)
  simp only [Pi.smul_def, smul_eq_mul, c] at hpull
  filter_upwards [hmart, hpull] with ω hω hmul
  rw [hmul] at hω
  apply (mul_left_cancel₀ (exp_ne_zero (-(c * t))))
  rw [hω, ← mul_assoc, ← exp_add]
  congr 2
  dsimp [c]
  ring

end IsFilteredPreBrownianReal
end TauCeti.Probability
