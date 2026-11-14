/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.GridExponential.Basic
public import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.MeasureTheory.Function.UniformIntegrable

/-!
# Limits of bounded Brownian grid likelihoods

Suppose predictable heights on a sequence of deterministic grids share a bound `K`, and
the elapsed grid lengths share a finite bound `T`. The grid likelihoods are uniformly
integrable. Consequently any limit in probability is square integrable, the likelihoods
converge to it in `L¹`, and its expectation is one. In particular, a finite real limit `L`
of their logarithms gives a strictly positive normalized density `exp L`.

These statements supply the passage to the limit in exponential-density approximations.
They do not construct approximations to a stochastic integral or identify the limiting
logarithm with an integral minus half its energy. Those convergence statements are explicit
inputs; expectation one and integrability of the limiting density are conclusions, not inputs.
The grids need not be nested, their lengths may vary, and zero elapsed time is allowed.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5 (exponential densities and bounded integrands).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {K T : ℝ}

/-- The `L²` norm of a grid likelihood is controlled by its height bound and elapsed time. -/
theorem eLpNorm_two_gridExponential_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {θ : ℕ → Ω → ℝ} (hτ : Monotone τ)
    (hθ : ∀ j, Measurable[ℱ (τ j)] (θ j))
    (hK : ∀ j, ∀ᵐ ω ∂P, |θ j ω| ≤ K) (n : ℕ)
    (hT : (τ n : ℝ) - τ 0 ≤ T) :
    eLpNorm (gridExponential τ θ W n) 2 P ≤
      ENNReal.ofReal (exp (K ^ 2 * T)) ^ (1 / 2 : ℝ) := by
  rw [(hW.memLp_two_gridExponential hτ hθ hK n).eLpNorm_eq_integral_rpow_norm
    two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by positivity : (0 : ℝ) ≤ 1 / 2)]
  simp only [one_div]
  gcongr
  exact (hW.integral_sq_gridExponential_le hτ hθ hK n).trans
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT (sq_nonneg K)))

/-- Common bounds on heights and elapsed time give uniform integrability, independently of
the number and spacing of the dates in each grid. -/
theorem unifIntegrable_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    {ι : Type*} {τ : ι → ℕ → ℝ≥0} {θ : ι → ℕ → Ω → ℝ} {N : ι → ℕ}
    (hτ : ∀ k, Monotone (τ k)) (hθ : ∀ k j, Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) :
    UnifIntegrable (fun k ↦ gridExponential (τ k) (θ k) W (N k)) 1 P := by
  exact unifIntegrable_of_eLpNorm_bound (by norm_num) (by finiteness)
    (fun k ↦ hW.eLpNorm_two_gridExponential_le (hτ k) (hθ k) (hK k) (N k) (hT k))

variable {τ : ℕ → ℕ → ℝ≥0} {θ : ℕ → ℕ → Ω → ℝ} {N : ℕ → ℕ}

/-- A limit in probability of grid likelihoods with common height and time bounds retains
their `L²` bound. -/
theorem eLpNorm_two_le_of_tendstoInMeasure_gridExponential
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, Monotone (τ k)) (hθ : ∀ k j, Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) atTop Z) :
    eLpNorm Z 2 P ≤ ENNReal.ofReal (exp (K ^ 2 * T)) ^ (1 / 2 : ℝ) := by
  exact eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun k ↦
      hW.eLpNorm_two_gridExponential_le (hτ k) (hθ k) (hK k) (N k) (hT k)) hZ
    (fun k ↦ (hW.memLp_two_gridExponential (hτ k) (hθ k) (hK k) (N k)).aestronglyMeasurable)

/-- A limit in probability of grid likelihoods with common height and time bounds is in `L²`.
No measurability or integrability hypothesis on the limit is needed. -/
theorem memLp_two_of_tendstoInMeasure_gridExponential
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, Monotone (τ k)) (hθ : ∀ k j, Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) atTop Z) :
    MemLp Z 2 P := by
  exact (hW.eLpNorm_two_le_of_tendstoInMeasure_gridExponential hτ hθ hK hT hZ).trans_lt
    (by finiteness)

/-- Convergence in probability upgrades to `L¹` convergence under common height and time bounds. -/
theorem tendsto_eLpNorm_gridExponential_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, Monotone (τ k)) (hθ : ∀ k j, Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) atTop Z) :
    Tendsto (fun k ↦ eLpNorm (gridExponential (τ k) (θ k) W (N k) - Z) 1 P)
      atTop (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun k ↦ (hW.memLp_two_gridExponential (hτ k) (hθ k) (hK k) (N k)).aestronglyMeasurable)
    ((hW.memLp_two_of_tendstoInMeasure_gridExponential hτ hθ hK hT hZ).mono_exponent (by norm_num))
    (hW.unifIntegrable_gridExponential hτ hθ hK hT) hZ

/-- The limit density has expectation one: bounded grid likelihoods lose no mass in the limit. -/
theorem integral_eq_one_of_tendstoInMeasure_gridExponential
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, Monotone (τ k)) (hθ : ∀ k j, Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) atTop Z) :
    ∫ ω, Z ω ∂P = 1 := by
  have hi := hW.tendsto_eLpNorm_gridExponential_sub hτ hθ hK hT hZ
  have ht := tendsto_integral_of_L1' Z
    (Eventually.of_forall fun k ↦
      hW.integrable_gridExponential (hτ k) (hθ k) (hK k) (N k)) hi
  have ht' := ht.congr fun k ↦ hW.integral_gridExponential (hτ k) (hθ k) (hK k) (N k)
  exact tendsto_nhds_unique ht' tendsto_const_nhds

/-- A finite limit in probability of the grid log likelihoods exponentiates to a normalized,
strictly positive density. Strict positivity follows pointwise from `Real.exp_pos`. -/
theorem integral_exp_eq_one_of_tendstoInMeasure_log_gridExponential
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, Monotone (τ k)) (hθ : ∀ k j, Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {L : Ω → ℝ}
    (hL : TendstoInMeasure P (fun k ω ↦ log (gridExponential (τ k) (θ k) W (N k) ω)) atTop L) :
    ∫ ω, exp (L ω) ∂P = 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm k := (measurable_log.comp_aemeasurable
    (hW.memLp_two_gridExponential (hτ k) (hθ k) (hK k)
      (N k)).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have h := hL.continuous_comp hm continuous_exp
  simp only [exp_log (gridExponential_pos _ _ _ _ _)] at h
  exact hW.integral_eq_one_of_tendstoInMeasure_gridExponential hτ hθ hK hT h

end TauCeti.Probability.IsFilteredPreBrownianReal
