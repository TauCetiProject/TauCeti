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

Suppose predictable heights on a family of deterministic grids share a bound `K`, and
the elapsed grid lengths share a finite bound `T`. The grid likelihoods are uniformly
integrable. Consequently any limit in probability along a nontrivial countably generated
filter is square integrable, the likelihoods converge to it in `L¹`, and its expectation is
one. In particular, a finite real limit `L` of their logarithms gives a strictly positive
normalized density `exp L`.

These statements supply the passage to the limit in exponential-density approximations.
They do not construct approximations to a stochastic integral or identify the limiting
logarithm with an integral minus half its energy. Those convergence statements are explicit
inputs; expectation one and integrability of the limiting density are conclusions, not inputs.
The grids need not be nested, their lengths may vary, and zero elapsed time is allowed.
Only dates and heights used by each finite grid need satisfy the grid hypotheses.

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
  {ι : Type*} {τ : ι → ℕ → ℝ≥0} {θ : ι → ℕ → Ω → ℝ} {N : ι → ℕ}

/-- Common bounds on heights and elapsed time give uniform integrability, including a uniform
`L¹` bound, independently of the number and spacing of the dates in each grid. -/
theorem uniformIntegrable_gridExponential (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, j < N k → ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) :
    UniformIntegrable (fun k ↦ gridExponential (τ k) (θ k) W (N k)) 1 P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact uniformIntegrable_of_eLpNorm_le (by norm_num) (by finiteness)
    (fun k ↦ hW.eLpNorm_two_gridExponential_le (hτ k) (hθ k) (hK k) (hT k))

variable {l : Filter ι} [l.IsCountablyGenerated]

/-- A limit in probability of grid likelihoods with common height and time bounds retains
their `L²` bound. -/
theorem eLpNorm_two_le_of_tendstoInMeasure_gridExponential [NeBot l]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, j < N k → ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) l Z) :
    eLpNorm Z 2 P ≤ ENNReal.ofReal (exp (K ^ 2 * T)) ^ (1 / 2 : ℝ) := by
  exact eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall fun k ↦
      hW.eLpNorm_two_gridExponential_le (hτ k) (hθ k) (hK k) (hT k)) hZ
    (fun k ↦ (hW.memLp_two_gridExponential (hτ k) (hθ k) (hK k)).aestronglyMeasurable)

/-- A limit in probability of grid likelihoods with common height and time bounds is in `L²`.
No measurability or integrability hypothesis on the limit is needed. -/
theorem memLp_two_of_tendstoInMeasure_gridExponential [NeBot l]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, j < N k → ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) l Z) :
    MemLp Z 2 P := by
  exact memLp_iff.2 <|
    (hW.eLpNorm_two_le_of_tendstoInMeasure_gridExponential hτ hθ hK hT hZ).trans_lt
      (by finiteness)

/-- Convergence in probability upgrades to `L¹` convergence under common height and time bounds. -/
theorem tendsto_eLpNorm_gridExponential_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, j < N k → ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) l Z) :
    Tendsto (fun k ↦ eLpNorm (gridExponential (τ k) (θ k) W (N k) - Z) 1 P)
      l (𝓝 0) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  rcases eq_or_neBot l with rfl | hl
  · simp
  apply tendsto_of_seq_tendsto
  intro ns hns
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun k ↦ (hW.memLp_two_gridExponential
      (hτ (ns k)) (hθ (ns k)) (hK (ns k))).aestronglyMeasurable)
    ((hW.memLp_two_of_tendstoInMeasure_gridExponential hτ hθ hK hT hZ).mono_exponent (by norm_num))
    ((hW.uniformIntegrable_gridExponential hτ hθ hK hT).comp ns).unifIntegrable
    (hZ.comp hns)

/-- The limit density has expectation one: bounded grid likelihoods lose no mass in the limit. -/
theorem integral_eq_one_of_tendstoInMeasure_gridExponential [NeBot l]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, j < N k → ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {Z : Ω → ℝ}
    (hZ : TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) l Z) :
    ∫ ω, Z ω ∂P = 1 := by
  have hi := hW.tendsto_eLpNorm_gridExponential_sub hτ hθ hK hT hZ
  have ht := tendsto_integral_of_L1' Z
    (Eventually.of_forall fun k ↦
      hW.integrable_gridExponential (hτ k) (hθ k)) hi
  have ht' := ht.congr fun k ↦ hW.integral_gridExponential (hτ k) (hθ k)
  exact tendsto_nhds_unique ht' tendsto_const_nhds

omit [l.IsCountablyGenerated] in
/-- A finite limit in probability of grid log likelihoods exponentiates to a limit of the
likelihoods. No height or elapsed-time bound, or countable generation of the filter, is needed. -/
theorem tendstoInMeasure_gridExponential_of_log (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j)) {L : Ω → ℝ}
    (hL : TendstoInMeasure P (fun k ω ↦ log (gridExponential (τ k) (θ k) W (N k) ω)) l L) :
    TendstoInMeasure P (fun k ↦ gridExponential (τ k) (θ k) W (N k)) l (fun ω ↦ exp (L ω)) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hm k : AEStronglyMeasurable
      (fun ω ↦ log (gridExponential (τ k) (θ k) W (N k) ω)) P :=
    (measurable_log.comp
      ((hW.adapted.measurable_gridExponential (hτ k) (hθ k)).mono
        (ℱ.le _) le_rfl)).aestronglyMeasurable
  have h := hL.continuous_comp continuous_exp
    (Eventually.of_forall fun k ↦ continuous_exp.comp_aestronglyMeasurable (hm k))
  simpa only [exp_log (gridExponential_pos _ _ _ _ _)] using h

/-- A finite limit in probability of the grid log likelihoods exponentiates to a normalized,
strictly positive density. Strict positivity follows pointwise from `Real.exp_pos`. -/
theorem integral_exp_eq_one_of_tendstoInMeasure_log_gridExponential [NeBot l]
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (N k)))
    (hθ : ∀ k j, j < N k → Measurable[ℱ (τ k j)] (θ k j))
    (hK : ∀ k j, j < N k → ∀ᵐ ω ∂P, |θ k j ω| ≤ K)
    (hT : ∀ k, (τ k (N k) : ℝ) - τ k 0 ≤ T) {L : Ω → ℝ}
    (hL : TendstoInMeasure P (fun k ω ↦ log (gridExponential (τ k) (θ k) W (N k) ω)) l L) :
    ∫ ω, exp (L ω) ∂P = 1 := by
  exact hW.integral_eq_one_of_tendstoInMeasure_gridExponential hτ hθ hK hT
    (hW.tendstoInMeasure_gridExponential_of_log hτ hθ hL)

end TauCeti.Probability.IsFilteredPreBrownianReal
