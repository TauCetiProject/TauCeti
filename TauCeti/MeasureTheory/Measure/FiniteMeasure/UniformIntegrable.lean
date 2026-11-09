/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation

/-!
# Integrals of unbounded functions along weakly convergent finite measures

Weak convergence `μᵢ ⇀ μ` of finite measures is defined by convergence of the integrals of
bounded continuous functions. For an *unbounded* continuous function `g : Ω → ℝ≥0` the integrals
`∫⁻ g ∂μᵢ` need not converge to `∫⁻ g ∂μ`: mass escaping to the region where `g` is large can
carry a non-vanishing share of the integral. This file proves that this is the only obstruction.
The integrals converge exactly when the tails of `g` are *uniformly integrable along the family*:
for every `ε > 0` there is a level `R` such that eventually `∫⁻ x in {x | R ≤ g x}, g x ∂μᵢ ≤ ε`.

This is the measure-theoretic core of the characterization of convergence in the `p`-Wasserstein
distance by weak convergence together with convergence of `p`-moments, where `g` is the `p`-th
power of the distance to a basepoint. Everything is stated for finite measures; probability
measures are the special case reached through `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Both directions compare `g` with its truncations `min g R`, which are bounded continuous and hence
have converging integrals, and use that `g - R` and the tail `g` on `{x | 2 R ≤ g x}` control
each other. No metric structure on `Ω` and no finiteness of `∫⁻ g ∂μ` is needed for the
sufficiency of the tail condition; the necessity needs `∫⁻ g ∂μ ≠ ∞`.

## Main statements

* `TauCeti.tendsto_lintegral_of_forall_exists_setLIntegral_le` — uniformly integrable tails along a
  weakly convergent family give convergence of the integrals;
* `TauCeti.tendsto_lintegral_of_sq_bound` — an eventual uniform second-moment bound gives
  convergence of the integrals;
* `TauCeti.exists_setLIntegral_le_of_tendsto_lintegral` — conversely, convergence of the
  integrals to a finite limit gives uniformly integrable tails;
* `TauCeti.tendsto_lintegral_iff_forall_exists_setLIntegral_le` — the resulting equivalence.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd edition, Wiley 1999, Theorems 3.5
  and 3.6, stated there for real random variables converging in distribution.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 6.8,
  where this tail condition defines weak convergence in `P_p`.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
  {g : Ω → ℝ≥0} {γ : Type*} {L : Filter γ} {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω}

/-- The truncations `min g R` of a continuous function are bounded continuous, so their integrals
converge along a weakly convergent family. -/
private theorem tendsto_lintegral_min (hg : Continuous g) (h : Tendsto μs L (𝓝 μ)) (R : ℝ≥0) :
    Tendsto (fun i ↦ ∫⁻ x, min (g x : ℝ≥0∞) R ∂(μs i : Measure Ω)) L
      (𝓝 (∫⁻ x, min (g x : ℝ≥0∞) R ∂(μ : Measure Ω))) := by
  let f : BoundedContinuousFunction Ω ℝ≥0 := BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ min (g x) R, hg.min continuous_const⟩ R fun x y ↦ by
      rw [NNReal.dist_eq]
      exact abs_sub_le_of_nonneg_of_le (by positivity) (by exact_mod_cast min_le_right _ _)
        (by positivity) (by exact_mod_cast min_le_right _ _)
  simpa [f, ENNReal.coe_min] using FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.1 h f

/-- The lower half of the convergence holds with no tail condition: along a weakly convergent
family the integral of a continuous function can only drop in the limit. -/
private theorem eventually_lt_lintegral (hg : Continuous g) (h : Tendsto μs L (𝓝 μ))
    {a : ℝ≥0∞} (ha : a < ∫⁻ x, g x ∂(μ : Measure Ω)) :
    ∀ᶠ i in L, a < ∫⁻ x, g x ∂(μs i : Measure Ω) := by
  obtain ⟨R, hR⟩ := ((tendsto_lintegral_min_atTop
    hg.measurable.coe_nnreal_ennreal.aemeasurable).eventually (lt_mem_nhds ha)).exists
  filter_upwards [(tendsto_lintegral_min hg h R).eventually (lt_mem_nhds hR)] with i hi
  exact hi.trans_le (lintegral_mono fun x ↦ min_le_left _ _)

/-- **Uniformly integrable tails give convergence of integrals.** Along a weakly convergent family
of finite measures, the integrals of a continuous function `g : Ω → ℝ≥0` converge as soon as
its tails are uniformly small: for every `ε > 0` there is a level `R` beyond which eventually the
integral of `g` is at most `ε`. -/
theorem tendsto_lintegral_of_forall_exists_setLIntegral_le (hg : Continuous g)
    (h : Tendsto μs L (𝓝 μ))
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0,
      ∀ᶠ i in L, ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) ≤ ε) :
    Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))) := by
  refine tendsto_order.2 ⟨fun a ha ↦ eventually_lt_lintegral hg h ha, fun a ha ↦ ?_⟩
  obtain ⟨b, hb, hba⟩ := exists_between ha
  obtain ⟨r, hr, hbr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hba
  obtain ⟨R, hR⟩ := htail r (by exact_mod_cast hr)
  have hmin : ∫⁻ x, min (g x : ℝ≥0∞) R ∂(μ : Measure Ω) < b :=
    (lintegral_mono fun x ↦ min_le_left _ _).trans_lt hb
  filter_upwards [(tendsto_lintegral_min hg h R).eventually (gt_mem_nhds hmin), hR] with i hi hRi
  calc ∫⁻ x, g x ∂(μs i : Measure Ω)
      ≤ ∫⁻ x, min (g x : ℝ≥0∞) R + {x | R ≤ g x}.indicator (fun x ↦ (g x : ℝ≥0∞)) x
          ∂(μs i : Measure Ω) := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : R ≤ g x
        · simp [hx]
        · simp [hx, ENNReal.coe_le_coe.2 (le_of_not_ge hx)]
    _ = ∫⁻ x, min (g x : ℝ≥0∞) R ∂(μs i : Measure Ω) +
          ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) := by
        rw [lintegral_add_left (hg.measurable.coe_nnreal_ennreal.min measurable_const),
          lintegral_indicator (measurableSet_le measurable_const hg.measurable)]
    _ < b + r :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.coe_ne_top hRi) hi hRi
    _ < a := hbr

/-- **Convergence of integrals gives uniformly integrable tails.** If a continuous function
`g : Ω → ℝ≥0` has finite integral against the limit of a weakly convergent family of finite
measures, and its integrals converge along the family, then its tails are uniformly small: for
every `ε > 0` there is a level `R` beyond which eventually the integral of `g` is at most `ε`. -/
theorem exists_setLIntegral_le_of_tendsto_lintegral (hg : Continuous g) (h : Tendsto μs L (𝓝 μ))
    (hμ : ∫⁻ x, g x ∂(μ : Measure Ω) ≠ ∞)
    (hlim : Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ R : ℝ≥0, ∀ᶠ i in L, ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) ≤ ε := by
  -- Against the limit, the excess integral vanishes as the level grows. Along the family, it is
  -- the difference of the integral of `g` and of its truncation, so it converges.
  obtain ⟨R, hR⟩ := ((tendsto_lintegral_tsub_atTop hg.measurable.coe_nnreal_ennreal.aemeasurable
    hμ).eventually (gt_mem_nhds (ENNReal.half_pos hε.ne'))).exists
  have hsub (ν : FiniteMeasure Ω) (R : ℝ≥0) :
      ∫⁻ x, g x ∂(ν : Measure Ω) - ∫⁻ x, min (g x : ℝ≥0∞) R ∂(ν : Measure Ω) =
        ∫⁻ x, (g x : ℝ≥0∞) - R ∂(ν : Measure Ω) := by
    rw [← lintegral_sub (hg.measurable.coe_nnreal_ennreal.min measurable_const)
      (ne_top_of_le_ne_top (lintegral_const_lt_top ENNReal.coe_ne_top).ne
        (lintegral_mono fun x ↦ min_le_right _ _)) (.of_forall fun x ↦ min_le_left _ _)]
    simp_rw [tsub_min]
  have hexc_i : Tendsto (fun i ↦ ∫⁻ x, (g x : ℝ≥0∞) - R ∂(μs i : Measure Ω)) L
      (𝓝 (∫⁻ x, (g x : ℝ≥0∞) - R ∂(μ : Measure Ω))) := by
    simpa only [hsub] using ENNReal.Tendsto.sub hlim (tendsto_lintegral_min hg h R) (Or.inl hμ)
  refine ⟨2 * R, ?_⟩
  filter_upwards [hexc_i.eventually (gt_mem_nhds hR)] with i hi
  -- Beyond the level `2 R`, the function is at most twice its excess over `R`.
  calc ∫⁻ x in {x | 2 * R ≤ g x}, g x ∂(μs i : Measure Ω)
      = ∫⁻ x, {x | 2 * R ≤ g x}.indicator (fun x ↦ (g x : ℝ≥0∞)) x ∂(μs i : Measure Ω) :=
        (lintegral_indicator (measurableSet_le measurable_const hg.measurable) _).symm
    _ ≤ ∫⁻ x, 2 * ((g x : ℝ≥0∞) - R) ∂(μs i : Measure Ω) := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : 2 * R ≤ g x
        · simp only [mem_ofPred_eq, hx, indicator_of_mem]
          rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.ofNat_ne_top, two_mul (g x : ℝ≥0∞)]
          refine ENNReal.le_sub_of_add_le_left (by finiteness) ?_
          gcongr
          simpa using ENNReal.coe_le_coe.2 hx
        · simp [hx]
    _ = 2 * ∫⁻ x, (g x : ℝ≥0∞) - R ∂(μs i : Measure Ω) :=
        lintegral_const_mul _ (hg.measurable.coe_nnreal_ennreal.sub measurable_const)
    _ ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- **Convergence of integrals of an unbounded function along weak convergence.** Along a weakly
convergent family of finite measures, the integrals of a continuous function `g : Ω → ℝ≥0`
with finite integral against the limit converge to that integral exactly when the tails of `g` are
uniformly small along the family. -/
theorem tendsto_lintegral_iff_forall_exists_setLIntegral_le (hg : Continuous g)
    (h : Tendsto μs L (𝓝 μ)) (hμ : ∫⁻ x, g x ∂(μ : Measure Ω) ≠ ∞) :
    Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))) ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ≥0,
        ∀ᶠ i in L, ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω) ≤ ε :=
  ⟨fun hlim _ hε ↦ exists_setLIntegral_le_of_tendsto_lintegral hg h hμ hlim hε,
    tendsto_lintegral_of_forall_exists_setLIntegral_le hg h⟩

/-- A uniform second-moment bound for a continuous nonnegative function gives convergence
of its integrals along weakly convergent finite measures. -/
theorem tendsto_lintegral_of_sq_bound (hg : Continuous g)
    (h : Tendsto μs L (𝓝 μ)) {C : ℝ≥0}
    (hC : ∀ᶠ i in L, ∫⁻ x, (g x : ℝ≥0∞) ^ 2 ∂(μs i : Measure Ω) ≤ C) :
    Tendsto (fun i ↦ ∫⁻ x, g x ∂(μs i : Measure Ω)) L
      (𝓝 (∫⁻ x, g x ∂(μ : Measure Ω))) := by
  apply tendsto_lintegral_of_forall_exists_setLIntegral_le hg h
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  let R : ℝ≥0 := max (C / δ) 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCR : R⁻¹ * C ≤ δ := by
    rw [inv_mul_eq_div, div_le_iff₀ hR]
    calc C ≤ C / δ * δ := (div_mul_cancel₀ C (by exact_mod_cast hδ.ne')).ge
         _ ≤ δ * R := by rw [mul_comm δ]; gcongr; exact le_max_left _ _
  refine ⟨R, ?_⟩
  filter_upwards [hC] with i hi
  calc
    ∫⁻ x in {x | R ≤ g x}, g x ∂(μs i : Measure Ω)
        ≤ ∫⁻ x in {x | R ≤ g x}, (R : ℝ≥0∞)⁻¹ * (g x : ℝ≥0∞) ^ 2
            ∂(μs i : Measure Ω) := by
      apply setLIntegral_mono' (measurableSet_le measurable_const hg.measurable)
      intro x hx
      have hx' : g x ≤ R⁻¹ * g x ^ 2 := by
        rw [inv_mul_eq_div, le_div_iff₀ hR, pow_two]
        gcongr
        exact hx
      simpa only [ENNReal.coe_mul, ENNReal.coe_inv hR.ne', ENNReal.coe_pow] using
        (ENNReal.coe_le_coe.mpr hx')
    _ = (R : ℝ≥0∞)⁻¹ * ∫⁻ x in {x | R ≤ g x}, (g x : ℝ≥0∞) ^ 2
        ∂(μs i : Measure Ω) := by
      rw [lintegral_const_mul _ (hg.measurable.coe_nnreal_ennreal.pow_const 2)]
    _ ≤ (R : ℝ≥0∞)⁻¹ * C := by
      gcongr
      exact (setLIntegral_le_lintegral _ _).trans hi
    _ ≤ (δ : ℝ≥0∞) := by
      simpa only [ENNReal.coe_mul, ENNReal.coe_inv hR.ne'] using (ENNReal.coe_le_coe.mpr hCR)
    _ ≤ ε := hδε.le

end TauCeti
