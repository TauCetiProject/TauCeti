/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral

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
* `MeasureTheory.FiniteMeasure.tendsto_integral_of_integral_sq_le` — convergence of real integrals
  under an eventual square-integrability bound and integrability at the limit.
* `MeasureTheory.FiniteMeasure.integrable_and_integral_eq_of_mapClusterPt_of_integral_sq_le` —
  integrability and integral equality at a weak cluster point under the same square bound.

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
  obtain ⟨R, hR⟩ := (tendsto_lintegral_min_atTop.eventually (lt_mem_nhds ha)).exists
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
  obtain ⟨R, hR⟩ := ((tendsto_lintegral_tsub_atTop hμ).eventually
    (gt_mem_nhds (ENNReal.half_pos hε.ne'))).exists
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

namespace MeasureTheory.FiniteMeasure

open TauCeti

private theorem tendsto_toReal_lintegral_ofReal_of_sq_bound
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    {ι : Type*} {l : Filter ι} {μn : ι → FiniteMeasure Ω}
    {ν : FiniteMeasure Ω} {f g : Ω → ℝ} {B : ℝ}
    (hf : Continuous f) (hfsq : ∀ x, f x ^ 2 = g x ^ 2)
    (hfν : Integrable f (ν : Measure Ω))
    (hμ : Tendsto μn l (𝓝 ν))
    (h2 : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) (μn i : Measure Ω))
    (hB : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂(μn i : Measure Ω) ≤ B) :
    Tendsto (fun i ↦ (∫⁻ x, ENNReal.ofReal (f x) ∂(μn i : Measure Ω)).toReal) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure Ω)).toReal) := by
  have hbound : ∀ᶠ i in l,
      ∫⁻ x, (Real.toNNReal (f x) : ℝ≥0∞) ^ 2 ∂(μn i : Measure Ω) ≤
        (Real.toNNReal B : ℝ≥0∞) := by
    filter_upwards [h2, hB] with i h2i hBi
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(μn i : Measure Ω) := by
        refine lintegral_mono fun x ↦ ?_
        rw [ENNReal.ofNNReal_toNNReal]
        by_cases hx : 0 ≤ f x
        · rw [← ENNReal.ofReal_pow hx, hfsq x]
        · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hx), zero_pow (by decide)]
          exact bot_le
      _ = ENNReal.ofReal (∫ x, g x ^ 2 ∂(μn i : Measure Ω)) :=
        (ofReal_integral_eq_lintegral_ofReal h2i (.of_forall fun x ↦ sq_nonneg (g x))).symm
      _ ≤ (Real.toNNReal B : ℝ≥0∞) := by
        rw [ENNReal.ofNNReal_toNNReal]
        exact ENNReal.ofReal_le_ofReal hBi
  have hfinite : ∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure Ω) ≠ ∞ := by
    have h := (lintegral_ofReal_ne_top_iff_integrable
      hfν.pos_part.aestronglyMeasurable (.of_forall fun x ↦ le_max_right (f x) 0)).2
        hfν.pos_part
    simpa using h
  have h := TauCeti.tendsto_lintegral_of_sq_bound
    (continuous_real_toNNReal.comp hf) hμ hbound
  simpa only [Function.comp_def, ENNReal.ofNNReal_toNNReal] using
    (ENNReal.tendsto_toReal hfinite).comp h

/-- Weak convergence of finite measures and an eventual bound on the integrals of `g²` imply
convergence of the integrals of continuous `g`, provided `g²` is eventually integrable and `g` is
integrable at the limit. -/
theorem tendsto_integral_of_integral_sq_le
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    {ι : Type*} {l : Filter ι} {μn : ι → FiniteMeasure Ω}
    {ν : FiniteMeasure Ω} {g : Ω → ℝ} {B : ℝ}
    (hg : Continuous g) (hνint : Integrable g (ν : Measure Ω))
    (hμ : Tendsto μn l (𝓝 ν))
    (h2 : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) (μn i : Measure Ω))
    (hB : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂(μn i : Measure Ω) ≤ B) :
    Tendsto (fun i ↦ ∫ x, g x ∂(μn i : Measure Ω)) l
      (𝓝 (∫ x, g x ∂(ν : Measure Ω))) := by
  have hint : ∀ᶠ i in l, Integrable g (μn i : Measure Ω) := by
    filter_upwards [h2] with i hi
    simpa only [pow_one] using
      (integrable_pow_of_le hg.aestronglyMeasurable (by omega : 1 ≤ 2) hi)
  have hp := tendsto_toReal_lintegral_ofReal_of_sq_bound hg (fun _ ↦ rfl) hνint hμ h2 hB
  have hn := tendsto_toReal_lintegral_ofReal_of_sq_bound hg.neg (fun x ↦ by simp) hνint.neg hμ
    h2 hB
  have hdiff := hp.sub hn
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hνint]
  refine hdiff.congr' ?_
  filter_upwards [hint] with i hi
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm

/-- If the integrals of a continuous function converge to `m` and its square is eventually
integrable with uniformly bounded integral, the function is integrable at every weak cluster point
of the finite measures and has integral `m` there. -/
theorem integrable_and_integral_eq_of_mapClusterPt_of_integral_sq_le
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    {ι : Type*} {l : Filter ι} {μn : ι → FiniteMeasure Ω}
    {ν : FiniteMeasure Ω} {g : Ω → ℝ} {m B : ℝ}
    (hg : Continuous g)
    (h2 : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) (μn i : Measure Ω))
    (hB : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂(μn i : Measure Ω) ≤ B)
    (hlim : Tendsto (fun i ↦ ∫ x, g x ∂(μn i : Measure Ω)) l (𝓝 m))
    (hν : MapClusterPt ν l μn) :
    Integrable g (ν : Measure Ω) ∧ ∫ x, g x ∂(ν : Measure Ω) = m := by
  have h2ν : Integrable (fun x ↦ g x ^ 2) (ν : Measure Ω) :=
    (integrable_and_integral_le_of_mapClusterPt_of_eventually_le_finiteMeasure
      (hg.pow 2).lowerSemicontinuous (fun x ↦ sq_nonneg (g x)) h2 hB hν).1
  have hνint : Integrable g (ν : Measure Ω) := by
    simpa only [pow_one] using
      (integrable_pow_of_le hg.aestronglyMeasurable (by omega : 1 ≤ 2) h2ν)
  let L : Filter ι := l ⊓ Filter.comap μn (𝓝 ν)
  have : L.NeBot := by
    dsimp only [L]
    rw [neBot_inf_comap_iff_map, inf_comm]
    exact hν.clusterPt.neBot
  have hμ : Tendsto μn L (𝓝 ν) := tendsto_comap.mono_left inf_le_right
  have hconv := tendsto_integral_of_integral_sq_le hg hνint hμ
    (h2.filter_mono inf_le_left) (hB.filter_mono inf_le_left)
  exact ⟨hνint, tendsto_nhds_unique hconv (hlim.mono_left inf_le_left)⟩

end MeasureTheory.FiniteMeasure
