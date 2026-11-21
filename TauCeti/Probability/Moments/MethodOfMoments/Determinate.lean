/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight.Normed
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# The method of moments

If probability measures `μₙ` on `ℝ` have moments that are eventually integrable and the moments
converge to those of a probability measure `μ`, and `μ` is determined by its moments among
probability measures with all moments, then `μₙ → μ` weakly (the method of moments).

Unlike `TauCeti.Probability.Moments.MethodOfMoments.CompactSupport`, this version does not require
compact support; it assumes moment determinacy instead. The criteria in
`TauCeti.Probability.Moments.Determinacy` currently use two-sided exponential integrability.
Applying them here also requires deriving the needed exponential integrability of a candidate
cluster-point law `ν` from its
matching polynomial moments.

## Main results

* `MeasureTheory.ProbabilityMeasure.integrable_pow_and_integral_pow_eq_of_mapClusterPt`:
  moments of a weak cluster point equal the limits of the moments.
* `ProbabilityMeasure.integrable_pow_and_integral_pow_eq_of_mapClusterPt_of_integral_pow_le`:
  the single-moment version, needing only a bounded twice-order moment.
* `ProbabilityMeasure.tendsto_of_tendsto_integral_pow_of_forall_integral_pow_eq_imp_eq`: weak
  convergence when the limit is determined by its moments.

## Implementation notes

Bounded second moments give tightness, and Prokhorov's theorem gives compactness of an eventual
family. Lower semicontinuity of integrals gives integrability at a cluster point, while uniform
integrability gives convergence of the moments along the cluster-point filter.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

open TauCeti

private theorem tendsto_toReal_lintegral_ofReal_of_sq_bound
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {f g : ℝ → ℝ} {B : ℝ}
    (hf : Continuous f) (hfsq : ∀ x, f x ^ 2 = g x ^ 2)
    (hfν : Integrable f (ν : Measure ℝ))
    (hμ : Tendsto (fun i ↦ (μn i).toFiniteMeasure) l (𝓝 ν.toFiniteMeasure))
    (h2 : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) (μn i : Measure ℝ))
    (hB : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂(μn i : Measure ℝ) ≤ B) :
    Tendsto (fun i ↦ (∫⁻ x, ENNReal.ofReal (f x) ∂(μn i : Measure ℝ)).toReal) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure ℝ)).toReal) := by
  have hbound : ∀ᶠ i in l,
      ∫⁻ x, (Real.toNNReal (f x) : ℝ≥0∞) ^ 2 ∂(μn i : Measure ℝ) ≤
        (Real.toNNReal B : ℝ≥0∞) := by
    filter_upwards [h2, hB] with i h2i hBi
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂(μn i : Measure ℝ) := by
        refine lintegral_mono fun x ↦ ?_
        change ENNReal.ofReal (f x) ^ 2 ≤ ENNReal.ofReal (g x ^ 2)
        by_cases hx : 0 ≤ f x
        · rw [← ENNReal.ofReal_pow hx, hfsq x]
        · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hx), zero_pow (by decide)]
          exact bot_le
      _ = ENNReal.ofReal (∫ x, g x ^ 2 ∂(μn i : Measure ℝ)) :=
        (ofReal_integral_eq_lintegral_ofReal h2i (.of_forall fun x ↦ sq_nonneg (g x))).symm
      _ ≤ (Real.toNNReal B : ℝ≥0∞) := ENNReal.ofReal_le_ofReal hBi
  have hfinite : ∫⁻ x, ENNReal.ofReal (f x) ∂(ν : Measure ℝ) ≠ ∞ := by
    have h := (lintegral_ofReal_ne_top_iff_integrable
      hfν.pos_part.aestronglyMeasurable (.of_forall fun x ↦ le_max_right (f x) 0)).2
        hfν.pos_part
    simpa using h
  have h := TauCeti.tendsto_lintegral_of_sq_bound
    (continuous_real_toNNReal.comp hf) hμ hbound
  exact (ENNReal.tendsto_toReal hfinite).comp h

/-- A weak cluster point preserves the integral of a continuous function when its square has an
eventual integral bound. -/
theorem integral_eq_of_mapClusterPt_of_integral_sq_le
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {g : ℝ → ℝ} {m B : ℝ}
    (hg : Continuous g)
    (h2 : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) (μn i : Measure ℝ))
    (hB : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂(μn i : Measure ℝ) ≤ B)
    (hlim : Tendsto (fun i ↦ ∫ x, g x ∂(μn i : Measure ℝ)) l (𝓝 m))
    (hν : MapClusterPt ν l μn) :
    ∫ x, g x ∂(ν : Measure ℝ) = m := by
  have hint : ∀ᶠ i in l, Integrable g (μn i : Measure ℝ) := by
    filter_upwards [h2] with i hi
    simpa only [pow_one] using
      (integrable_pow_of_le hg.aestronglyMeasurable (by omega : 1 ≤ 2) hi)
  have h2ν : Integrable (fun x ↦ g x ^ 2) (ν : Measure ℝ) :=
    (integrable_and_integral_le_of_mapClusterPt_of_eventually_le
      (hg.pow 2).lowerSemicontinuous (fun x ↦ sq_nonneg (g x)) h2 hB hν).1
  have hνint : Integrable g (ν : Measure ℝ) := by
    simpa only [pow_one] using
      (integrable_pow_of_le hg.aestronglyMeasurable (by omega : 1 ≤ 2) h2ν)
  let L : Filter ι := l ⊓ comap μn (𝓝 ν)
  have : L.NeBot := by
    rw [show L = l ⊓ comap μn (𝓝 ν) from rfl, neBot_inf_comap_iff_map, inf_comm]
    exact hν
  have hμ : Tendsto (fun i ↦ (μn i).toFiniteMeasure) L (𝓝 ν.toFiniteMeasure) :=
    toFiniteMeasure_continuous.tendsto ν |>.comp (tendsto_comap.mono_left inf_le_right)
  have hp := tendsto_toReal_lintegral_ofReal_of_sq_bound hg (fun _ ↦ rfl) hνint hμ
    (h2.filter_mono inf_le_left) (hB.filter_mono inf_le_left)
  have hn := tendsto_toReal_lintegral_ofReal_of_sq_bound hg.neg (fun x ↦ by simp) hνint.neg hμ
    (h2.filter_mono inf_le_left) (hB.filter_mono inf_le_left)
  have hconv : Tendsto (fun i ↦ ∫ x, g x ∂(μn i : Measure ℝ)) L
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) := by
    have hdiff := hp.sub hn
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hνint]
    refine hdiff.congr' ?_
    filter_upwards [hint.filter_mono inf_le_left] with i hi
    exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm
  exact tendsto_nhds_unique hconv (hlim.mono_left inf_le_left)

/-- A weak cluster point inherits a fixed moment if that moment converges and the moments
of twice its order are eventually integrable and uniformly bounded. -/
theorem integrable_pow_and_integral_pow_eq_of_mapClusterPt_of_integral_pow_le
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {m B : ℝ} (k : ℕ)
    (hint : ∀ᶠ i in l, Integrable (fun x : ℝ => x ^ (2 * k)) (μn i : Measure ℝ))
    (hB : ∀ᶠ i in l, ∫ x, x ^ (2 * k) ∂(μn i : Measure ℝ) ≤ B)
    (hlimk : Tendsto (fun i => ∫ x, x ^ k ∂(μn i : Measure ℝ)) l (𝓝 m))
    (hν : MapClusterPt ν l μn) :
    Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) ∧
      ∫ x, x ^ k ∂(ν : Measure ℝ) = m := by
  have hnonneg : ∀ x : ℝ, 0 ≤ x ^ (2 * k) := by
    intro x
    rw [Nat.mul_comm, pow_mul]
    exact sq_nonneg (x ^ k)
  have h2k : Integrable (fun x : ℝ => x ^ (2 * k)) (ν : Measure ℝ) :=
    (TauCeti.integrable_and_integral_le_of_mapClusterPt_of_eventually_le
      (continuous_id.pow (2 * k)).lowerSemicontinuous
      hnonneg hint hB hν).1
  have hk : Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ) :=
    integrable_pow_of_le aestronglyMeasurable_id (by omega) h2k
  have hpow (x : ℝ) : x ^ (2 * k) = (x ^ k) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  have h2 : ∀ᶠ i in l, Integrable (fun x : ℝ => (x ^ k) ^ 2) (μn i : Measure ℝ) := by
    filter_upwards [hint] with i hi
    exact hi.congr (ae_of_all _ hpow)
  have hB' : ∀ᶠ i in l, ∫ x, (x ^ k) ^ 2 ∂(μn i : Measure ℝ) ≤ B := by
    filter_upwards [hB] with i hi
    rwa [← integral_congr_ae (ae_of_all _ hpow)]
  refine ⟨hk, ?_⟩
  exact integral_eq_of_mapClusterPt_of_integral_sq_le (continuous_id.pow k)
    h2 hB' hlimk hν

/-- A weak cluster point of probability measures with converging moments has finite moments,
equal to the limits. -/
theorem integrable_pow_and_integral_pow_eq_of_mapClusterPt
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ}
    {m : ℕ → ℝ} (hint : ∀ k, ∀ᶠ n in l,
      Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) l (𝓝 (m k)))
    (hν : MapClusterPt ν l μn) :
    (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) ∧
      ∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = m k := by
  have h k := integrable_pow_and_integral_pow_eq_of_mapClusterPt_of_integral_pow_le
    (B := m (2 * k) + 1) k (hint (2 * k))
    ((hlim (2 * k)).eventually (Iio_mem_nhds (by linarith)) |>.mono fun _ hi => hi.le)
    (hlim k) hν
  exact ⟨fun k => (h k).1, fun k => (h k).2⟩

/-- **The method of moments.** Let `μn` be probability measures on `ℝ` whose moments are
eventually finite and converge to those of `μ`. If `μ` is determined by its moments among
probability measures with finite moments, then `μn` converges weakly to `μ`. -/
theorem tendsto_of_tendsto_integral_pow_of_forall_integral_pow_eq_imp_eq
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ}
    (hint : ∀ k, ∀ᶠ n in l, Integrable (fun x : ℝ => x ^ k) (μn n : Measure ℝ))
    (hlim : ∀ k, Tendsto (fun n => ∫ x, x ^ k ∂(μn n : Measure ℝ)) l
      (𝓝 (∫ x, x ^ k ∂(μ : Measure ℝ))))
    (hdet : ∀ ν : ProbabilityMeasure ℝ, (∀ k, Integrable (fun x : ℝ => x ^ k) (ν : Measure ℝ)) →
      (∀ k, ∫ x, x ^ k ∂(ν : Measure ℝ) = ∫ x, x ^ k ∂(μ : Measure ℝ)) → ν = μ) :
    Tendsto μn l (𝓝 μ) := by
  let B : ℝ := (∫ x, x ^ 2 ∂(μ : Measure ℝ)) + 1
  let s : Set ι := {n | Integrable (fun x : ℝ => x ^ 2) (μn n : Measure ℝ) ∧
    ∫ x, x ^ 2 ∂(μn n : Measure ℝ) ≤ B}
  have hμ2_lt_B : ∫ x, x ^ 2 ∂(μ : Measure ℝ) < B := by
    dsimp [B]
    linarith
  have hs : s ∈ l := by
    filter_upwards [hint 2, (hlim 2).eventually
      (Iio_mem_nhds hμ2_lt_B)] with n hi hb
    exact ⟨hi, hb.le⟩
  have htight : IsTightMeasureSet
      ((fun p : ProbabilityMeasure ℝ => (p : Measure ℝ)) '' (μn '' s)) := by
    refine TauCeti.isTightMeasureSet_of_integral_sq_le (B := B) ?_
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact hn
  have hevent : ∀ᶠ n in l, μn n ∈ closure (μn '' s) := by
    filter_upwards [hs] with n hn
    exact subset_closure ⟨n, hn, rfl⟩
  refine (isCompact_closure_of_isTightMeasureSet htight).tendsto_nhds_of_unique_mapClusterPt
    hevent fun ν _ hν => ?_
  obtain ⟨h1, h2⟩ := integrable_pow_and_integral_pow_eq_of_mapClusterPt hint hlim hν
  exact hdet ν h1 h2

end MeasureTheory.ProbabilityMeasure
