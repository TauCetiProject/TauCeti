/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight.Normed
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.UniformIntegrable

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

Bounded second moments give tightness, and Prokhorov's theorem gives compactness of the weak
closure of an eventual family. Lower semicontinuity gives integrability at a cluster point, while
uniform integrability gives convergence of the moments along the cluster-point filter.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley (1995), Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

open TauCeti

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
  exact integrable_and_integral_eq_of_mapClusterPt_of_integral_sq_le
    (g := fun x : ℝ => x ^ k) (by fun_prop)
    (by simpa only [pow_mul'] using hint) (by simpa only [pow_mul'] using hB) hlimk hν

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
