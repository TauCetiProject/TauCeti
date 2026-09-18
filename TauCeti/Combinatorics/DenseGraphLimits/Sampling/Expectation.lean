/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Unbiased
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Closeness

/-!
# Expected homomorphism densities in graphon samples

For a fixed finite graph `F`, the expected ordinary homomorphism density of `F` in a graphon
sample `G(n, W)` converges to the graphon homomorphism density `t(F, W)`. At finite `n`, the
difference is at most `|V(F)|.choose 2 / n`.

The proof compares the ordinary homomorphism density with the injective density. The injective
density is exactly unbiased under graphon sampling, while the two finite densities differ only
when a sampled vertex map has a collision.

## Main results

* `TauCeti.DenseGraphLimits.abs_integral_homDensityFin_sampleGraph_sub_le` bounds the finite-sample
  bias of the ordinary homomorphism density;
* `TauCeti.DenseGraphLimits.tendsto_integral_homDensityFin_sampleGraph` gives convergence of its
  expectation to the graphon homomorphism density.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012),
  Sections 5.2 and 10.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The mean ordinary homomorphism density differs from the graphon density by no more than the
collision probability bound, whenever the sample has enough vertices for the injective density. -/
theorem abs_integral_homDensityFin_sampleGraph_sub_le {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ}
    (hVn : Fintype.card V ≤ n) :
    |(∫ G, homDensityFin F G ∂sampleGraph W n) - homDensity F W| ≤
      ((Fintype.card V).choose 2 : ℝ) / n := by
  rw [← integral_injHomDensity_sampleGraph W F hVn, ← integral_sub]
  · calc
      |∫ G, homDensityFin F G - injHomDensity F G ∂sampleGraph W n|
          ≤ ∫ G, |homDensityFin F G - injHomDensity F G| ∂sampleGraph W n :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _G, ((Fintype.card V).choose 2 : ℝ) / n ∂sampleGraph W n := by
        refine integral_mono Integrable.of_finite (integrable_const _) fun G => ?_
        simpa only [Fintype.card_fin] using homDensityFin_sub_injHomDensity_le F G
      _ = ((Fintype.card V).choose 2 : ℝ) / n := by simp
  · exact Integrable.of_finite
  · exact Integrable.of_finite

/-- The expected ordinary homomorphism density of a fixed finite graph in `G(n, W)` converges to
its graphon homomorphism density as the sample size tends to infinity. -/
theorem tendsto_integral_homDensityFin_sampleGraph {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    Filter.Tendsto (fun n : ℕ => ∫ G, homDensityFin F G ∂sampleGraph W n) Filter.atTop
      (nhds (homDensity F W)) := by
  have hbound : Filter.Tendsto
      (fun n : ℕ => ((Fintype.card V).choose 2 : ℝ) / n) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbound ε hε
  refine ⟨max (Fintype.card V) N, fun n hn => ?_⟩
  have hVn : Fintype.card V ≤ n := (le_max_left _ _).trans hn
  have hboundn := hN n ((le_max_right _ _).trans hn)
  rw [Real.dist_eq]
  refine (abs_integral_homDensityFin_sampleGraph_sub_le F W hVn).trans_lt ?_
  simpa [Real.dist_eq, abs_of_nonneg (by positivity :
    0 ≤ ((Fintype.card V).choose 2 : ℝ) / n)] using hboundn

end DenseGraphLimits

end TauCeti
