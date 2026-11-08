/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Exposure
import TauCeti.Combinatorics.DenseGraphLimits.Sampling.Expectation
import TauCeti.Probability.Concentration.SubgaussianTail
import TauCeti.Probability.McDiarmid

/-!
# Concentration of sampled homomorphism densities

For a fixed finite graph `F`, its ordinary homomorphism density in a graphon sample `G(n, W)`
concentrates exponentially around the graphon homomorphism density. The proof applies McDiarmid's
bounded-differences inequality to the padded vertex exposure: its coordinates are independent, its
pushforward is the sampling law, and changing one coordinate moves the density by at most
`|V(F)| / n`.

McDiarmid centers the estimator at its finite-sample mean. The ordinary density is not exactly
unbiased because vertex maps may collide, so the proof compares it to the injective density. The
latter is unbiased, while their pointwise difference is at most `|V(F)|.choose 2 / n`. The stated
side condition absorbs this collision bias.

## Main result

* `TauCeti.DenseGraphLimits.sampleGraph_homDensityFin_concentration` — the probability of a
  deviation of at least `ε` is at most `2 * exp (-ε²n / (2|V(F)|²))`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §10.1.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SampleExposure.lean`.
  The centering, collision-bias transfer, and two-tail calculation are adapted from that file.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integration along the padded exposure agrees with integration under the graphon sampling law.
This is the integral form of `map_exposedSample`. -/
private theorem integral_homDensityFin_exposedSample {V : Type*} [Fintype V]
    (F : SimpleGraph V) (W : Graphon Ω μ) (n : ℕ) :
    (∫ x, homDensityFin F (exposedSample W x) ∂exposureMeasure μ n) =
      ∫ G, homDensityFin F G ∂sampleGraph W n := by
  have hG : Measurable fun G : SimpleGraph (Fin n) => homDensityFin F G :=
    measurable_of_finite _
  rw [← map_exposedSample W n,
    integral_map (measurable_exposedSample W).aemeasurable hG.aestronglyMeasurable]

/-- The collision bias of the mean ordinary homomorphism density along the padded exposure is at
most `ε / 2` once `2q² ≤ εn`, where `q` is the number of vertices of `F`. -/
private theorem abs_integral_homDensityFin_exposedSample_sub_le {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} {ε : ℝ}
    (hn0 : 0 < n) (hVn : Fintype.card V ≤ n)
    (hn : 2 * (Fintype.card V : ℝ) ^ 2 ≤ ε * n) :
    |(∫ x, homDensityFin F (exposedSample W x) ∂exposureMeasure μ n) - homDensity F W| ≤
      ε / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hchoose : ((Fintype.card V).choose 2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow (Fintype.card V) 2
  rw [integral_homDensityFin_exposedSample F W n]
  calc
    |(∫ G, homDensityFin F G ∂sampleGraph W n) - homDensity F W|
        ≤ ((Fintype.card V).choose 2 : ℝ) / n :=
      F.abs_integral_homDensityFin_sampleGraph_sub_le W hVn
    _ ≤ (Fintype.card V : ℝ) ^ 2 / n := by gcongr
    _ ≤ ε / 2 := (div_le_iff₀ hnR).2 (by nlinarith [hn])

/-- The concentration bound when `F` has a vertex and `ε ≤ 1`: McDiarmid's inequality for the
padded vertex exposure, centered at the finite-sample mean, together with the collision bias. -/
private theorem sampleGraph_homDensityFin_concentration_of_card_pos {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} {ε : ℝ}
    (hε1 : ε ≤ 1) (hq : 0 < Fintype.card V) (hn : 2 * (Fintype.card V : ℝ) ^ 2 ≤ ε * n) :
    (sampleGraph W n).real {G | ε ≤ |homDensityFin F G - homDensity F W|} ≤
      2 * Real.exp (-(ε ^ 2 * n) / (2 * (Fintype.card V : ℝ) ^ 2)) := by
  have hqR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hq
  have hnpos : 0 < n := Nat.pos_of_ne_zero fun hn0 => by
    subst n
    norm_num at hn
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hVn : Fintype.card V ≤ n := by
    have hεn : ε * (n : ℝ) ≤ n := by nlinarith
    have hq1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hq
    have hVnR : (Fintype.card V : ℝ) ≤ n := by nlinarith
    exact_mod_cast hVnR
  let ν : Measure (Ω × (Fin n → ℝ)) :=
    μ.prod (Measure.pi fun _ : Fin n => Probability.uniformMeasure 0 1)
  let f : (Fin n → Ω × (Fin n → ℝ)) → ℝ := fun x => homDensityFin F (exposedSample W x)
  have hf : Measurable f :=
    (measurable_of_finite fun G : SimpleGraph (Fin n) => homDensityFin F G).comp
      (measurable_exposedSample W)
  have hsub : ProbabilityTheory.HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂Measure.pi fun _ : Fin n => ν)
      ((n : ℝ≥0) * (Real.toNNReal ((Fintype.card V : ℝ) / (n : ℝ)) / 2) ^ 2)
      (Measure.pi fun _ : Fin n => ν) :=
    Probability.hasSubgaussianMGF_of_bounded_differences_fin ν f hf
      ((Fintype.card V : ℝ) / n) fun x i y => by
        simpa [f] using abs_homDensityFin_exposedSample_update_le F W x i y
  have hν : Measure.pi (fun _ : Fin n => ν) = exposureMeasure μ n := by
    simp only [ν, exposureMeasure_def]
  rw [hν] at hsub
  rw [← map_exposedSample W n,
    map_measureReal_apply (measurable_exposedSample W) MeasurableSet.of_discrete,
    ← Probability.neg_sq_div_two_mul_variance_proxy (ε := ε)]
  exact Probability.measureReal_abs_sub_ge_le_of_hasSubgaussianMGF (g := f) hsub
    (abs_integral_homDensityFin_exposedSample_sub_le F W hnpos hVn hn)

/-- **Exponential concentration of a sampled homomorphism density.** Let `F` have `q` vertices.
If `2q² ≤ εn`, then under the graphon sampling law `G(n, W)`,

`P(|t(F, G(n, W)) - t(F, W)| ≥ ε) ≤ 2 exp(-ε²n / (2q²))`.

The side condition is eventual in `n` for fixed `F` and positive `ε`; it absorbs the collision
bias between the mean ordinary homomorphism density and the graphon density. -/
theorem sampleGraph_homDensityFin_concentration {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) {n : ℕ} {ε : ℝ} (_hε : 0 < ε)
    (hn : 2 * (Fintype.card V : ℝ) ^ 2 ≤ ε * n) :
    ((sampleGraph W n) {G | ε ≤ |homDensityFin F G - homDensity F W|}).toReal ≤
      2 * Real.exp (-(ε ^ 2 * n) / (2 * (Fintype.card V : ℝ) ^ 2)) := by
  rw [← Measure.real_def]
  by_cases hε1 : ε ≤ 1
  · rcases Nat.eq_zero_or_pos (Fintype.card V) with hq | hq
    · have hcard : (Fintype.card V : ℝ) = 0 := by simp [hq]
      calc
        _ ≤ (sampleGraph W n).real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp
        _ ≤ 2 * Real.exp (-(ε ^ 2 * n) / (2 * (Fintype.card V : ℝ) ^ 2)) := by
          rw [hcard]
          norm_num
    · exact sampleGraph_homDensityFin_concentration_of_card_pos F W hε1 hq hn
  · have hset : {G : SimpleGraph (Fin n) | ε ≤ |homDensityFin F G - homDensity F W|} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun G hG => ?_
      rw [Set.mem_ofPred_eq] at hG
      have hdiff : |homDensityFin F G - homDensity F W| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          linarith [homDensityFin_nonneg F G, homDensityFin_le_one F G,
            homDensity_nonneg F W, homDensity_le_one F W]
      exact (not_le.mpr (lt_of_not_ge hε1)) (hG.trans hdiff)
    rw [hset, measureReal_empty]
    positivity

end DenseGraphLimits

end TauCeti
