/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Moment
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Const
public import TauCeti.Probability.Exchangeability.ConditionallyIID.WeakConvergence
public import Mathlib.Probability.StrongLaw

/-!
# Empirical measures converge in the Wasserstein distance

Let `Y 0, Y 1, …` be independent random points of a separable pseudometric space, each with law
`μ`, and let `μ` have finite `p`-moment for a finite nonzero exponent `p`. Then, almost surely,
the empirical measures `(n + 1)⁻¹ ∑_{i ≤ n} δ_{Y i}` converge to `μ` in the `p`-Wasserstein
distance. This is the almost-sure consistency of the empirical measure as an estimator of `μ` in
every `W_p` with `p < ∞`.

The proof reads the convergence off the characterization of Wasserstein convergence as weak
convergence together with convergence of `p`-moments,
`TauCeti.tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral`. Both
inputs hold almost surely:

* the empirical measures converge weakly to `μ` almost surely (Varadarajan's theorem), which is the
  constant-directing-measure case of
  `TauCeti.Probability.ConditionallyIIDWith.tendsto_empiricalMeasure_ae`;
* the `p`-moment `∫⁻ y, edist x y ^ p` of the empirical measure about a basepoint `x` is the
  sample mean of the integrable variables `dist x (Y i) ^ p`, so it converges almost surely to the
  `p`-moment of `μ` by the strong law of large numbers `ProbabilityTheory.strong_law_ae`.

The exponent is finite: at `p = ∞` the statement fails. For the law giving mass `1 / 2` to each
of two points at distance `1`, an odd number of samples never splits evenly between them, so some
mass has to cross, and those empirical measures are at `W_∞` distance `1` from the law.

## Main statements

* `TauCeti.tendsto_wassersteinEDist_empiricalMeasure_ae` — almost surely, the empirical measures of
  an i.i.d. sequence with law `μ` converge to `μ` in the `p`-Wasserstein distance.

## References

* V. S. Varadarajan, *On the convergence of sample probability distributions*, Sankhyā 19 (1958),
  23--26.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 6.9, the
  characterization of Wasserstein convergence used here.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace TauCeti

open Probability

variable {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [TopologicalSpace.SeparableSpace X]
  {P : Measure Ω} {Y : ℕ → Ω → X} {μ : ProbabilityMeasure X} {p : ℝ≥0∞}

/-- **Empirical measures converge in the Wasserstein distance.** Let `Y 0, Y 1, …` be independent
random points of a separable pseudometric space, each with law `μ`, where `μ` has finite
`p`-moment for a finite nonzero exponent `p`. Then almost surely the `p`-Wasserstein distance from
the empirical measure of `Y 0, …, Y n` to `μ` tends to `0`. -/
theorem tendsto_wassersteinEDist_empiricalMeasure_ae (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hμ : HasFiniteMoment p (μ : Measure X)) (hindep : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (μ : Measure X) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ wassersteinEDist p (empiricalMeasure (fun i ↦ Y i ω) n : Measure X) μ) atTop
      (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  obtain ⟨x, hx⟩ := hasFiniteMoment_def.mp hμ
  -- The `p`-moment of `μ` about `x` is finite.
  have hmom : ∫⁻ y, edist x y ^ p.toReal ∂(μ : Measure X) ≠ ∞ := by
    simpa only [enorm_eq_self] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hx.eLpNorm_lt_top).ne
  -- The real-valued `p`-th power of the distance to `x`, whose sample means are the moments.
  set f : X → ℝ := fun y ↦ dist x y ^ p.toReal with hf_def
  have hf : Measurable f := (continuous_const.dist continuous_id).measurable.pow_const _
  have hfe : ∀ y, edist x y ^ p.toReal = ENNReal.ofReal (f y) := fun y ↦ by
    rw [hf_def, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg hq.le]
  have hfint : Integrable f (μ : Measure X) := by
    refine ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y ↦ by positivity)).2 ?_⟩
    rw [← lintegral_congr hfe]
    exact hmom.lt_top
  have := (hY 0).isProbabilityMeasure
  -- Almost surely, the empirical measures converge weakly to `μ`.
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i ↦ (hY i).identDistrib (hY 0)
  have hweak := (ConditionallyIIDWith.of_iIndepFun_identDistrib hindep hident)
    |>.tendsto_empiricalMeasure_ae
  have hlaw : (⟨P.map (Y 0), (hY 0).map_eq ▸ inferInstance⟩ : ProbabilityMeasure X) = μ :=
    Subtype.ext (hY 0).map_eq
  -- Almost surely, the sample means of `f ∘ Y i` converge to the mean of `f` under `μ`.
  have hslln := strong_law_ae (fun i ↦ f ∘ Y i) ((hY 0).integrable_comp hfint)
    (fun i j hij ↦ (hindep.indepFun hij).comp hf hf) (fun i ↦ (hident i).comp hf)
  filter_upwards [hweak, hslln] with ω hωw hωs
  refine tendsto_wassersteinEDist_of_tendsto_probabilityMeasure_of_tendsto_lintegral hp0 hp
    (by simpa only [hlaw] using hωw) x hmom ?_
  -- The moments of the empirical measures are the sample means of `f ∘ Y i`, shifted by one
  -- because `empiricalMeasure _ n` averages the first `n + 1` points.
  rw [lintegral_congr fun y ↦ hfe y, ← ofReal_integral_eq_lintegral_ofReal hfint
    (Eventually.of_forall fun y ↦ by positivity), ← (hY 0).integral_comp hf.aestronglyMeasurable]
  refine ((ENNReal.continuous_ofReal.tendsto _).comp
    (hωs.comp (tendsto_add_atTop_nat 1))).congr fun n ↦ ?_
  have hnonneg : ∀ i, 0 ≤ f (Y i ω) := fun i ↦ by positivity
  simp only [Function.comp_apply, smul_eq_mul, lintegral_empiricalMeasure (hf.ennreal_ofReal),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹),
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hnonneg i,
    ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)),
    ENNReal.ofReal_natCast, hfe]

end TauCeti
