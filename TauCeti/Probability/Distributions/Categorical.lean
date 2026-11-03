/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Measurability
public import TauCeti.MeasureTheory.Constructions.BorelSpace.StdSimplex
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.Probability.Quantile.Finite
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Probability.Distributions.Multinomial.Transforms
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Categorical distributions

A probability vector `p : Convexity.StdSimplex ℝ≥0 ι` determines the categorical law on
`ι` by assigning mass `p.weights i` to each category `i`.  This file gives the measure-level
definition, its singleton masses and finite-sum integration formula, and measurability in the
probability vector.

With the coordinate topology on the finite simplex, the categorical law is weakly continuous
on the full simplex, including zero weights.

Categorical laws are functorial in the category type: mapping categories along `f : ι → κ`
adds the weights over the fibres of `f`, exactly as `Convexity.StdSimplex.map` does.  Encoding a
category `i` by the one-hot count vector `Pi.single i 1` identifies the categorical law with the
one-trial multinomial law.  These facts make categorical measures usable as finite mixing laws and
connect them to the existing multinomial API.

## Main results

* `TauCeti.Probability.categoricalMeasure` is the weighted sum of Dirac measures;
* `TauCeti.Probability.categoricalMeasure_singleton` gives its masses;
* `TauCeti.Probability.integral_categoricalMeasure` evaluates integrals as finite weighted sums;
* `TauCeti.Probability.measurable_categoricalMeasure` proves parameter measurability;
* `TauCeti.Probability.continuous_categoricalMeasure` proves weak continuity on the full simplex,
  including zero weights;
* `TauCeti.Probability.map_categoricalMeasure` aggregates categories;
* `TauCeti.Probability.map_piSingle_categoricalMeasure` identifies one-hot encoding with a
  one-trial multinomial law.
* `Convexity.StdSimplex.cdf_map_categoricalMeasure` and
  `Convexity.StdSimplex.quantile_map_categoricalMeasure_eq_iff` compute the cdf and characterize
  the quantile after assigning real labels to the categories;
* `Convexity.StdSimplex.tendsto_quantile_map_categoricalMeasure_nhdsGT_zero` and
  `Convexity.StdSimplex.tendsto_quantile_map_categoricalMeasure_nhdsLT_one` give its endpoint
  limits at the extreme labels of positive weight.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {I J : Type*}

section Basic

variable [Fintype I] [MeasurableSpace I]

/-- The categorical law with probability vector `p` is the corresponding finite weighted sum of
Dirac measures. -/
def categoricalMeasure (p : StdSimplex NNReal I) : Measure I :=
  ∑ i, (p.weights i : ENNReal) • Measure.dirac i

/-- The categorical law as its defining weighted sum of Dirac measures. -/
theorem categoricalMeasure_def (p : StdSimplex NNReal I) :
    categoricalMeasure p = ∑ i, (p.weights i : ENNReal) • Measure.dirac i := (rfl)

/-- A categorical law is a probability measure. -/
instance isProbabilityMeasure_categoricalMeasure (p : StdSimplex NNReal I) :
    IsProbabilityMeasure (categoricalMeasure p) := by
  apply TauCeti.isProbabilityMeasure_sum_smul_dirac
  exact p.total_of_fintype

variable [MeasurableSingletonClass I]

/-- The mass of a category under its categorical law is its simplex weight. -/
@[simp]
theorem categoricalMeasure_singleton (p : StdSimplex NNReal I) (i : I) :
    categoricalMeasure p {i} = p.weights i := by
  classical
  rw [categoricalMeasure_def, _root_.sum_apply]
  simp [Pi.single_apply]

/-- The real mass of a category under its categorical law is its simplex weight. -/
@[simp]
theorem categoricalMeasure_real_singleton (p : StdSimplex NNReal I) (i : I) :
    (categoricalMeasure p).real {i} = p.weights i := by
  rw [measureReal_def, categoricalMeasure_singleton]
  simp

/-- Integration against a categorical law is the probability-weighted finite sum. -/
theorem integral_categoricalMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : I → E) (p : StdSimplex NNReal I) :
    ∫ i, g i ∂categoricalMeasure p = ∑ i, (p.weights i : ℝ) • g i := by
  simpa only [categoricalMeasure_real_singleton] using
    integral_fintype (μ := categoricalMeasure p) (f := g) Integrable.of_finite

end Basic

section Measurability

variable [Fintype I] [MeasurableSpace I]

/-- The categorical law is measurable in its probability vector. -/
@[fun_prop]
theorem measurable_categoricalMeasure :
    Measurable fun p : StdSimplex NNReal I ↦ categoricalMeasure p := by
  simpa only [categoricalMeasure_def, Measure.sum_fintype, id_eq] using
    (TauCeti.MeasureTheory.measurable_sum_smul_dirac
      (f := fun (p : StdSimplex NNReal I) i ↦ (p.weights i : ENNReal)) (g := id) fun i ↦
      measurable_coe_nnreal_ennreal.comp
        ((measurable_pi_apply i).comp StdSimplex.measurable_toFun_comp_weights))

end Measurability

section Continuity

variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [TopologicalSpace I] [OpensMeasurableSpace I]

/-- Categorical laws vary weakly continuously with all their weights, including zero weights. -/
theorem continuous_categoricalMeasure :
    Continuous (fun p : StdSimplex ℝ≥0 I ↦ (categoricalMeasure p).toProbabilityMeasure) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  simp only [Measure.coe_toProbabilityMeasure, integral_categoricalMeasure, smul_eq_mul]
  fun_prop

/-- A continuous probability vector gives a weakly continuous categorical family. -/
@[fun_prop]
theorem _root_.Continuous.categoricalMeasure {X : Type*} [TopologicalSpace X]
    {p : X → StdSimplex ℝ≥0 I} (hp : Continuous p) :
    Continuous (fun x ↦ (categoricalMeasure (p x)).toProbabilityMeasure) :=
  continuous_categoricalMeasure.comp hp

end Continuity

section Aggregation

variable [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

/-- Mapping a categorical law along a map of category types adds weights over its fibres. -/
@[simp]
theorem map_categoricalMeasure (f : I → J) (p : StdSimplex NNReal I) :
    (categoricalMeasure p).map f = categoricalMeasure (p.map f) := by
  classical
  have hf : Measurable f := measurable_of_finite f
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply hf (MeasurableSet.singleton j),
    categoricalMeasure_def, _root_.sum_apply, categoricalMeasure_singleton,
    StdSimplex.weights_map_apply]
  simp only [_root_.smul_apply, Measure.dirac_apply' _ (hf (MeasurableSet.singleton j)),
    Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [← Finset.sum_filter]
  push_cast
  rfl

end Aggregation

end TauCeti.Probability

namespace Convexity.StdSimplex

open TauCeti.Probability

section Quantile

variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The real mass below a cutoff after assigning real labels to categorical outcomes is the sum
of the weights of all categories whose labels lie below that cutoff. Equal labels are therefore
aggregated automatically. -/
theorem map_categoricalMeasure_real_Iio (p : StdSimplex NNReal I) (label : I → ℝ) (x : ℝ) :
    ((categoricalMeasure p).map label).real (Iio x) =
      ∑ i with label i < x, (p.weights i : ℝ) := by
  classical
  rw [map_measureReal_apply (measurable_of_finite label) measurableSet_Iio]
  have hpreimage : label ⁻¹' Iio x = (Finset.univ.filter fun i ↦ label i < x : Finset I) := by
    ext i
    simp
  rw [hpreimage, ← sum_measureReal_singleton]
  simp only [categoricalMeasure_real_singleton]

/-- The cdf after assigning real labels to categorical outcomes is the sum of the weights of all
categories whose labels are at most the cutoff. Equal labels are aggregated automatically. -/
theorem cdf_map_categoricalMeasure (p : StdSimplex NNReal I) (label : I → ℝ) (x : ℝ) :
    cdf ((categoricalMeasure p).map label) x =
      ∑ i with label i ≤ x, (p.weights i : ℝ) := by
  classical
  rw [Measure.cdf_map _ label (measurable_of_finite label)]
  have hpreimage : label ⁻¹' Iic x = (Finset.univ.filter fun i ↦ label i ≤ x : Finset I) := by
    ext i
    simp
  rw [hpreimage, ← sum_measureReal_singleton]
  simp only [categoricalMeasure_real_singleton]

/-- A real number is the quantile of a categorical law with supplied real labels exactly when
the level strictly exceeds the total weight of smaller labels and is at most the total weight of
labels no larger than it. This sorts distinct labels and aggregates equal labels automatically. -/
theorem quantile_map_categoricalMeasure_eq_iff (p : StdSimplex NNReal I) (label : I → ℝ)
    {u x : ℝ} (hu : u ∈ Ioo 0 1) :
    ((categoricalMeasure p).map label).quantile u = x ↔
      (∑ i with label i < x, (p.weights i : ℝ)) < u ∧
        u ≤ ∑ i with label i ≤ x, (p.weights i : ℝ) := by
  rw [Measure.quantile_map_finite_eq_iff _ label hu,
    ← map_measureReal_apply (measurable_of_finite label) measurableSet_Iio,
    p.map_categoricalMeasure_real_Iio,
    ← Measure.cdf_map _ label (measurable_of_finite label), p.cdf_map_categoricalMeasure]

/-- As the level tends to zero from above, categorical quantiles tend to any least label whose
category has positive weight. Zero-weight categories do not affect the endpoint. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsGT_zero
    (p : StdSimplex NNReal I) (label : I → ℝ) (i : I) (hi : 0 < (p.weights i : ℝ))
    (hmin : ∀ j, 0 < (p.weights j : ℝ) → label i ≤ label j) :
    Tendsto ((categoricalMeasure p).map label).quantile (𝓝[>] 0) (𝓝 (label i)) := by
  apply Measure.tendsto_quantile_map_finite_nhdsGT_zero (categoricalMeasure p) label i
  · simpa only [categoricalMeasure_real_singleton] using hi
  · intro j hj
    exact hmin j (by simpa only [categoricalMeasure_real_singleton] using hj)

/-- As the level tends to one from below, categorical quantiles tend to any greatest label whose
category has positive weight. Zero-weight categories do not affect the endpoint. -/
theorem tendsto_quantile_map_categoricalMeasure_nhdsLT_one
    (p : StdSimplex NNReal I) (label : I → ℝ) (i : I) (hi : 0 < (p.weights i : ℝ))
    (hmax : ∀ j, 0 < (p.weights j : ℝ) → label j ≤ label i) :
    Tendsto ((categoricalMeasure p).map label).quantile (𝓝[<] 1) (𝓝 (label i)) := by
  apply Measure.tendsto_quantile_map_finite_nhdsLT_one (categoricalMeasure p) label i
  · simpa only [categoricalMeasure_real_singleton] using hi
  · intro j hj
    exact hmax j (by simpa only [categoricalMeasure_real_singleton] using hj)

end Quantile

end Convexity.StdSimplex

namespace TauCeti.Probability

section Multinomial

variable [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Classical decidable equality used to form one-hot vectors on a finite category type. -/
local instance categoricalDecidableEq : DecidableEq I := Classical.decEq I

/-- Encoding a categorical outcome as the one-hot vector `Pi.single i 1` gives the multinomial
law with one trial. -/
@[simp]
theorem map_piSingle_categoricalMeasure (p : StdSimplex NNReal I) :
    (categoricalMeasure p).map (fun i ↦ Pi.single i 1) = multinomialMeasure 1 p := by
  classical
  apply (measurableEmbedding_multinomialToEuclidean (ι := I)).map_injective
  let _ := isProbabilityMeasure_categoricalMeasure p
  let _ := isProbabilityMeasure_multinomialMeasure 1 p
  apply Measure.ext_of_charFun
  funext t
  rw [Measure.map_map measurable_multinomialToEuclidean (by fun_prop), charFun_apply,
    integral_map (by fun_prop) (by fun_prop), integral_categoricalMeasure,
    charFun_map_multinomialToEuclidean_multinomialMeasure]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    Complex.real_smul, pow_one]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [Finset.sum_eq_single i]
  · simp only [Function.comp_apply, multinomialToEuclidean_apply, Pi.single_eq_same,
      Nat.cast_one, mul_one]
    rw [mul_comm]
  · intro j _ hji
    simp [hji]
  · simp

end Multinomial

end TauCeti.Probability
