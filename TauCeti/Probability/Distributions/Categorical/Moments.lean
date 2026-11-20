/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Categorical.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Moments and transforms of labelled categorical laws

Assigning real labels to the outcomes of a categorical law gives a finitely supported real
probability law. Its moments and transforms are weighted sums over the categories. Repeated
labels are allowed, and zero-weight categories contribute nothing, regardless of their labels.

Every function is integrable against a labelled categorical law on a carrier with measurable
singletons. In particular, all natural moments exist and the exponential-integrability domain
is the whole real line. The variance is the weighted second moment minus the squared weighted
mean, and the cumulant-generating function is the logarithm of the weighted exponential sum.

The integration formulas use `Convexity.StdSimplex.integral_map_categoricalMeasure`, which also
applies to labels in other measurable spaces and to Banach-valued observables. Native categorical
random variables inherit the corresponding expectation, variance, and transform formulas through
`HasLaw`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped NNReal

namespace Convexity.StdSimplex

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Every natural raw moment of a real-labelled categorical law is its finite weighted power
sum. Integrability is supplied by `Convexity.StdSimplex.integrable_map_categoricalMeasure`. -/
theorem integral_pow_id_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (label : I → ℝ)
    (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(categoricalMeasure p).map label =
      ∑ i, (p.weights i : ℝ) * label i ^ n := by
  simpa only [smul_eq_mul] using p.integral_map_categoricalMeasure label (fun x ↦ x ^ n)

/-- The mean of a real-labelled categorical law is the weighted mean of its labels. -/
theorem integral_id_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (label : I → ℝ) :
    ∫ x : ℝ, x ∂(categoricalMeasure p).map label = ∑ i, (p.weights i : ℝ) * label i := by
  simpa only [pow_one] using p.integral_pow_id_map_categoricalMeasure label 1

/-- The variance of a real-labelled categorical law is its weighted second moment minus the
square of its weighted mean. -/
theorem variance_id_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (label : I → ℝ) :
    variance id ((categoricalMeasure p).map label) =
      (∑ i, (p.weights i : ℝ) * label i ^ 2) -
        (∑ i, (p.weights i : ℝ) * label i) ^ 2 := by
  rw [variance_eq_sub (X := id) ((memLp_two_iff_integrable_sq (by fun_prop)).2
    (p.integrable_map_categoricalMeasure label (fun x : ℝ ↦ x ^ 2)))]
  simp only [Pi.pow_apply, id_eq, p.integral_pow_id_map_categoricalMeasure,
    p.integral_id_map_categoricalMeasure]

/-- Every real exponential moment of a real-labelled categorical law is finite. -/
@[simp]
theorem integrableExpSet_id_map_categoricalMeasure (p : StdSimplex ℝ≥0 I)
    (label : I → ℝ) :
    integrableExpSet id ((categoricalMeasure p).map label) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact p.integrable_map_categoricalMeasure label _

/-- The moment-generating function of a real-labelled categorical law is the finite weighted
sum of the exponentials of its labels. -/
theorem mgf_id_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (label : I → ℝ) (t : ℝ) :
    mgf id ((categoricalMeasure p).map label) t =
      ∑ i, (p.weights i : ℝ) * Real.exp (t * label i) := by
  simp only [mgf, id_eq, p.integral_map_categoricalMeasure, smul_eq_mul]

/-- The cumulant-generating function of a real-labelled categorical law is the logarithm of
its weighted exponential sum, for every real argument. -/
theorem cgf_id_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (label : I → ℝ) (t : ℝ) :
    cgf id ((categoricalMeasure p).map label) t =
      Real.log (∑ i, (p.weights i : ℝ) * Real.exp (t * label i)) := by
  rw [cgf, p.mgf_id_map_categoricalMeasure]

/-- The characteristic function of a real-labelled categorical law is the weighted sum of
the character values at its labels. -/
theorem charFun_map_categoricalMeasure (p : StdSimplex ℝ≥0 I) (label : I → ℝ) (t : ℝ) :
    charFun ((categoricalMeasure p).map label) t =
      ∑ i, (p.weights i : ℂ) * Complex.exp (t * label i * Complex.I) := by
  simp [charFun_apply_real, p.integral_map_categoricalMeasure, Complex.real_smul]

end Convexity.StdSimplex

namespace ProbabilityTheory.HasLaw

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] {P : Measure Ω} {X : Ω → I} {p : Convexity.StdSimplex ℝ≥0 I}

/-- An observable of a categorical random variable has expectation equal to its weighted
category sum. Its integrability follows from `HasLaw.integrable_comp` and `Integrable.of_finite`.
Taking the observable to be a power of a real label gives every natural raw moment. -/
theorem integral_comp_categoricalMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hX : HasLaw X (categoricalMeasure p) P) (f : I → E) :
    ∫ ω, f (X ω) ∂P = ∑ i, (p.weights i : ℝ) • f i := by
  simpa only [Function.comp_def] using
    (hX.integral_comp (f := f) .of_discrete).trans (integral_categoricalMeasure f p)

/-- The variance of a real label of a categorical random variable is its weighted second
moment minus its squared weighted mean. -/
theorem variance_comp_categoricalMeasure (hX : HasLaw X (categoricalMeasure p) P)
    (label : I → ℝ) :
    variance (fun ω ↦ label (X ω)) P =
      (∑ i, (p.weights i : ℝ) * label i ^ 2) -
        (∑ i, (p.weights i : ℝ) * label i) ^ 2 := by
  have hlabel : HasLaw (fun ω ↦ label (X ω)) ((categoricalMeasure p).map label) P :=
    (hasLaw_map (measurable_of_finite label).aemeasurable).fun_comp hX
  rw [hlabel.variance_eq, p.variance_id_map_categoricalMeasure]

/-- Every real exponential moment of a real label of a categorical random variable is finite.
The law hypothesis already guarantees that the source measure is a probability measure. -/
theorem integrableExpSet_comp_categoricalMeasure (hX : HasLaw X (categoricalMeasure p) P)
    (label : I → ℝ) :
    integrableExpSet (fun ω ↦ label (X ω)) P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  simpa only [Function.comp_def] using
    hX.integrable_comp (f := fun i ↦ Real.exp (t * label i)) Integrable.of_finite

/-- The mgf of a real label of a categorical random variable is its weighted exponential sum. -/
theorem mgf_comp_categoricalMeasure (hX : HasLaw X (categoricalMeasure p) P)
    (label : I → ℝ) (t : ℝ) :
    mgf (fun ω ↦ label (X ω)) P t =
      ∑ i, (p.weights i : ℝ) * Real.exp (t * label i) := by
  simpa only [mgf, smul_eq_mul] using
    hX.integral_comp_categoricalMeasure (fun i ↦ Real.exp (t * label i))

/-- The cgf of a real label of a categorical random variable is the logarithm of its weighted
exponential sum on the full real domain. -/
theorem cgf_comp_categoricalMeasure (hX : HasLaw X (categoricalMeasure p) P)
    (label : I → ℝ) (t : ℝ) :
    cgf (fun ω ↦ label (X ω)) P t =
      Real.log (∑ i, (p.weights i : ℝ) * Real.exp (t * label i)) := by
  rw [cgf, hX.mgf_comp_categoricalMeasure]

/-- The characteristic function of the real label of a categorical random variable is its
weighted sum of character values. -/
theorem charFun_map_comp_categoricalMeasure (hX : HasLaw X (categoricalMeasure p) P)
    (label : I → ℝ) (t : ℝ) :
    charFun (P.map (fun ω ↦ label (X ω))) t =
      ∑ i, (p.weights i : ℂ) * Complex.exp (t * label i * Complex.I) := by
  have hlabel : HasLaw (fun ω ↦ label (X ω)) ((categoricalMeasure p).map label) P :=
    (hasLaw_map (measurable_of_finite label).aemeasurable).fun_comp hX
  rw [hlabel.map_eq, p.charFun_map_categoricalMeasure]

end ProbabilityTheory.HasLaw
