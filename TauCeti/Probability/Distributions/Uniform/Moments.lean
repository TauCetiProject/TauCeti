/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance

/-!
# Moments and transforms of labelled finite uniform laws

A uniform sample from a finite set, followed by a real-valued labelling, has the empirical
distribution of those labels. Repeated labels retain their multiplicities. This file computes
its natural moments, mean, variance, moment-generating function, cumulant-generating function,
and characteristic function as normalized finite sums. Its exponential-integrability domain is
all of `ℝ`.

The formulas include the empty-set case: the uniform measure, its transforms, and the normalized
sums are then zero under Lean's totalized inverse convention. No ordering or injectivity
assumption is placed on the labels.

Random variables with a labelled finite uniform law inherit the same formulas through `HasLaw`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Finset

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

private theorem integrable_comp_map_uniformOn_finset (s : Finset α) (label : α → ℝ)
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g ((uniformOn (s : Set α)).map label)) :
    Integrable g ((uniformOn (s : Set α)).map label) := by
  rw [integrable_map_measure hg (s.aemeasurable_uniformOn_finset label)]
  exact s.integrable_uniformOn_finset (g ∘ label)

/-- Every natural raw moment of a real-labelled finite uniform law is the normalized finite
power sum. -/
theorem integral_pow_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(uniformOn (s : Set α)).map label =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ n := by
  rw [integral_map (s.aemeasurable_uniformOn_finset label) (by fun_prop),
    integral_uniformOn_finset]
  simp only [smul_eq_mul]

/-- The mean of a real-labelled finite uniform law is the arithmetic mean of its labels. -/
theorem integral_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) :
    ∫ x : ℝ, x ∂(uniformOn (s : Set α)).map label =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i := by
  simpa only [pow_one] using s.integral_pow_id_map_uniformOn_finset label 1

/-- The variance of a real-labelled finite uniform law is its normalized second moment minus the
square of its arithmetic mean. -/
theorem variance_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) :
    variance id ((uniformOn (s : Set α)).map label) =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ 2 -
        ((s.card : ℝ)⁻¹ * ∑ i ∈ s, label i) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [variance_eq_integral (by fun_prop)]
    simp
  · let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
    have hsq : Integrable (fun x : ℝ ↦ x ^ 2) ((uniformOn (s : Set α)).map label) :=
      s.integrable_comp_map_uniformOn_finset label _ (by fun_prop)
    rw [variance_eq_sub (X := id) ((memLp_two_iff_integrable_sq (by fun_prop)).2 hsq)]
    simp only [Pi.pow_apply, id_eq, s.integral_pow_id_map_uniformOn_finset,
      s.integral_id_map_uniformOn_finset]

/-- Every real exponential moment of a real-labelled finite uniform law is finite. -/
@[simp]
theorem integrableExpSet_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) :
    integrableExpSet id ((uniformOn (s : Set α)).map label) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact s.integrable_comp_map_uniformOn_finset label _ (by fun_prop)

/-- The moment-generating function of a real-labelled finite uniform law is the normalized finite
sum of the exponentials of its labels. -/
theorem mgf_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (t : ℝ) :
    mgf id ((uniformOn (s : Set α)).map label) t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i) := by
  rw [mgf, integral_map (s.aemeasurable_uniformOn_finset label) (by fun_prop),
    integral_uniformOn_finset]
  simp only [id_eq, smul_eq_mul]

/-- The cumulant-generating function of a real-labelled finite uniform law is the logarithm of
its normalized exponential sum. -/
theorem cgf_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (t : ℝ) :
    cgf id ((uniformOn (s : Set α)).map label) t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i)) := by
  rw [cgf, s.mgf_id_map_uniformOn_finset]

/-- The characteristic function of a real-labelled finite uniform law is the normalized finite
sum of the character values at its labels. -/
theorem charFun_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (t : ℝ) :
    charFun ((uniformOn (s : Set α)).map label) t =
      (s.card : ℂ)⁻¹ * ∑ i ∈ s, Complex.exp (t * label i * Complex.I) := by
  rw [charFun_apply_real, integral_map (s.aemeasurable_uniformOn_finset label) (by fun_prop),
    integral_uniformOn_finset, Complex.real_smul]
  push_cast
  ring

end Finset

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {P : Measure Ω} {X : Ω → α}

/-- A Banach-valued observable of a finite uniform random variable has expectation equal to the
arithmetic mean of its values. -/
theorem integral_comp_uniformOn_finset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {s : Finset α} (hX : HasLaw X (uniformOn (s : Set α)) P) (f : α → E) :
    ∫ ω, f (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, f i := by
  have hint : Integrable f (uniformOn (s : Set α)) := s.integrable_uniformOn_finset f
  simpa only [Function.comp_def] using
    (hX.integral_comp (f := f) hint.aestronglyMeasurable).trans
      (s.integral_uniformOn_finset f)

/-- The variance of a real label of a finite uniform random variable is its normalized second
moment minus the square of its arithmetic mean. -/
theorem variance_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) :
    variance (fun ω ↦ label (X ω)) P =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ 2 -
        ((s.card : ℝ)⁻¹ * ∑ i ∈ s, label i) ^ 2 := by
  have hlabel : HasLaw (fun ω ↦ label (X ω)) ((uniformOn (s : Set α)).map label) P :=
    (hasLaw_map (s.aemeasurable_uniformOn_finset label)).fun_comp hX
  rw [hlabel.variance_eq, s.variance_id_map_uniformOn_finset]

/-- Every real exponential moment of a real label of a finite uniform random variable is finite. -/
theorem integrableExpSet_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) :
    integrableExpSet (fun ω ↦ label (X ω)) P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  simpa only [Function.comp_def] using hX.integrable_comp
    (f := fun i ↦ Real.exp (t * label i))
    (s.integrable_uniformOn_finset fun i ↦ Real.exp (t * label i))

/-- The mgf of a real label of a finite uniform random variable is its normalized exponential
sum. -/
theorem mgf_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    mgf (fun ω ↦ label (X ω)) P t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i) := by
  simpa only [mgf, smul_eq_mul] using
    hX.integral_comp_uniformOn_finset fun i ↦ Real.exp (t * label i)

/-- The cgf of a real label of a finite uniform random variable is the logarithm of its normalized
exponential sum. -/
theorem cgf_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    cgf (fun ω ↦ label (X ω)) P t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i)) := by
  rw [cgf, hX.mgf_comp_uniformOn_finset]

/-- The characteristic function of a real label of a finite uniform random variable is its
normalized finite character sum. -/
theorem charFun_map_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    charFun (P.map fun ω ↦ label (X ω)) t =
      (s.card : ℂ)⁻¹ * ∑ i ∈ s, Complex.exp (t * label i * Complex.I) := by
  have hlabel : HasLaw (fun ω ↦ label (X ω)) ((uniformOn (s : Set α)).map label) P :=
    (hasLaw_map (s.aemeasurable_uniformOn_finset label)).fun_comp hX
  rw [hlabel.map_eq, s.charFun_map_uniformOn_finset]

end ProbabilityTheory.HasLaw
