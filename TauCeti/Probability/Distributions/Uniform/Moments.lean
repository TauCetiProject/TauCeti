/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Moments and transforms of labelled finite uniform laws

A uniform sample from a nonempty finite set, followed by a real-valued labelling, has the
empirical distribution of those labels. Repeated labels retain their multiplicities. This file
computes its natural moments, mean, variance, moment-generating function, cumulant-generating
function, and characteristic function as normalized finite sums. Its exponential-integrability
domain is all of `ℝ`.

The results are stated for a `Finset`, so the finite-type law is obtained by taking `s = univ`.
The formulas use `Finset.integral_map_uniformOn_finset`; no ordering or injectivity assumption is
placed on the labels.

## Implementation notes

The statements and proofs follow those for labelled categorical laws in
`TauCeti.Probability.Distributions.Categorical.Moments`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Finset

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Every natural raw moment of a real-labelled finite uniform law is the normalized finite
power sum. The empty-set convention is also valid: both sides are zero. -/
theorem integral_pow_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(uniformOn (s : Set α)).map label =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ n := by
  rw [integral_map_uniformOn_finset, smul_eq_mul]

/-- The mean of a real-labelled finite uniform law is the arithmetic mean of its labels. -/
theorem integral_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) :
    ∫ x : ℝ, x ∂(uniformOn (s : Set α)).map label =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i := by
  simpa only [pow_one] using s.integral_pow_id_map_uniformOn_finset label 1

/-- The variance of a labelled finite uniform law is its mean square minus the square of its
mean. The empty-set convention is also valid: both sides are zero. -/
theorem variance_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) :
    variance id ((uniformOn (s : Set α)).map label) =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ 2 -
        ((s.card : ℝ)⁻¹ * ∑ i ∈ s, label i) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  rw [variance_eq_sub (X := id) ((memLp_two_iff_integrable_sq (by fun_prop)).2
    (s.integrable_map_uniformOn_finset label (fun x : ℝ ↦ x ^ 2)))]
  simp only [Pi.pow_apply, id_eq, s.integral_pow_id_map_uniformOn_finset,
    s.integral_id_map_uniformOn_finset]

/-- Every real exponential moment of a labelled finite uniform law is finite, including for the
zero measure obtained from an empty sampling set. -/
@[simp]
theorem integrableExpSet_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) :
    integrableExpSet id ((uniformOn (s : Set α)).map label) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact s.integrable_map_uniformOn_finset label _

/-- The moment-generating function of a labelled finite uniform law is the normalized finite
sum of exponentials. -/
theorem mgf_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (t : ℝ) :
    mgf id ((uniformOn (s : Set α)).map label) t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i) := by
  rw [mgf, integral_map_uniformOn_finset]
  simp only [id_eq, smul_eq_mul]

/-- The cumulant-generating function of a labelled finite uniform law is the logarithm of its
normalized exponential sum. -/
theorem cgf_id_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (t : ℝ) :
    cgf id ((uniformOn (s : Set α)).map label) t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i)) := by
  rw [cgf, s.mgf_id_map_uniformOn_finset]

/-- The characteristic function of a labelled finite uniform law is the normalized finite sum
of its character values. -/
theorem charFun_map_uniformOn_finset (s : Finset α) (label : α → ℝ) (t : ℝ) :
    charFun ((uniformOn (s : Set α)).map label) t =
      (s.card : ℂ)⁻¹ * ∑ i ∈ s, Complex.exp (t * label i * Complex.I) := by
  rw [charFun_apply_real, integral_map_uniformOn_finset, Complex.real_smul]
  push_cast
  ring

end Finset

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {P : Measure Ω} {X : Ω → α}

/-- A Banach-valued observable of a uniform random element of a finite set has expectation equal
to the arithmetic mean over that set. -/
theorem integral_comp_uniformOn_finset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {s : Finset α} (hX : HasLaw X (uniformOn (s : Set α)) P) (f : α → E) :
    ∫ ω, f (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, f i := by
  have hint : Integrable f (uniformOn (s : Set α)) := s.integrable_uniformOn_finset f
  simpa only [Function.comp_def] using
    (hX.integral_comp hint.aestronglyMeasurable).trans
      (s.integral_uniformOn_finset f)

/-- The variance of a labelled uniform random element is the empirical variance of its labels. -/
theorem variance_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) :
    variance (fun ω ↦ label (X ω)) P =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ 2 -
        ((s.card : ℝ)⁻¹ * ∑ i ∈ s, label i) ^ 2 := by
  have hlabel : HasLaw (fun ω ↦ label (X ω))
      ((uniformOn (s : Set α)).map label) P :=
    (hasLaw_map (s.aemeasurable_uniformOn_finset label)).fun_comp hX
  rw [hlabel.variance_eq, s.variance_id_map_uniformOn_finset]

/-- Every exponential moment of a labelled uniform random element is finite. -/
theorem integrableExpSet_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) :
    integrableExpSet (fun ω ↦ label (X ω)) P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hX.integrable_comp
    (s.integrable_uniformOn_finset fun i ↦ Real.exp (t * label i))

/-- The mgf of a labelled uniform random element is its normalized exponential sum. -/
theorem mgf_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    mgf (fun ω ↦ label (X ω)) P t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i) := by
  simpa only [mgf, smul_eq_mul] using hX.integral_comp_uniformOn_finset
    (fun i ↦ Real.exp (t * label i))

/-- The cgf of a labelled uniform random element is the logarithm of its normalized exponential
sum. -/
theorem cgf_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    cgf (fun ω ↦ label (X ω)) P t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i)) := by
  rw [cgf, hX.mgf_comp_uniformOn_finset]

/-- The characteristic function of a labelled uniform random element is the normalized sum of
the corresponding character values. -/
theorem charFun_map_comp_uniformOn_finset {s : Finset α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    charFun (P.map fun ω ↦ label (X ω)) t =
      (s.card : ℂ)⁻¹ * ∑ i ∈ s, Complex.exp (t * label i * Complex.I) := by
  have hlabel : HasLaw (fun ω ↦ label (X ω))
      ((uniformOn (s : Set α)).map label) P :=
    (hasLaw_map (s.aemeasurable_uniformOn_finset label)).fun_comp hX
  rw [hlabel.map_eq, s.charFun_map_uniformOn_finset]

end ProbabilityTheory.HasLaw
