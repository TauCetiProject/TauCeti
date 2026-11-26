/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite.Basic
public import TauCeti.Probability.GeneratingFunction
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Moments and transforms of finite uniform laws

Assigning labels to a uniform sample from a finite set gives a finitely supported law,
with repeated labels counted with their multiplicities. For real labels, natural moments,
means, mgfs and characteristic functions are finite averages; the cgf is the logarithm of the
average exponential, and variance is the average square minus the square of the average.
For natural-valued labels, the pgf is the average monomial at every real argument.

For a finite type, take the sampling set to be `Finset.univ`. The integration results in
`Uniform.Finite.Basic` apply even to labels and observables that are not globally measurable.
The formulas hold for the empty sampling set, where the law is zero. Real observables have
full exponential-integrability domain even on arbitrary sampling sets: on infinite sets
`uniformOn` is zero. The `HasLaw` corollaries start from a native uniform random element.
Use `HasLaw.integral_comp_uniformOn_finset` for its labelled mean and raw moments,
and `HasLaw.fun_comp_uniformOn` for its law after labelling.

## Implementation notes

The real-labelled moment and transform formulas follow the statements and proofs for
labelled categorical laws in `TauCeti.Probability.Distributions.Categorical.Moments`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability

namespace Set

/-- All real exponential moments of an observable of `uniformOn` exist. On infinite sampling
sets this follows from the zero-measure convention. -/
@[simp]
theorem integrableExpSet_uniformOn {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (s : Set α) (f : α → ℝ) :
    integrableExpSet f (uniformOn s) = Set.univ := by
  ext t
  simp [integrableExpSet]

/-- Every real observable of a labelled uniform law has full exponential-integrability domain,
without global measurability assumptions on the labels or observable. -/
@[simp]
theorem integrableExpSet_map_uniformOn {α β : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (s : Set α) (f : α → β) (g : β → ℝ) :
    integrableExpSet g ((uniformOn s).map f) = Set.univ := by
  ext t
  simp [integrableExpSet]

end Set

namespace Finset

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Every natural raw moment of a finitely labelled uniform law is the average label power. -/
theorem integral_pow_id_map_uniformOn_finset (s : Finset α) (f : α → ℝ) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(uniformOn (s : Set α)).map f =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ n := by
  simpa only [smul_eq_mul] using s.integral_map_uniformOn_finset f (fun x : ℝ ↦ x ^ n)

/-- The mean of a finitely labelled uniform law is the average label. -/
theorem integral_id_map_uniformOn_finset (s : Finset α) (f : α → ℝ) :
    ∫ x : ℝ, x ∂(uniformOn (s : Set α)).map f =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i := by
  simpa only [id_eq, smul_eq_mul] using s.integral_map_uniformOn_finset f id

/-- The variance of a finite uniform sample is its average squared label minus the square of
its average label, including for the empty sampling set. -/
theorem variance_id_map_uniformOn_finset (s : Finset α) (f : α → ℝ) :
    variance id ((uniformOn (s : Set α)).map f) =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uniformOn_empty_meas]
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  have hL : MemLp (id : ℝ → ℝ) 2 ((uniformOn (s : Set α)).map f) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2
      (Set.integrable_map_uniformOn (s : Set α) f (fun x : ℝ ↦ x ^ 2))
  rw [variance_eq_sub hL]
  simpa only [Pi.pow_apply, id_eq] using congrArg₂ (fun x y : ℝ ↦ x - y ^ 2)
    (s.integral_pow_id_map_uniformOn_finset f 2) (s.integral_id_map_uniformOn_finset f)

/-- The mgf of a finitely labelled uniform law is the average exponential label. -/
theorem mgf_id_map_uniformOn_finset (s : Finset α) (f : α → ℝ) (t : ℝ) :
    mgf id ((uniformOn (s : Set α)).map f) t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * f i) := by
  simpa only [mgf, id_eq, smul_eq_mul] using
    s.integral_map_uniformOn_finset f (fun x : ℝ ↦ Real.exp (t * x))

/-- The cgf of a finitely labelled uniform law is the logarithm of its average exponential
label. For a nonempty set, that average is positive at every real argument. -/
theorem cgf_id_map_uniformOn_finset (s : Finset α) (f : α → ℝ) (t : ℝ) :
    cgf id ((uniformOn (s : Set α)).map f) t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * f i)) := by
  rw [cgf, s.mgf_id_map_uniformOn_finset]

/-- The characteristic function of a finitely labelled uniform law is the average complex
exponential label. -/
theorem charFun_map_uniformOn_finset (s : Finset α) (f : α → ℝ) (t : ℝ) :
    charFun ((uniformOn (s : Set α)).map f) t =
      (s.card : ℂ)⁻¹ * ∑ i ∈ s, Complex.exp (t * f i * Complex.I) := by
  rw [charFun_apply_real, integral_map_uniformOn_finset, Complex.real_smul]
  push_cast
  ring

/-- The pgf of a natural-valued observable of a finite uniform sample is the average monomial,
at every real argument. -/
theorem pgf_uniformOn_finset (s : Finset α) (f : α → ℕ) (z : ℝ) :
    pgf f (uniformOn (s : Set α)) z = (s.card : ℝ)⁻¹ * ∑ i ∈ s, z ^ f i := by
  simpa only [pgf_def, smul_eq_mul] using s.integral_uniformOn_finset (fun i ↦ z ^ f i)

end Finset

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {P : Measure Ω} {s : Finset α} {Y : Ω → α}

/-- The variance of a labelled uniform random element is the empirical variance of its labels. -/
theorem variance_comp_uniformOn_finset
    (hY : HasLaw Y (uniformOn (s : Set α)) P) (label : α → ℝ) :
    variance (fun ω ↦ label (Y ω)) P =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, label i ^ 2 -
        ((s.card : ℝ)⁻¹ * ∑ i ∈ s, label i) ^ 2 := by
  rw [(hY.fun_comp_uniformOn label).variance_eq, s.variance_id_map_uniformOn_finset]

/-- Every exponential moment of a labelled uniform random element is finite, including when
an infinite sampling set makes its law zero. -/
theorem integrableExpSet_comp_uniformOn {s : Set α}
    (hY : HasLaw Y (uniformOn s) P) (label : α → ℝ) :
    integrableExpSet (fun ω ↦ label (Y ω)) P = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hY.integrable_comp (s.integrable_uniformOn fun i ↦ Real.exp (t * label i))

/-- The mgf of a labelled uniform random element is its normalized exponential sum. -/
theorem mgf_comp_uniformOn_finset
    (hY : HasLaw Y (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    mgf (fun ω ↦ label (Y ω)) P t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i) := by
  simpa only [mgf, smul_eq_mul] using hY.integral_comp_uniformOn_finset
    (fun i ↦ Real.exp (t * label i))

/-- The cgf of a labelled uniform random element is the logarithm of its normalized exponential
sum. -/
theorem cgf_comp_uniformOn_finset
    (hY : HasLaw Y (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    cgf (fun ω ↦ label (Y ω)) P t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * label i)) := by
  rw [cgf, hY.mgf_comp_uniformOn_finset]

/-- The characteristic function of a labelled uniform random element is the normalized sum of
its character values. -/
theorem charFun_map_comp_uniformOn_finset
    (hY : HasLaw Y (uniformOn (s : Set α)) P) (label : α → ℝ) (t : ℝ) :
    charFun (P.map fun ω ↦ label (Y ω)) t =
      (s.card : ℂ)⁻¹ * ∑ i ∈ s, Complex.exp (t * label i * Complex.I) := by
  rw [(hY.fun_comp_uniformOn label).map_eq, s.charFun_map_uniformOn_finset]

end ProbabilityTheory.HasLaw
