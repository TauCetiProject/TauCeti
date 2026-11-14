/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite.Basic
public import TauCeti.Probability.GeneratingFunction
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Moments and transforms of finite uniform laws

Assigning real labels to a uniform sample from a finite set gives a finitely supported law,
with repeated labels counted with their multiplicities. Its moments and transforms are averages
over the sampling set, and every real exponential moment exists. The variance is the average
squared label minus the square of the average label.

The integration results in `Uniform.Finite.Basic` apply even to labels and observables that are
not globally measurable. All formulas, including variance, hold for the empty sampling set:
all integrals and transforms of that zero measure vanish, while its exponential-integrability
domain is still all of `ℝ`. The `HasLaw` corollaries allow any source measure with the stated law.
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

/-- Every natural raw moment of a finitely labelled uniform law is the average label power.
Its integrability follows from `Finset.integrable_map_uniformOn_finset`. -/
theorem integral_pow_map_uniformOn_finset (s : Finset α) (f : α → ℝ) (n : ℕ) :
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
      (s.integrable_map_uniformOn_finset f (fun x : ℝ ↦ x ^ 2))
  rw [variance_eq_sub hL]
  simpa only [Pi.pow_apply, id_eq] using congrArg₂ (fun x y : ℝ ↦ x - y ^ 2)
    (s.integral_pow_map_uniformOn_finset f 2) (s.integral_id_map_uniformOn_finset f)

/-- All real exponential moments of a finitely labelled uniform law exist, even when the
sampling set is empty. -/
theorem integrableExpSet_id_map_uniformOn_finset (s : Finset α) (f : α → ℝ) :
    integrableExpSet id ((uniformOn (s : Set α)).map f) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact s.integrable_map_uniformOn_finset f _

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
      (s.card : ℝ)⁻¹ • ∑ i ∈ s, Complex.exp (↑(t * f i) * Complex.I) := by
  rw [charFun_apply_real, s.integral_map_uniformOn_finset]
  simp only [Complex.ofReal_mul]

/-- For natural labels, the pgf of a finite uniform sample is the average monomial. This
polynomial formula holds at every real argument. -/
theorem pgf_map_uniformOn_finset (s : Finset α) (f : α → ℕ) (z : ℝ) :
    pgf id ((uniformOn (s : Set α)).map f) z =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, z ^ f i := by
  simpa only [pgf_def, id_eq, smul_eq_mul] using
    s.integral_map_uniformOn_finset f (fun k : ℕ ↦ z ^ k)

/-- The variance of an observable of a finite uniform sample is its average square minus the
square of its average, including for the empty sampling set. -/
theorem variance_uniformOn_finset (s : Finset α) (f : α → ℝ) :
    variance f (uniformOn (s : Set α)) =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i) ^ 2 := by
  rw [← variance_id_map (s.aemeasurable_uniformOn_finset f),
    s.variance_id_map_uniformOn_finset]

/-- The mgf of an observable of a finite uniform sample is the average exponential. -/
theorem mgf_uniformOn_finset (s : Finset α) (f : α → ℝ) (t : ℝ) :
    mgf f (uniformOn (s : Set α)) t =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * f i) := by
  simpa only [mgf, smul_eq_mul] using
    s.integral_uniformOn_finset (fun i ↦ Real.exp (t * f i))

/-- The cgf of an observable of a finite uniform sample is the logarithm of the average
exponential. -/
theorem cgf_uniformOn_finset (s : Finset α) (f : α → ℝ) (t : ℝ) :
    cgf f (uniformOn (s : Set α)) t =
      Real.log ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.exp (t * f i)) := by
  rw [cgf, s.mgf_uniformOn_finset]

/-- The pgf of a natural-valued observable of a finite uniform sample is the average monomial,
at every real argument. -/
theorem pgf_uniformOn_finset (s : Finset α) (f : α → ℕ) (z : ℝ) :
    pgf f (uniformOn (s : Set α)) z = (s.card : ℝ)⁻¹ * ∑ i ∈ s, z ^ f i := by
  simpa only [pgf_def, smul_eq_mul] using s.integral_uniformOn_finset (fun i ↦ z ^ f i)

/-- Natural raw moments of a uniform law on a finite real set are average powers. -/
theorem integral_pow_uniformOn_finset (s : Finset ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂uniformOn (s : Set ℝ) = (s.card : ℝ)⁻¹ * ∑ i ∈ s, i ^ n := by
  simpa only [smul_eq_mul] using s.integral_uniformOn_finset (fun x ↦ x ^ n)

/-- The mean of a uniform law on a finite real set is the average of its elements. -/
theorem integral_id_uniformOn_finset (s : Finset ℝ) :
    ∫ x, x ∂uniformOn (s : Set ℝ) = (s.card : ℝ)⁻¹ * ∑ i ∈ s, i := by
  simpa only [id_eq, smul_eq_mul] using s.integral_uniformOn_finset id

/-- The characteristic function of a uniform law on a finite real set is the average complex
exponential. -/
theorem charFun_uniformOn_finset (s : Finset ℝ) (t : ℝ) :
    charFun (uniformOn (s : Set ℝ)) t =
      (s.card : ℝ)⁻¹ • ∑ i ∈ s, Complex.exp (↑(t * i) * Complex.I) := by
  rw [charFun_apply_real, s.integral_uniformOn_finset]
  simp only [Complex.ofReal_mul]

end Finset

namespace TauCeti.Probability

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Raw moments of a labelled uniform sample from a finite type are average label powers. -/
theorem integral_pow_map_uniformOn_univ (f : α → ℝ) (n : ℕ) :
    ∫ x : ℝ, x ^ n ∂(uniformOn (Set.univ : Set α)).map f =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, f i ^ n := by
  simpa using (Finset.univ : Finset α).integral_pow_map_uniformOn_finset f n

/-- The mean of a labelled uniform sample from a finite type is the average label. -/
theorem integral_id_map_uniformOn_univ (f : α → ℝ) :
    ∫ x : ℝ, x ∂(uniformOn (Set.univ : Set α)).map f =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, f i := by
  simpa using (Finset.univ : Finset α).integral_id_map_uniformOn_finset f

/-- The variance of a labelled uniform sample from a finite type is the average squared label
minus the square of the average label. -/
theorem variance_id_map_uniformOn_univ (f : α → ℝ) :
    variance id ((uniformOn (Set.univ : Set α)).map f) =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, f i ^ 2 -
        ((Fintype.card α : ℝ)⁻¹ * ∑ i, f i) ^ 2 := by
  simpa using (Finset.univ : Finset α).variance_id_map_uniformOn_finset f

/-- The mgf of a labelled uniform sample from a finite type is the average exponential label. -/
theorem mgf_id_map_uniformOn_univ (f : α → ℝ) (t : ℝ) :
    mgf id ((uniformOn (Set.univ : Set α)).map f) t =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, Real.exp (t * f i) := by
  simpa using (Finset.univ : Finset α).mgf_id_map_uniformOn_finset f t

/-- The cgf of a labelled uniform sample from a finite type is the logarithm of the average
exponential label. -/
theorem cgf_id_map_uniformOn_univ (f : α → ℝ) (t : ℝ) :
    cgf id ((uniformOn (Set.univ : Set α)).map f) t =
      Real.log ((Fintype.card α : ℝ)⁻¹ * ∑ i, Real.exp (t * f i)) := by
  simpa using (Finset.univ : Finset α).cgf_id_map_uniformOn_finset f t

/-- The characteristic function of a labelled uniform sample from a finite type is the average
complex exponential label. -/
theorem charFun_map_uniformOn_univ (f : α → ℝ) (t : ℝ) :
    charFun ((uniformOn (Set.univ : Set α)).map f) t =
      (Fintype.card α : ℝ)⁻¹ • ∑ i, Complex.exp (↑(t * f i) * Complex.I) := by
  simpa using (Finset.univ : Finset α).charFun_map_uniformOn_finset f t

/-- The pgf of a naturally labelled uniform sample from a finite type is the average monomial. -/
theorem pgf_map_uniformOn_univ (f : α → ℕ) (z : ℝ) :
    pgf id ((uniformOn (Set.univ : Set α)).map f) z =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, z ^ f i := by
  simpa using (Finset.univ : Finset α).pgf_map_uniformOn_finset f z

/-- The variance of an observable of a uniform sample from a finite type is its average square
minus the square of its average. -/
theorem variance_uniformOn_univ (f : α → ℝ) :
    variance f (uniformOn (Set.univ : Set α)) =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, f i ^ 2 -
        ((Fintype.card α : ℝ)⁻¹ * ∑ i, f i) ^ 2 := by
  simpa using (Finset.univ : Finset α).variance_uniformOn_finset f

/-- The mgf of an observable of a uniform sample from a finite type is the average exponential. -/
theorem mgf_uniformOn_univ (f : α → ℝ) (t : ℝ) :
    mgf f (uniformOn (Set.univ : Set α)) t =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, Real.exp (t * f i) := by
  simpa using (Finset.univ : Finset α).mgf_uniformOn_finset f t

/-- The cgf of an observable of a uniform sample from a finite type is the logarithm of the
average exponential. -/
theorem cgf_uniformOn_univ (f : α → ℝ) (t : ℝ) :
    cgf f (uniformOn (Set.univ : Set α)) t =
      Real.log ((Fintype.card α : ℝ)⁻¹ * ∑ i, Real.exp (t * f i)) := by
  simpa using (Finset.univ : Finset α).cgf_uniformOn_finset f t

/-- The pgf of a natural-valued observable of a uniform sample from a finite type is the average
monomial. -/
theorem pgf_uniformOn_univ (f : α → ℕ) (z : ℝ) :
    pgf f (uniformOn (Set.univ : Set α)) z =
      (Fintype.card α : ℝ)⁻¹ * ∑ i, z ^ f i := by
  simpa using (Finset.univ : Finset α).pgf_uniformOn_finset f z

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {P : Measure Ω} {s : Finset α}

/-- The expectation of any observable of a native finite uniform sample is its average over
the sampling set, without a global measurability assumption on the observable. -/
theorem integral_comp_uniformOn_finset {X : Ω → α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hX : HasLaw X (uniformOn (s : Set α)) P) (g : α → E) :
    ∫ ω, g (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, g i :=
  (hX.integral_comp (s.integrable_uniformOn_finset g).aestronglyMeasurable).trans
    (s.integral_uniformOn_finset g)

/-- A native finite uniform random variable is integrable. -/
theorem integrable_uniformOn_finset [SeminormedAddGroup α] {X : Ω → α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) : Integrable X P :=
  hX.integrable (s.integrable_uniformOn_finset id)

/-- Assigning arbitrary labels to a native finite uniform random variable gives the mapped
uniform law, without requiring the labels to be globally measurable. -/
theorem map_uniformOn_finset {β : Type*} [MeasurableSpace β] {X : Ω → α}
    (hX : HasLaw X (uniformOn (s : Set α)) P) (f : α → β) :
    HasLaw (fun ω ↦ f (X ω)) ((uniformOn (s : Set α)).map f) P :=
  (hasLaw_map (s.aemeasurable_uniformOn_finset f)).fun_comp hX

/-- Every observable of a random variable with a finitely labelled uniform law is integrable. -/
theorem integrable_comp_map_uniformOn_finset {β E : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] [SeminormedAddGroup E] {X : Ω → β} {f : α → β}
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (g : β → E) :
    Integrable (fun ω ↦ g (X ω)) P :=
  hX.integrable_comp (s.integrable_map_uniformOn_finset f g)

/-- The expectation of any observable of a finitely labelled uniform random variable is its
average over the sampling inputs, without global measurability assumptions. -/
theorem integral_comp_map_uniformOn_finset {β E : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Ω → β} {f : α → β}
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (g : β → E) :
    ∫ ω, g (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, g (f i) :=
  (hX.integral_comp (s.integrable_map_uniformOn_finset f g).aestronglyMeasurable).trans
    (s.integral_map_uniformOn_finset f g)

variable {X : Ω → ℝ} {f : α → ℝ}

/-- Natural moments of a random variable with a finitely labelled uniform law are average
label powers. -/
theorem integral_pow_map_uniformOn_finset
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P = (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ n := by
  simpa only [smul_eq_mul] using hX.integral_comp_map_uniformOn_finset (fun x ↦ x ^ n)

/-- The mean of a random variable with a finitely labelled uniform law is the average label. -/
theorem integral_map_uniformOn_finset
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) :
    ∫ ω, X ω ∂P = (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i := by
  simpa only [id_eq, smul_eq_mul] using hX.integral_comp_map_uniformOn_finset id

/-- Variance of a random variable with a finitely labelled uniform law, including the empty
sampling set. -/
theorem variance_map_uniformOn_finset
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) :
    variance X P =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i) ^ 2 := by
  rw [hX.variance_eq]
  exact s.variance_id_map_uniformOn_finset f

end ProbabilityTheory.HasLaw
