/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite
public import TauCeti.Probability.GeneratingFunction
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Moments and transforms of finite uniform laws

Assigning real labels to a uniform sample from a finite set gives a finitely supported law,
with repeated labels counted with their multiplicities. Its moments and transforms are averages
over the sampling set, and every real exponential moment exists. The variance is the average
squared label minus the square of the average label, for a nonempty sampling set.

The integration results in `Uniform.Finite` apply even to labels and observables that are not
globally measurable. The results here include the empty-set convention: all integrals and
transforms of that zero measure vanish, while its exponential-integrability domain is still all
of `ℝ`. Only the variance formulas require a nonempty sampling set; the `HasLaw` corollaries
allow any source measure with the stated law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability

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

/-- The variance of a nonempty finite uniform sample is its average squared label minus the
square of its average label. -/
theorem variance_id_map_uniformOn_finset (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    variance id ((uniformOn (s : Set α)).map f) =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i) ^ 2 := by
  let _ := isProbabilityMeasure_uniformOn s.finite_toSet hs
  have hL : MemLp (id : ℝ → ℝ) 2 ((uniformOn (s : Set α)).map f) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2
      (s.integrable_map_uniformOn_finset f (fun x : ℝ ↦ x ^ 2))
  rw [variance_eq_sub hL]
  simpa only [Pi.pow_apply, id_eq] using congrArg₂ (fun x y : ℝ ↦ x - y ^ 2)
    (s.integral_pow_map_uniformOn_finset f 2) (s.integral_id_map_uniformOn_finset f)

/-- All real exponential moments of a finitely labelled uniform law exist, even when the
sampling set is empty. -/
@[simp]
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
theorem pgf_id_map_uniformOn_finset (s : Finset α) (f : α → ℕ) (z : ℝ) :
    pgf id ((uniformOn (s : Set α)).map f) z =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, z ^ f i := by
  simpa only [pgf_def, id_eq, smul_eq_mul] using
    s.integral_map_uniformOn_finset f (fun k : ℕ ↦ z ^ k)

end Finset

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {P : Measure Ω} {s : Finset α}

/-- The expectation of any observable of a native finite uniform sample is its average over
the sampling set, without a global measurability assumption on the observable. -/
theorem integral_uniformOn_finset {X : Ω → α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hX : HasLaw X (uniformOn (s : Set α)) P) (g : α → E) :
    ∫ ω, g (X ω) ∂P = (s.card : ℝ)⁻¹ • ∑ i ∈ s, g i :=
  (hX.integral_comp (s.integrable_uniformOn_finset g).aestronglyMeasurable).trans
    (s.integral_uniformOn_finset g)

variable {X : Ω → ℝ} {f : α → ℝ}

/-- Every observable of a random variable with a finitely labelled uniform law is integrable. -/
theorem integrable_map_uniformOn_finset {E : Type*} [NormedAddCommGroup E]
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (g : ℝ → E) :
    Integrable (fun ω ↦ g (X ω)) P :=
  hX.integrable_comp (s.integrable_map_uniformOn_finset f g)

/-- Natural moments of a random variable with a finitely labelled uniform law are average
label powers. -/
theorem integral_pow_map_uniformOn_finset
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P = (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ n := by
  exact (hX.integral_comp
    (s.integrable_map_uniformOn_finset f (fun x : ℝ ↦ x ^ n)).aestronglyMeasurable).trans
      (s.integral_pow_map_uniformOn_finset f n)

/-- Variance of a random variable with a nonempty finitely labelled uniform law. -/
theorem variance_map_uniformOn_finset
    (hX : HasLaw X ((uniformOn (s : Set α)).map f) P) (hs : s.Nonempty) :
    variance X P =
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i ^ 2 - ((s.card : ℝ)⁻¹ * ∑ i ∈ s, f i) ^ 2 := by
  rw [hX.variance_eq]
  exact s.variance_id_map_uniformOn_finset hs f

end ProbabilityTheory.HasLaw
