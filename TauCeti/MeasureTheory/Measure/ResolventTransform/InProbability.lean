/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.WeakConvergence
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.ConvergenceInMeasure

/-!
# Weak convergence in probability from resolvent transforms

Random probability measures on the real line converge weakly in probability to a deterministic
law exactly when their resolvent transforms converge in probability at each point of the upper
half-plane. A countable dense subset of that half-plane suffices. The sample spaces may vary
with the index; no joint realization or independence across sizes is needed.

The proof identifies the weak topology with the topology induced by the resolvent tests on a
countable determining set. Each weak neighborhood therefore contains a neighborhood specified
by finitely many resolvent tests. A finite union bound transfers convergence in probability.
This also identifies the criterion with convergence in probability of every real bounded
continuous test integral, rather than convergence of the expected random measure.

## Main results

* `MeasureTheory.ProbabilityMeasure.isEmbedding_resolventTransform`: resolvent transforms on a
  countable dense subset of the upper half-plane embed the space of probability measures.
* `MeasureTheory.ProbabilityMeasure.tendsto_measure_notMem_nhds_iff_resolventTransform`:
  the neighborhood criterion, allowing varying measure spaces and arbitrary filters.
* `MeasureTheory.ProbabilityMeasure.tendsto_measure_integral_iff_resolventTransform`:
  the equivalence with bounded continuous test integrals on varying spaces.
* `ProbabilityMeasure.forall_tendstoInMeasure_integral_iff_resolventTransform`:
  the same equivalence in Mathlib's `TendstoInMeasure` on a fixed space.

The statements use outer measures, so no measurability assumptions on the random measures
are necessary. They apply in particular to measurable empirical spectral measures. The limit
must be a probability measure: convergence of transforms to zero can describe mass escaping
to infinity and does not imply weak convergence to a probability law.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.4.3.
-/

public section

open Filter Set Topology
open scoped Topology BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

/-- Weak convergence in probability to `μ`, expressed by its neighborhoods, is equivalent
to convergence in probability of the transforms on any determining set of nonreal
points whose closure contains the upper half-plane. Measures, sample spaces and the convergence
filter are unrestricted. -/
theorem tendsto_measure_notMem_nhds_iff_resolventTransform_of_subset_closure
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure ℝ)
    (l : Filter ι) (μ : ProbabilityMeasure ℝ) {D : Set ℂ}
    (hDim : ∀ z ∈ D, z.im ≠ 0)
    (hD : {z : ℂ | 0 < z.im} ⊆ closure D) :
    (∀ U ∈ 𝓝 μ, Tendsto (fun i ↦ P i {ω | μs i ω ∉ U}) l (𝓝 0)) ↔
      ∀ z ∈ D, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
        ε ≤ ‖resolventTransform (μs i ω : Measure ℝ) z -
          resolventTransform (μ : Measure ℝ) z‖}) l (𝓝 0) := by
  simpa only [Subtype.forall, dist_eq_norm] using
    (isEmbedding_resolventTransform hDim hD).isInducing.tendsto_measure_notMem_nhds_iff
      P μs l μ

/-- Bounded continuous test integrals converge in probability to those of `μ` if and only
if resolvent transforms converge in probability on a determining set of nonreal points. This
includes random measures on different sample spaces at each size and arbitrary filters. -/
theorem tendsto_measure_integral_iff_resolventTransform_of_subset_closure
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure ℝ)
    (l : Filter ι) (μ : ProbabilityMeasure ℝ) {D : Set ℂ}
    (hDim : ∀ z ∈ D, z.im ≠ 0)
    (hD : {z : ℂ | 0 < z.im} ⊆ closure D) :
    (∀ f : ℝ →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
      ε ≤ |(∫ x, f x ∂(μs i ω : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ)|}) l (𝓝 0)) ↔
      ∀ z ∈ D, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
        ε ≤ ‖resolventTransform (μs i ω : Measure ℝ) z -
          resolventTransform (μ : Measure ℝ) z‖}) l (𝓝 0) := by
  exact (tendsto_measure_notMem_nhds_iff_integral P μs l μ).symm.trans
    (tendsto_measure_notMem_nhds_iff_resolventTransform_of_subset_closure P μs l μ hDim hD)

/-- On a fixed measure space, weak convergence in probability tested by bounded continuous
real functions is equivalent to convergence in measure of the resolvent transforms on a
determining set of nonreal points whose closure contains the upper half-plane. -/
theorem forall_tendstoInMeasure_integral_iff_resolventTransform_of_subset_closure
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μs : ι → Ω → ProbabilityMeasure ℝ) (l : Filter ι) (μ : ProbabilityMeasure ℝ)
    {D : Set ℂ} (hDim : ∀ z ∈ D, z.im ≠ 0)
    (hD : {z : ℂ | 0 < z.im} ⊆ closure D) :
    (∀ f : ℝ →ᵇ ℝ, TendstoInMeasure P (fun i ω ↦ ∫ x, f x ∂(μs i ω : Measure ℝ)) l
      (fun _ ↦ ∫ x, f x ∂(μ : Measure ℝ))) ↔
      ∀ z ∈ D, TendstoInMeasure P (fun i ω ↦ resolventTransform (μs i ω : Measure ℝ) z) l
        (fun _ ↦ resolventTransform (μ : Measure ℝ) z) := by
  simp_rw [tendstoInMeasure_iff_norm, Real.norm_eq_abs]
  exact tendsto_measure_integral_iff_resolventTransform_of_subset_closure
    (fun _ ↦ P) μs l μ hDim hD

/-- Weak convergence in probability to `μ`, expressed by its neighborhoods, is equivalent
to convergence in probability of the resolvent transforms at each upper-half-plane point.
The sample spaces may vary with the index. -/
theorem tendsto_measure_notMem_nhds_iff_resolventTransform
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure ℝ)
    (l : Filter ι) (μ : ProbabilityMeasure ℝ) :
    (∀ U ∈ 𝓝 μ, Tendsto (fun i ↦ P i {ω | μs i ω ∉ U}) l (𝓝 0)) ↔
      ∀ z : ℂ, 0 < z.im → ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
        ε ≤ ‖resolventTransform (μs i ω : Measure ℝ) z -
          resolventTransform (μ : Measure ℝ) z‖}) l (𝓝 0) := by
  simpa only [Subtype.forall, mem_ofPred_eq, dist_eq_norm] using
    (isEmbedding_resolventTransform (D := {z : ℂ | 0 < z.im})
      (fun _ hz ↦ hz.ne') subset_closure).isInducing.tendsto_measure_notMem_nhds_iff
      P μs l μ

/-- Random real probability measures converge weakly in probability, tested against every
real bounded continuous function, if and only if their resolvent transforms converge in
probability at each point of the upper half-plane. The sample spaces may vary. -/
theorem tendsto_measure_integral_iff_resolventTransform
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure ℝ)
    (l : Filter ι) (μ : ProbabilityMeasure ℝ) :
    (∀ f : ℝ →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
      ε ≤ |(∫ x, f x ∂(μs i ω : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ)|}) l (𝓝 0)) ↔
      ∀ z : ℂ, 0 < z.im → ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
        ε ≤ ‖resolventTransform (μs i ω : Measure ℝ) z -
          resolventTransform (μ : Measure ℝ) z‖}) l (𝓝 0) := by
  exact (tendsto_measure_notMem_nhds_iff_integral P μs l μ).symm.trans
    (tendsto_measure_notMem_nhds_iff_resolventTransform P μs l μ)

/-- On a fixed space, convergence in measure of all bounded continuous test integrals is
equivalent to convergence in measure of every upper-half-plane resolvent transform. -/
theorem forall_tendstoInMeasure_integral_iff_resolventTransform
    {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μs : ι → Ω → ProbabilityMeasure ℝ) (l : Filter ι) (μ : ProbabilityMeasure ℝ) :
    (∀ f : ℝ →ᵇ ℝ, TendstoInMeasure P (fun i ω ↦ ∫ x, f x ∂(μs i ω : Measure ℝ)) l
      (fun _ ↦ ∫ x, f x ∂(μ : Measure ℝ))) ↔
      ∀ z : ℂ, 0 < z.im →
        TendstoInMeasure P (fun i ω ↦ resolventTransform (μs i ω : Measure ℝ) z) l
          (fun _ ↦ resolventTransform (μ : Measure ℝ) z) := by
  simp_rw [tendstoInMeasure_iff_norm, Real.norm_eq_abs]
  exact tendsto_measure_integral_iff_resolventTransform (fun _ ↦ P) μs l μ

end MeasureTheory.ProbabilityMeasure
