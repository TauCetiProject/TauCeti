/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Particle counts of finite labelled configurations

A labelled configuration of finitely many particles in `E` is a map `x : ι → E`. The count of
a window `B` is the number of labels whose particle lies in `B`, so coincident particles are
counted with multiplicity. Counts are sums of indicators, are additive on disjoint windows,
ignore relabelling, and turn powers into products of one-particle factors.

Counts are measurable for measurable windows. For a null-measurable window they are almost
everywhere measurable under any product of sigma-finite measures, so finite point processes
given by densities on labelled configurations need no measurable representative of a window.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

variable {ι E : Type*} [Fintype ι]

/-- The number of labelled particles in a window, counting multiplicity. -/
def particleCount (x : ι → E) (B : Set E) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ x i ∈ B).card

/-- The defining cardinality of the particles whose coordinates belong to a window. -/
theorem particleCount_def (x : ι → E) (B : Set E) [DecidablePred (· ∈ B)] :
    particleCount x B = (Finset.univ.filter fun i ↦ x i ∈ B).card := by
  rw [particleCount]
  congr

/-- A count is the sum over the particles of the indicator of the window. -/
theorem particleCount_eq_sum_indicator (x : ι → E) (B : Set E) :
    particleCount x B = ∑ i, B.indicator 1 (x i) := by
  classical
  simp [particleCount_def, Set.indicator_apply, Finset.sum_boole]

/-- A count never exceeds the number of particles. -/
theorem particleCount_le (x : ι → E) (B : Set E) : particleCount x B ≤ Fintype.card ι := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- Counting all particles gives their number, including the empty family. -/
@[simp]
theorem particleCount_univ (x : ι → E) : particleCount x Set.univ = Fintype.card ι := by
  simp [particleCount]

/-- The empty window contains no particle. -/
@[simp]
theorem particleCount_empty (x : ι → E) : particleCount x ∅ = 0 := by
  simp [particleCount]

/-- The empty configuration has no particle in any window. -/
@[simp]
theorem particleCount_of_isEmpty [IsEmpty ι] (x : ι → E) (B : Set E) :
    particleCount x B = 0 := by
  simp [particleCount_eq_sum_indicator]

/-- A gap means that every particle avoids the window. -/
@[simp]
theorem particleCount_eq_zero_iff (x : ι → E) (B : Set E) :
    particleCount x B = 0 ↔ ∀ i, x i ∉ B := by
  classical
  simp [particleCount, Finset.filter_eq_empty_iff]

/-- Counts do not depend on how the particles are labelled. -/
@[simp]
theorem particleCount_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → E)
    (B : Set E) : particleCount (x ∘ e) B = particleCount x B := by
  simp only [particleCount_eq_sum_indicator, Function.comp_apply]
  exact e.sum_comp fun i ↦ B.indicator 1 (x i)

/-- Counting the images of the particles in a window counts the particles in its preimage. -/
theorem particleCount_preimage {F : Type*} (f : E → F) (x : ι → E) (B : Set F) :
    particleCount (f ∘ x) B = particleCount x (f ⁻¹' B) := by
  simp only [particleCount_eq_sum_indicator, Function.comp_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (Set.indicator_comp_right (g := 1) _).symm

/-- Counts are additive on disjoint windows. -/
theorem particleCount_union (x : ι → E) {B C : Set E} (h : Disjoint B C) :
    particleCount x (B ∪ C) = particleCount x B + particleCount x C := by
  simp only [particleCount_eq_sum_indicator, Set.indicator_union_of_disjoint h,
    Finset.sum_add_distrib]

/-- Raising `z` to a particle count gives the product of the one-particle generating factors. -/
theorem pow_particleCount {M : Type*} [CommMonoid M] (x : ι → E) (B : Set E) (z : M) :
    z ^ particleCount x B = ∏ i, B.mulIndicator (fun _ ↦ z) (x i) := by
  classical
  simp [particleCount, Set.mulIndicator, Finset.prod_ite]

/-- A product of powers of window counts is the product over the particles of the products
of their one-window factors. The windows may overlap. -/
theorem prod_pow_particleCount {κ M : Type*} [Fintype κ] [CommMonoid M] (x : ι → E)
    (B : κ → Set E) (z : κ → M) :
    ∏ k, z k ^ particleCount x (B k) = ∏ i, ∏ k, (B k).mulIndicator (fun _ ↦ z k) (x i) := by
  simp_rw [pow_particleCount]
  exact Finset.prod_comm

section Measurable

variable [MeasurableSpace E]

/-- Particle counts are measurable for measurable windows. -/
theorem measurable_particleCount {B : Set E} (hB : MeasurableSet B) :
    Measurable (fun x : ι → E ↦ particleCount x B) := by
  simp_rw [particleCount_eq_sum_indicator]
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_one.indicator hB).comp (measurable_pi_apply i)

/-- Particle counts are almost everywhere measurable for null-measurable windows, for every
product of a sigma-finite reference measure. -/
theorem aemeasurable_particleCount {μ : Measure E} [SigmaFinite μ] {B : Set E}
    (hB : NullMeasurableSet B μ) :
    AEMeasurable (fun x : ι → E ↦ particleCount x B) (Measure.pi fun _ ↦ μ) := by
  simp_rw [particleCount_eq_sum_indicator]
  exact Finset.aemeasurable_fun_sum _ fun i _ ↦
    (aemeasurable_one.indicator₀ hB).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval _ i)

end Measurable

end TauCeti
