/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy.Conditional
public import TauCeti.MeasureTheory.MeasurableSpace.Sum
public import Mathlib.MeasureTheory.Measure.Regular
import TauCeti.InformationTheory.PartitionEntropy.Finite

/-!
# Approximating finite partitions by closed partitions

These are the partition estimates behind Goodwyn's inequality `h_μ(T) ≤ h_top(T)`. Restricting a
finite label `a` to a set `F`, that is, keeping `a x` on `F` and lumping `Fᶜ` into one extra atom,
costs a conditional entropy of at most `μ Fᶜ * log (card ι)`. For a weakly regular measure on a
topological space, every atom of a finite measurable label contains a closed set of nearly full
measure, so the restriction to the union of these closed sets has arbitrarily small conditional
entropy, while its atoms other than the lumped one are closed.

## Main results

* `TauCeti.restrictLabel a F`: the label equal to `a` on `F` and to `Sum.inr ()` off `F`, with
  atoms `TauCeti.preimage_restrictLabel_inl` and `TauCeti.preimage_restrictLabel_inr`.
* `TauCeti.conditionalPartitionEntropy_restrictLabel_le`:
  `H(a | restrictLabel a F) ≤ μ Fᶜ * log (card ι)`.
* `TauCeti.exists_isClosed_measure_compl_iUnion_le`: for a weakly regular finite measure, closed
  sets `F i ⊆ a ⁻¹' {i}` with `μ (⋃ i, F i)ᶜ ≤ δ`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, §4.6.3, pp. 122–123.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The restriction of the label `a` to the set `F`: equal to `Sum.inl (a x)` on `F` and to
`Sum.inr ()` off `F`, so that `Fᶜ` becomes a single atom. -/
noncomputable def restrictLabel (a : X → ι) (F : Set X) : X → ι ⊕ Unit :=
  open Classical in fun x ↦ if x ∈ F then Sum.inl (a x) else Sum.inr ()

theorem restrictLabel_of_mem {a : X → ι} {F : Set X} {x : X} (hx : x ∈ F) :
    restrictLabel a F x = Sum.inl (a x) := by
  simp [restrictLabel, hx]

theorem restrictLabel_of_notMem {a : X → ι} {F : Set X} {x : X} (hx : x ∉ F) :
    restrictLabel a F x = Sum.inr () := by
  simp [restrictLabel, hx]

/-- The atom of `restrictLabel a F` with value `Sum.inl i` is `F ∩ a ⁻¹' {i}`. -/
@[simp]
theorem preimage_restrictLabel_inl (a : X → ι) (F : Set X) (i : ι) :
    restrictLabel a F ⁻¹' {Sum.inl i} = F ∩ a ⁻¹' {i} := by
  ext x
  by_cases hx : x ∈ F <;> simp [restrictLabel_of_mem, restrictLabel_of_notMem, hx]

/-- The lumped atom of `restrictLabel a F` is `Fᶜ`. -/
@[simp]
theorem preimage_restrictLabel_inr (a : X → ι) (F : Set X) :
    restrictLabel a F ⁻¹' {Sum.inr ()} = Fᶜ := by
  ext x
  by_cases hx : x ∈ F <;> simp [restrictLabel_of_mem, restrictLabel_of_notMem, hx]

/-- The restriction of a measurable label to a measurable set is measurable. -/
theorem measurable_restrictLabel [MeasurableSpace ι] {a : X → ι} (ha : Measurable a) {F : Set X}
    (hF : MeasurableSet F) : Measurable (restrictLabel a F) := by
  classical
  exact Measurable.ite hF (measurable_inl.comp ha) measurable_const

/-- **Cost of restricting a label.** For every measure, a measurable label `a` into a finite type
and a measurable set `F`, `H(a | restrictLabel a F) ≤ μ Fᶜ * log (card ι)`: on the
atoms inside `F` the label `a` is constant. -/
theorem conditionalPartitionEntropy_restrictLabel_le [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a : X → ι} (ha : Measurable a) {F : Set X}
    (hF : MeasurableSet F) :
    conditionalPartitionEntropy μ a (restrictLabel a F) ≤
      μ Fᶜ * ENNReal.ofReal (Real.log (Fintype.card ι)) := by
  have hb := measurable_restrictLabel ha hF
  rw [conditionalPartitionEntropy_eq_tsum_cond _ hb, tsum_fintype, Fintype.sum_sum_type]
  -- On an atom inside `F` the label `a` is constant.
  have hin (i : ι) : countablePartitionEntropy μ[|restrictLabel a F ⁻¹' {Sum.inl i}] a = 0 := by
    have hS := hb (measurableSet_singleton (Sum.inl i))
    rw [countablePartitionEntropy_congr_ae (a' := fun _ ↦ i), countablePartitionEntropy_const]
    filter_upwards [ae_cond_mem hS] with x hx
    exact ((preimage_restrictLabel_inl a F i).subset hx).2
  simp only [hin, mul_zero, Finset.sum_const_zero, zero_add, Finset.univ_unique,
    Finset.sum_singleton, PUnit.default_eq_unit, preimage_restrictLabel_inr]
  gcongr
  simpa using countablePartitionEntropy_le_ofReal_log_card (μ := μ[|Fᶜ]) ha Finset.univ
    fun x ↦ Finset.mem_univ (a x)

/-- **Closed approximation.** For a weakly regular finite measure on a topological space with
measurable open sets and a measurable label `a` into a finite type, every `δ > 0` admits closed
sets `F i ⊆ a ⁻¹' {i}` whose union misses a set of measure at most `δ`. -/
theorem exists_isClosed_measure_compl_iUnion_le [TopologicalSpace X] [OpensMeasurableSpace X]
    [IsFiniteMeasure μ] [μ.WeaklyRegular] [Finite ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a : X → ι} (ha : Measurable a) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ F : ι → Set X, (∀ i, IsClosed (F i)) ∧ (∀ i, F i ⊆ a ⁻¹' {i}) ∧
      μ (⋃ i, F i)ᶜ ≤ δ := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ ↦ ∅, fun _ ↦ isClosed_empty, fun _ ↦ empty_subset _, ?_⟩
    have : IsEmpty X := ⟨fun x ↦ hι.false (a x)⟩
    simp [Set.univ_eq_empty_iff.2 this]
  have hcard : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp
  have hε : δ / Fintype.card ι ≠ 0 := ENNReal.div_ne_zero.2 ⟨hδ, by simp⟩
  choose F hFsub hFc hF using fun i : ι ↦
    (ha (measurableSet_singleton i)).exists_isClosed_sdiff_lt (measure_ne_top μ _) hε
  refine ⟨F, hFc, hFsub, ?_⟩
  have hcover : (⋃ i, F i)ᶜ ⊆ ⋃ i, a ⁻¹' {i} \ F i := fun x hx ↦
    mem_iUnion.2 ⟨a x, rfl, fun h ↦ hx (mem_iUnion.2 ⟨a x, h⟩)⟩
  calc μ (⋃ i, F i)ᶜ ≤ ∑ i, μ (a ⁻¹' {i} \ F i) :=
        (measure_mono hcover).trans (measure_iUnion_fintype_le μ _)
    _ ≤ ∑ _i : ι, δ / Fintype.card ι := Finset.sum_le_sum fun i _ ↦ (hF i).le
    _ = δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.mul_div_cancel hcard (ENNReal.natCast_ne_top _)]

end TauCeti
