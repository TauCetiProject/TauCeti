/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy.Conditional
public import TauCeti.MeasureTheory.MeasurableSpace.Sum
import TauCeti.InformationTheory.PartitionEntropy.Finite

/-!
# Restricting a finite label to a set

Restricting a finite label `a` to a set `F`, that is, keeping `a x` on `F` and lumping `Fᶜ` into
one extra atom, costs a conditional entropy of at most `μ Fᶜ * log (card ι)`. This is one of the
partition estimates behind Goodwyn's inequality `h_μ(T) ≤ h_top(T)`: for a weakly regular measure
every atom of `a` contains a closed set of nearly full measure
(`Measurable.exists_isClosed_measure_compl_iUnion_le`), so restricting `a` to the union of these
closed sets has arbitrarily small conditional entropy, while the atoms of the restriction other
than the lumped one are closed.

## Main results

* `TauCeti.restrictLabel a F`: the label equal to `a` on `F` and to `Sum.inr ()` off `F`, with
  atoms `TauCeti.preimage_restrictLabel_inl` and `TauCeti.preimage_restrictLabel_inr`.
* `TauCeti.conditionalPartitionEntropy_restrictLabel_le`:
  `H(a | restrictLabel a F) ≤ μ Fᶜ * log (card ι)`.

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

@[simp]
theorem restrictLabel_of_mem {a : X → ι} {F : Set X} {x : X} (hx : x ∈ F) :
    restrictLabel a F x = Sum.inl (a x) := by
  simp [restrictLabel, hx]

@[simp]
theorem restrictLabel_of_notMem {a : X → ι} {F : Set X} {x : X} (hx : x ∉ F) :
    restrictLabel a F x = Sum.inr () := by
  simp [restrictLabel, hx]

/-- The atom of `restrictLabel a F` with value `Sum.inl i` is `F ∩ a ⁻¹' {i}`. -/
@[simp]
theorem preimage_restrictLabel_inl (a : X → ι) (F : Set X) (i : ι) :
    restrictLabel a F ⁻¹' {Sum.inl i} = F ∩ a ⁻¹' {i} := by
  ext x
  by_cases hx : x ∈ F <;> simp [hx]

/-- The lumped atom of `restrictLabel a F` is `Fᶜ`. -/
@[simp]
theorem preimage_restrictLabel_inr (a : X → ι) (F : Set X) :
    restrictLabel a F ⁻¹' {Sum.inr ()} = Fᶜ := by
  ext x
  by_cases hx : x ∈ F <;> simp [hx]

/-- The restriction of a measurable label to a measurable set is measurable. -/
theorem measurable_restrictLabel [MeasurableSpace ι] {a : X → ι} (ha : Measurable a) {F : Set X}
    (hF : MeasurableSet F) : Measurable (restrictLabel a F) := by
  unfold restrictLabel
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

end TauCeti
