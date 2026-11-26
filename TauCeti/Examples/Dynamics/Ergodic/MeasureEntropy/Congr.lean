/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Congr
public import TauCeti.InformationTheory.PartitionEntropy.Finite
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Worked examples: almost-everywhere equal labels and relabeling into `ℕ`

* A constant label on a one-point probability space, with an empty atom added to its alphabet
  `Bool`, has entropy `0`, and so does its composite with an injection into `ℕ`; the empty
  itinerary has entropy `0`. Alphabet size alone would give `log 2`.
* On `[0, 1]` with Lebesgue measure, the labels of `[0, 1/2)` and `[0, 1/2]` differ only at
  `1/2`. Both have entropy `log 2`, and their join has entropy `log 2`, the entropy of a fair bit
  joined with itself, not the `2 log 2` of two independent fair bits.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.MeasureEntropyCongrExamples

/-- A constant label into `Bool` on a one-point space has entropy `0`, even with an empty atom. -/
example : countablePartitionEntropy (Measure.dirac ()) (fun _ : Unit ↦ true) = 0 :=
  countablePartitionEntropy_const true

/-- Its composite with an injection `Bool → ℕ` also has entropy `0`. -/
example : countablePartitionEntropy (Measure.dirac ())
    ((fun b : Bool ↦ b.toNat) ∘ fun _ : Unit ↦ true) = 0 := by
  rw [countablePartitionEntropy_comp_of_injective _ fun x y h ↦ by
    cases x <;> cases y <;> simp_all]
  exact countablePartitionEntropy_const true

/-- The empty itinerary has entropy `0`. -/
example : countablePartitionEntropy (Measure.dirac ())
    (iteratedPartitionLabel id (fun _ : Unit ↦ true) 0) = 0 := by
  rw [iteratedPartitionLabel_zero]
  exact countablePartitionEntropy_const Fin.elim0

/-- Lebesgue measure on `[0, 1]`. -/
noncomputable abbrev unitLebesgue : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance instIsProbabilityMeasureUnitLebesgue : IsProbabilityMeasure unitLebesgue :=
  ⟨by simp⟩

/-- The label of `[0, 1/2)`. -/
noncomputable def leftOpen (x : ℝ) : Bool := decide (x < 1 / 2)

/-- The label of `[0, 1/2]`. -/
noncomputable def leftClosed (x : ℝ) : Bool := decide (x ≤ 1 / 2)

/-- The two labels agree away from `1/2`, hence almost everywhere. -/
theorem leftOpen_ae_eq_leftClosed : leftOpen =ᵐ[unitLebesgue] leftClosed := by
  have h : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 / 2 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae h] with x hx
  simp only [leftOpen, leftClosed, decide_eq_decide]
  exact ⟨le_of_lt, fun h' ↦ lt_of_le_of_ne h' hx⟩

/-- The two labels have the same entropy. -/
example : countablePartitionEntropy unitLebesgue leftOpen =
    countablePartitionEntropy unitLebesgue leftClosed :=
  countablePartitionEntropy_congr_ae leftOpen_ae_eq_leftClosed

/-- The label of `[0, 1/2)` has entropy `log 2`. -/
theorem countablePartitionEntropy_leftOpen :
    countablePartitionEntropy unitLebesgue leftOpen = ENNReal.ofReal (log 2) := by
  have h : ∀ b, unitLebesgue.real (leftOpen ⁻¹' {b}) = 1 / 2 := by
    have hl : Measurable leftOpen := measurable_to_bool (by
      rw [show leftOpen ⁻¹' {true} = Set.Iio (1 / 2) by ext x; grind [leftOpen]]
      exact measurableSet_Iio)
    have hm : ∀ b, MeasurableSet (leftOpen ⁻¹' {b}) := fun b ↦ hl (measurableSet_singleton b)
    intro b
    rw [measureReal_restrict_apply (hm b)]
    cases b
    · rw [show leftOpen ⁻¹' {false} ∩ Set.Icc 0 1 = Set.Icc (1 / 2) 1 by
        ext x; grind [leftOpen]]
      norm_num
    · rw [show leftOpen ⁻¹' {true} ∩ Set.Icc 0 1 = Set.Ico 0 (1 / 2) by
        ext x; grind [leftOpen]]
      simp
  rw [countablePartitionEntropy_eq_ofReal_labelEntropy, labelEntropy_def]
  simp only [h, Fintype.sum_bool, negMulLog, one_div, log_inv]
  congr 1
  ring

/-- Their join has entropy `log 2`: it is almost everywhere the label joined with itself. -/
example : countablePartitionEntropy unitLebesgue (fun x ↦ (leftOpen x, leftClosed x)) =
    ENNReal.ofReal (log 2) := by
  rw [← countablePartitionEntropy_pair_congr_ae (Filter.EventuallyEq.refl _ leftOpen)
    leftOpen_ae_eq_leftClosed, countablePartitionEntropy_pair_self,
    countablePartitionEntropy_leftOpen]

end TauCeti.MeasureEntropyCongrExamples
