/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Worked examples: partition entropy and Kolmogorov–Sinai entropy

These examples check the conventions of `TauCeti.countablePartitionEntropy`,
`TauCeti.conditionalPartitionEntropy`, `TauCeti.iteratedPartitionLabel` and
`TauCeti.measureEntropy`.

* A one-atom label has entropy `0`; a fair binary label has entropy `log 2`; the uniform
  probability on `Bool × Bool` with the identity label has entropy `2 log 2`.
* Independent fair binary labels have conditional entropy `log 2`, while conditioning a label on
  itself gives `0`. The zero measure gives entropy `0`.
* Iterating a binary label under the identity gives `(i, i, i)`; iterating the two-point flip
  from `false` gives `(false, true, false)`. The length-zero itinerary is the empty function.
* The identity has entropy `0`, and every map has entropy `0` under a Dirac probability or the
  zero measure.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.MeasureEntropyExamples

/-- The fair bit: the uniform probability on `Bool`. -/
noncomputable abbrev fairBit : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

theorem fairBit_real_singleton (b : Bool) : fairBit.real {b} = 1 / 2 := by
  simp [Measure.real]

instance instIsProbabilityMeasureFairBit : IsProbabilityMeasure fairBit :=
  ⟨by
    rw [smul_apply, Measure.count_univ]
    simp [ENNReal.inv_mul_cancel]⟩

/-- Two independent fair bits: the uniform probability on `Bool × Bool`. -/
noncomputable abbrev twoBits : Measure (Bool × Bool) := fairBit.prod fairBit

theorem twoBits_real_cell (i j : Bool) :
    twoBits.real (Prod.fst ⁻¹' {i} ∩ Prod.snd ⁻¹' {j}) = 1 / 4 := by
  rw [← Set.prod_eq, measureReal_prod_prod, fairBit_real_singleton,
    fairBit_real_singleton]
  norm_num

theorem twoBits_real_snd (j : Bool) : twoBits.real (Prod.snd ⁻¹' {j}) = 1 / 2 := by
  rw [show Prod.snd ⁻¹' {j} = (Set.univ : Set Bool) ×ˢ ({j} : Set Bool) by ext; simp,
    measureReal_prod_prod, fairBit_real_singleton, probReal_univ, one_mul]

/-- A fair binary label has entropy `log 2`. -/
example : countablePartitionEntropy fairBit id = ENNReal.ofReal (log 2) := by
  rw [countablePartitionEntropy_eq_ofReal_sum]
  simp only [Set.preimage_id, fairBit_real_singleton, Fintype.sum_bool, negMulLog, one_div,
    log_inv]
  congr 1
  ring

/-- The uniform probability on `Bool × Bool` with the identity label has entropy `2 log 2`. -/
example : countablePartitionEntropy twoBits id = ENNReal.ofReal (2 * log 2) := by
  rw [countablePartitionEntropy_eq_ofReal_sum]
  have h : ∀ p : Bool × Bool, twoBits.real (id ⁻¹' {p}) = 1 / 4 := fun ⟨i, j⟩ ↦ by
    rw [Set.preimage_id, ← twoBits_real_cell i j, ← Set.prod_eq,
      Set.singleton_prod_singleton]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    negMulLog, one_div, log_inv, nsmul_eq_mul]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  congr 1
  push_cast
  ring

/-- A one-atom label has entropy `0`, whatever empty atoms its alphabet carries. -/
example : countablePartitionEntropy fairBit (fun _ ↦ (7 : ℕ)) = 0 :=
  countablePartitionEntropy_const 7

/-- Independent fair binary labels have conditional entropy `log 2`. -/
example : conditionalPartitionEntropy twoBits Prod.fst Prod.snd = ENNReal.ofReal (log 2) := by
  rw [conditionalPartitionEntropy_def, tsum_fintype]
  simp only [twoBits_real_cell, twoBits_real_snd, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num
  ring

/-- Conditioning a label on itself gives `0`. -/
example : conditionalPartitionEntropy twoBits Prod.fst Prod.fst = 0 :=
  conditionalPartitionEntropy_self _ _

/-- The zero measure gives entropy `0`. -/
example : countablePartitionEntropy (0 : Measure Bool) id = 0 :=
  countablePartitionEntropy_zero_measure id

/-- Iterating a binary label under the identity repeats it. -/
example (x : Bool) : iteratedPartitionLabel id id 3 x = ![x, x, x] := by
  ext k
  fin_cases k <;> simp

/-- Iterating the two-point flip from `false` gives `(false, true, false)`. -/
example : iteratedPartitionLabel not id 3 false = ![false, true, false] := by
  ext k
  fin_cases k <;> simp

/-- The length-zero itinerary is the empty function. -/
example (T : Bool → Bool) (x : Bool) : iteratedPartitionLabel T id 0 x = Fin.elim0 := by
  simp

/-- The identity has entropy `0`. -/
example : measureEntropy fairBit id = 0 :=
  measureEntropy_id

/-- Every map has entropy `0` under a Dirac probability and under the zero measure. -/
example (T : Bool → Bool) :
    measureEntropy (Measure.dirac true) T = 0 ∧ measureEntropy (0 : Measure Bool) T = 0 :=
  ⟨measureEntropy_dirac true T, measureEntropy_zero_measure T⟩

end TauCeti.MeasureEntropyExamples
