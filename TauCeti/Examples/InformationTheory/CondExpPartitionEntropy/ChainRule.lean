/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy.ChainRule
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Worked examples: the conditional chain rule

These examples check `TauCeti.condExpPartitionEntropy_pair` on two fair bits.

* For two independent fair bits `P` and `Q` (the coordinates of the uniform probability on
  `Bool × Bool`), `H(P ∨ Q) = 2 log 2`, `H(P) = log 2`, and the chain rule gives
  `H(Q | σ(P)) = log 2`: knowing `P` says nothing about `Q`.
* For a fair bit `P` joined with itself, `H(P ∨ P) = log 2`, not the `2 log 2` of two independent
  fair bits, and `H(P | σ(P)) = 0`.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.CondExpPartitionEntropyChainRuleExamples

/-- Two independent fair bits: the uniform probability on `Bool × Bool`. -/
noncomputable abbrev twoBits : Measure (Bool × Bool) := (4 : ℝ≥0∞)⁻¹ • Measure.count

instance instIsProbabilityMeasureTwoBits : IsProbabilityMeasure twoBits :=
  ⟨by
    rw [smul_apply, Measure.count_univ]
    simp [ENNReal.inv_mul_cancel]⟩

/-- The fair bit: the uniform probability on `Bool`. -/
noncomputable abbrev fairBit : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance instIsProbabilityMeasureFairBit : IsProbabilityMeasure fairBit :=
  ⟨by
    rw [smul_apply, Measure.count_univ]
    simp [ENNReal.inv_mul_cancel]⟩

/-- Every atom of a label on a finite discrete space is measurable. -/
theorem measurableSet_preimage {α β : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (f : α → β) (i : β) : MeasurableSet (f ⁻¹' {i}) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- The joint entropy of two independent fair bits is `2 log 2`. -/
theorem condExpPartitionEntropy_bot_pair :
    condExpPartitionEntropy twoBits ⊥ (fun x ↦ (x.1, x.2)) = 2 * log 2 := by
  rw [condExpPartitionEntropy_bot fun i ↦ (measurableSet_preimage _ i).nullMeasurableSet]
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  simpa [measureReal_def, negMulLog] using h4

/-- Each value of the first coordinate has two preimages in `Bool × Bool`. -/
theorem count_fst_preimage (b : Bool) :
    Measure.count (Prod.fst ⁻¹' {b} : Set (Bool × Bool)) = 2 := by
  have : (Prod.fst ⁻¹' {b} : Set (Bool × Bool)) = ↑({(b, false), (b, true)} : Finset _) := by
    ext ⟨x, y⟩
    cases x <;> cases y <;> cases b <;> simp
  rw [this, Measure.count_apply_finset]
  simp

/-- The entropy of the first of two independent fair bits is `log 2`. -/
theorem condExpPartitionEntropy_bot_fst :
    condExpPartitionEntropy twoBits ⊥ Prod.fst = log 2 := by
  rw [condExpPartitionEntropy_bot fun i ↦ (measurableSet_preimage _ i).nullMeasurableSet]
  simp only [measureReal_def, smul_apply, count_fst_preimage, Fintype.sum_bool, negMulLog,
    smul_eq_mul]
  norm_num [Real.log_div one_ne_zero two_ne_zero]
  linarith

/-- By the chain rule, the second of two independent fair bits keeps entropy `log 2` given the
first: `H(Q | σ(P)) = H(P ∨ Q) - H(P) = 2 log 2 - log 2`. -/
example : condExpPartitionEntropy twoBits (⊥ ⊔ MeasurableSpace.comap Prod.fst ⊤) Prod.snd =
    log 2 := by
  have h := condExpPartitionEntropy_pair (μ := twoBits) (m := ⊥)
    (measurableSet_preimage Prod.fst) (measurableSet_preimage Prod.snd)
  rw [condExpPartitionEntropy_bot_pair, condExpPartitionEntropy_bot_fst] at h
  linarith

/-- A fair bit joined with itself has entropy `log 2`, not `2 log 2`. -/
example : condExpPartitionEntropy fairBit ⊥ (fun x ↦ (x, x)) = log 2 := by
  change condExpPartitionEntropy fairBit ⊥ (fun x ↦ (id x, id x)) = log 2
  rw [condExpPartitionEntropy_pair_self (a := id) (measurableSet_preimage id),
    condExpPartitionEntropy_bot fun i ↦ (measurableSet_preimage id i).nullMeasurableSet]
  simp [measureReal_def, negMulLog]

end TauCeti.CondExpPartitionEntropyChainRuleExamples
