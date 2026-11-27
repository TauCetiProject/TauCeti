/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.LabelEntropy
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Worked examples: entropy of finite labels

These examples check the conventions of `TauCeti.labelEntropy` and `TauCeti.condLabelEntropy`.

* A constant label has entropy `0`; a fair bit has entropy `log 2` (natural units, not the
  base-two value `1`); enlarging the alphabet by an unused value does not change the entropy.
* A label conditioned on itself has conditional entropy `0`, and `H((X, X)) = H(X)`.
* The order of the arguments of `condLabelEntropy` is fixed by an asymmetric joint law on
  `Bool × Bool` with masses `1/2` at `(false, false)`, `1/4` at `(true, false)` and `1/4` at
  `(true, true)`: conditioning the first coordinate on the second gives
  `(1/2) log (3/2) + (1/4) log 3`, conditioning the other way gives `(1/2) log 2`. The joint entropy
  is `H((X, Y)) = (3/2) log 2`, and the chain rule `H(Y) + H(X | Y) = H((X, Y))` confirms it.
-/

public section

open MeasureTheory Real TauCeti
open scoped ENNReal

namespace TauCeti.LabelEntropyExamples

/-- The fair bit: the uniform probability on `Bool`. -/
noncomputable abbrev fairBit : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

theorem fairBit_real_singleton (b : Bool) : fairBit.real {b} = 1 / 2 := by
  simp [Measure.real]

/-- A fair bit has entropy `log 2`, not its base-two value `1`. -/
example : labelEntropy fairBit id = log 2 := by
  simp only [labelEntropy_def, Set.preimage_id, fairBit_real_singleton, Fintype.sum_bool,
    negMulLog, one_div, log_inv]
  ring

/-- Enlarging the alphabet `Bool` to `Option Bool` by an unused value leaves the entropy
unchanged. -/
example : labelEntropy fairBit (some ∘ id) = log 2 := by
  rw [labelEntropy_comp_of_injective _ (Option.some_injective Bool)]
  simp only [labelEntropy_def, Set.preimage_id, fairBit_real_singleton, Fintype.sum_bool,
    negMulLog, one_div, log_inv]
  ring

/-- A constant label has entropy `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    labelEntropy μ (fun _ : Ω ↦ true) = 0 :=
  labelEntropy_const true

/-- A label conditioned on itself has entropy `0`, and `H((X, X)) = H(X)`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Bool) :
    condLabelEntropy μ X X = 0 ∧ labelEntropy μ (fun ω ↦ (X ω, X ω)) = labelEntropy μ X :=
  ⟨condLabelEntropy_self μ X, labelEntropy_pair_self μ X⟩

/-- The asymmetric joint law: masses `1/2` at `(false, false)`, `1/4` at `(true, false)`,
`1/4` at `(true, true)` and `0` at `(false, true)`. -/
noncomputable abbrev skewLaw : Measure (Bool × Bool) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (false, false) + (4 : ℝ≥0∞)⁻¹ • Measure.dirac (true, false) +
    (4 : ℝ≥0∞)⁻¹ • Measure.dirac (true, true)

open scoped Classical in
theorem skewLaw_real (s : Set (Bool × Bool)) :
    skewLaw.real s = (if (false, false) ∈ s then 1 / 2 else 0) +
      (if (true, false) ∈ s then 1 / 4 else 0) + (if (true, true) ∈ s then 1 / 4 else 0) := by
  simp only [Measure.real, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  split_ifs <;> simp [ENNReal.toReal_add, ENNReal.toReal_inv]

/-- Conditioning the first coordinate on the second gives `(1/2) log (3/2) + (1/4) log 3`. -/
example : condLabelEntropy skewLaw Prod.fst Prod.snd = 1 / 2 * log (3 / 2) + 1 / 4 * log 3 := by
  simp only [condLabelEntropy_def, Fintype.sum_bool, skewLaw_real]
  norm_num [Set.mem_preimage, Set.mem_inter_iff]
  ring

/-- Conditioning the second coordinate on the first gives `(1/2) log 2`. -/
example : condLabelEntropy skewLaw Prod.snd Prod.fst = 1 / 2 * log 2 := by
  simp only [condLabelEntropy_def, Fintype.sum_bool, skewLaw_real]
  norm_num [Set.mem_preimage, Set.mem_inter_iff]
  ring

/-- The joint entropy, computed directly from the cells: `H((X, Y)) = (3/2) log 2`. -/
theorem skewLaw_labelEntropy_pair :
    labelEntropy skewLaw (fun ω ↦ (ω.1, ω.2)) = 3 / 2 * log 2 := by
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]
  simp only [labelEntropy_pair, Fintype.sum_bool, skewLaw_real]
  norm_num [Set.mem_preimage, Set.mem_inter_iff, negMulLog]
  simp only [one_div, log_inv, h4]
  ring

/-- The chain rule checks the first conditional value against the joint entropy:
`H(Y) + H(X | Y) = H((X, Y)) = (3/2) log 2`. -/
example : labelEntropy skewLaw Prod.snd + condLabelEntropy skewLaw Prod.fst Prod.snd =
    3 / 2 * log 2 := by
  have : IsFiniteMeasure skewLaw := ⟨by simp [lt_top_iff_ne_top]⟩
  rw [← labelEntropy_pair_eq_add measurable_fst, ← skewLaw_labelEntropy_pair]

end TauCeti.LabelEntropyExamples
