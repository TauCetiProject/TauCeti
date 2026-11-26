/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Worked example: dyadic truncations of the identity of `[0, 1]`

On `[0, 1]` with Lebesgue measure, the label `x ↦ x` has uncountably many values and is not a
countable partition. Every one of its atoms is a point, of mass zero, so the countable-partition
formula applied to it would give `0`. Its dyadic truncations `x ↦ ⌊2 ^ k * x⌋₊` are admissible
labels into `ℕ`: the `2 ^ k` atoms `[j / 2 ^ k, (j + 1) / 2 ^ k)` have mass `2⁻¹ ^ k` (and the
atom `{1}` of label `2 ^ k` is null), so the truncation at level `k` has entropy `k log 2`, which
tends to `⊤`.
-/

public section

open MeasureTheory Real Filter Topology Set
open scoped ENNReal

namespace TauCeti.DyadicEntropyExamples

/-- Lebesgue measure on `[0, 1]`. -/
noncomputable abbrev unitLebesgue : Measure ℝ := volume.restrict (Icc 0 1)

/-- The dyadic truncation at level `k`: the index `⌊2 ^ k * x⌋₊` of the dyadic interval of length
`2⁻¹ ^ k` containing `x`. -/
noncomputable def dyadicLabel (k : ℕ) (x : ℝ) : ℕ := ⌊2 ^ k * x⌋₊

/-- The dyadic truncation is measurable. -/
theorem measurable_dyadicLabel (k : ℕ) : Measurable (dyadicLabel k) :=
  Measurable.nat_floor (f := fun x : ℝ ↦ 2 ^ k * x) (by fun_prop)

/-- The atom of the dyadic truncation with index `j < 2 ^ k` has mass `2⁻¹ ^ k`, and the other
atoms are null. -/
theorem measureReal_dyadicLabel_preimage (k j : ℕ) :
    unitLebesgue.real (dyadicLabel k ⁻¹' {j}) = if j < 2 ^ k then 2⁻¹ ^ k else 0 := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rw [measureReal_restrict_apply (measurable_dyadicLabel k (measurableSet_singleton j))]
  split_ifs with hj
  · have hset : dyadicLabel k ⁻¹' {j} ∩ Icc 0 1 = Ico ((j : ℝ) / 2 ^ k) ((j + 1) / 2 ^ k) := by
      have hj' : (j : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast hj
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Icc, mem_Ico, dyadicLabel,
        div_le_iff₀ h2, lt_div_iff₀ h2]
      constructor
      · rintro ⟨hfl, hx0, -⟩
        rw [Nat.floor_eq_iff (by positivity)] at hfl
        constructor <;> linarith
      · rintro ⟨hlo, hhi⟩
        have hx0 : 0 ≤ x := by
          by_contra! hneg
          nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        refine ⟨(Nat.floor_eq_iff (by positivity)).mpr ⟨by linarith, by linarith⟩, hx0, ?_⟩
        nlinarith
    rw [hset, Real.volume_real_Ico_of_le (by gcongr; linarith), ← sub_div, add_sub_cancel_left,
      one_div, inv_pow]
  · have hsub : dyadicLabel k ⁻¹' {j} ∩ Icc 0 1 ⊆ {1} := fun x ⟨hfl, hx0, hx1⟩ ↦ by
      simp only [mem_preimage, mem_singleton_iff, dyadicLabel] at hfl
      have hle : (2 : ℝ) ^ k ≤ 2 ^ k * x := by
        have := Nat.floor_le (a := 2 ^ k * x) (by positivity)
        rw [hfl] at this
        exact le_trans (by exact_mod_cast not_lt.mp hj) this
      exact mem_singleton_iff.mpr (le_antisymm hx1 (by nlinarith))
    rw [Measure.real, measure_mono_null hsub (measure_singleton 1), ENNReal.toReal_zero]

/-- **Dyadic truncations.** The truncation at level `k` has entropy `k log 2`. -/
theorem countablePartitionEntropy_dyadicLabel (k : ℕ) :
    countablePartitionEntropy unitLebesgue (dyadicLabel k) = ENNReal.ofReal (k * log 2) := by
  rw [countablePartitionEntropy_def, tsum_eq_sum (s := Finset.range (2 ^ k)) fun j hj ↦ by
    rw [measureReal_dyadicLabel_preimage]
    simp [Finset.mem_range.not.mp hj]]
  rw [Finset.sum_congr rfl (g := fun _ ↦ ENNReal.ofReal (negMulLog (2⁻¹ ^ k))) fun j hj ↦ by
    simp only [measureReal_dyadicLabel_preimage, Finset.mem_range.mp hj, ite_true]]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [negMulLog_def, log_pow, log_inv, inv_pow]
  push_cast
  field_simp

/-- The entropies of the dyadic truncations tend to `⊤`. -/
theorem tendsto_countablePartitionEntropy_dyadicLabel :
    Tendsto (fun k ↦ countablePartitionEntropy unitLebesgue (dyadicLabel k)) atTop (𝓝 ∞) := by
  simp only [countablePartitionEntropy_dyadicLabel]
  exact ENNReal.tendsto_ofReal_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const (log_pos one_lt_two))

/-- The countable-partition formula applied to the label `x ↦ x`, whose atoms are points, gives
`0`: the label is not a countable partition, and its entropy is not this value. -/
example : countablePartitionEntropy unitLebesgue id = 0 := by
  rw [countablePartitionEntropy_def]
  refine tsum_eq_zero_iff.mpr fun i ↦ ?_
  have h0 : unitLebesgue {i} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans_eq (measure_singleton i)) bot_le
  simp [Measure.real, h0]

end TauCeti.DyadicEntropyExamples
