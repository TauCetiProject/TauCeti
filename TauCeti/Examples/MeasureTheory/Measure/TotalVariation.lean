/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Measure.TotalVariation.Countable
import TauCeti.MeasureTheory.Measure.TotalVariation.Map
public import Mathlib.Probability.UniformOn

/-!
# Worked examples: event excess and total variation distance

The *excess* of a measure `μ` over a measure `ν` is the largest event difference
`⨆ (A) (_ : MeasurableSet A), μ A - ν A`, truncated in `ℝ≥0∞`. These examples evaluate it, and
Mathlib's total variation distance `etvDist`, in small cases, using the general results of
`TauCeti.MeasureTheory.Measure.TotalVariation`:

* pushing two measures forward along a constant map leaves exactly the excess `μ univ - ν univ`
  of the whole space, which is at most the excess of `μ` over `ν`;
* on `Bool`, the point mass at `true` exceeds the uniform law by `1/2`. The sum of the truncated
  singleton differences is `1/2 + 0`, the event `{true}` where the point mass is larger attains
  it, and `etvDist` is `1`, twice the excess;
* `etvDist μ μ` and the excess of `μ` over itself vanish, while two point masses at distinct
  points have excess `1` and `etvDist` equal to `2`, the largest value for probability measures.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Examples.TotalVariation

/-! ### Constant pushforwards -/

-- Pushing two measures forward along a constant map leaves the excess `μ univ - ν univ` of the
-- whole space, which is at most the excess of `μ` over `ν`, as for every measurable pushforward.
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ ν : Measure α) (b : β) :
    (⨆ (B : Set β) (_ : MeasurableSet B),
      μ.map (fun _ => b) B - ν.map (fun _ => b) B) = μ Set.univ - ν Set.univ := by
  simp only [Measure.map_const, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine le_antisymm (iSup₂_le fun B hB => ?_) ?_
  · by_cases hb : b ∈ B <;> simp [Measure.dirac_apply' _ hB, hb]
  · simpa using le_iSup₂ (f := fun (B : Set β) (_ : MeasurableSet B) =>
      μ Set.univ * Measure.dirac b B - ν Set.univ * Measure.dirac b B) Set.univ .univ

example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ ν : Measure α) (b : β) :
    (⨆ (B : Set β) (_ : MeasurableSet B), μ.map (fun _ => b) B - ν.map (fun _ => b) B) ≤
      ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A :=
  iSup_measure_map_sub_le μ ν measurable_const

/-! ### A point mass against the uniform law on `Bool` -/

/-- The uniform law on `Bool` gives each point mass `1/2`. -/
theorem uniformOn_univ_bool_singleton (b : Bool) :
    uniformOn (Set.univ : Set Bool) {b} = 2⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton]
  simp

-- The sum of the truncated singleton differences is `(1 - 1/2) + (0 - 1/2) = 1/2 + 0`.
example :
    ∑ y : Bool, (Measure.dirac true {y} - uniformOn (Set.univ : Set Bool) {y}) = 1 / 2 := by
  rw [Fintype.sum_bool, uniformOn_univ_bool_singleton, uniformOn_univ_bool_singleton]
  simp [ENNReal.one_sub_inv_two]

-- The point mass at `true` exceeds the uniform law on `Bool` by exactly that sum, `1/2`.
example :
    (⨆ (A : Set Bool) (_ : MeasurableSet A),
      Measure.dirac true A - uniformOn (Set.univ : Set Bool) A) = 1 / 2 := by
  rw [iSup_measure_sub_eq_sum_singleton, Fintype.sum_bool, uniformOn_univ_bool_singleton,
    uniformOn_univ_bool_singleton]
  simp [ENNReal.one_sub_inv_two]

-- The event `{true}`, where the point mass is larger than the uniform law, attains the excess:
-- its two masses differ by `1/2`.
example : {y : Bool | uniformOn (Set.univ : Set Bool) {y} < Measure.dirac true {y}} = {true} := by
  ext y
  cases y <;> rw [Set.mem_ofPred_eq, uniformOn_univ_bool_singleton] <;> simp

example :
    Measure.dirac true {true} - uniformOn (Set.univ : Set Bool) {true} = 1 / 2 := by
  rw [uniformOn_univ_bool_singleton]
  simp [ENNReal.one_sub_inv_two]

-- The total variation distance is `2 * (1 - 1/2) = 1`, twice the excess.
example : etvDist (Measure.dirac true) (uniformOn (Set.univ : Set Bool)) = 1 := by
  rw [etvDist_dirac_left, uniformOn_univ_bool_singleton, ENNReal.one_sub_inv_two,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

-- Pushing both forward along a constant map gives excess `0`, below `1/2`.
example :
    (⨆ (B : Set Bool) (_ : MeasurableSet B),
      (Measure.dirac true).map (fun _ => false) B -
        (uniformOn (Set.univ : Set Bool)).map (fun _ => false) B) = 0 := by
  simp only [Measure.map_const, measure_univ, one_smul, tsub_self]
  exact le_antisymm (iSup₂_le fun _ _ => le_rfl) bot_le

/-! ### Equal measures and distinct point masses -/

-- A finite measure is at total variation distance `0` from itself, with excess `0`.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    etvDist μ μ = 0 ∧ (⨆ (A : Set α) (_ : MeasurableSet A), μ A - μ A) = 0 :=
  ⟨etvDist_self μ, by simp⟩

-- Two point masses at distinct points are at total variation distance `2`, the largest value for
-- probability measures, and the excess of one over the other is `1`.
example {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {a b : α} (hab : a ≠ b) :
    etvDist (Measure.dirac a) (Measure.dirac b) = 2 ∧
      (⨆ (A : Set α) (_ : MeasurableSet A), Measure.dirac a A - Measure.dirac b A) = 1 := by
  have h : etvDist (Measure.dirac a) (Measure.dirac b) = 2 := by
    simp [Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hab.symm)]
  refine ⟨h, ?_⟩
  rw [etvDist_eq_two_mul_iSup_sub (by simp)] at h
  rwa [← ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top, mul_one]

end TauCeti.Examples.TotalVariation
