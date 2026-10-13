/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Reparam
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Absolutely continuous paths

Absolute continuity of the standard real extension of a path is preserved by reversal,
concatenation, and truncation. These facts use the existing `Path` operations.
-/

public section

open Set

variable {X : Type*} [PseudoMetricSpace X] {x y z : X}

namespace Path

/-- The constant extension of an absolutely continuous path is absolutely continuous on every
real parameter interval. -/
theorem absolutelyContinuousOnInterval_extend {γ : Path x y}
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1) (a b : ℝ) :
    AbsolutelyContinuousOnInterval γ.extend a b := by
  let θ : ℝ → ℝ := fun t ↦ max 0 (min 1 t)
  have hθ : AbsolutelyContinuousOnInterval θ a b :=
    ((LipschitzWith.id.const_min 1).const_max 0).lipschitzOnWith.absolutelyContinuousOnInterval
  have hm : Monotone θ := (monotone_const.max (monotone_const.min monotone_id))
  have hmap : MapsTo θ (uIcc a b) (uIcc (0 : ℝ) 1) := by
    intro t _
    rw [uIcc_of_le zero_le_one]
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  apply (hγ.comp_monotoneOn hθ (hm.monotoneOn _) hmap).congr
  intro t _
  simp only [Function.comp_apply]
  by_cases ht₀ : t ≤ 0
  · have hθt : θ t = 0 := by simp [θ, min_eq_right (ht₀.trans zero_le_one), max_eq_left ht₀]
    rw [hθt, extend_zero, extend_of_le_zero γ ht₀]
  by_cases ht₁ : 1 ≤ t
  · have hθt : θ t = 1 := by simp [θ, min_eq_left ht₁]
    rw [hθt, extend_one, extend_of_one_le γ ht₁]
  have hθt : θ t = t := by
    simp [θ, min_eq_right (le_of_not_ge ht₁), max_eq_right (le_of_not_ge ht₀)]
  rw [hθt]

/-- Reversing a path preserves absolute continuity of its standard real extension. -/
theorem absolutelyContinuousOnInterval_extend_symm {γ : Path x y}
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1) :
    AbsolutelyContinuousOnInterval γ.symm.extend 0 1 := by
  have hmap : MapsTo (fun t : ℝ ↦ 1 - t) (uIcc (0 : ℝ) 1) (uIcc (0 : ℝ) 1) := by
    simp only [uIcc_of_le zero_le_one, MapsTo, mem_Icc]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmap' : MapsTo (fun t : ℝ ↦ (-1) * t + 1)
      (uIcc (0 : ℝ) 1) (uIcc (0 : ℝ) 1) := by
    simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using hmap
  simpa only [extend_symm, Function.comp_def, neg_one_mul, sub_eq_add_neg, add_comm]
    using AbsolutelyContinuousOnInterval.comp_affine hγ (-1) 1 hmap'

/-- Concatenating two absolutely continuous paths preserves absolute continuity. -/
theorem absolutelyContinuousOnInterval_extend_trans {γ₁ : Path x y} {γ₂ : Path y z}
    (h₁ : AbsolutelyContinuousOnInterval γ₁.extend 0 1)
    (h₂ : AbsolutelyContinuousOnInterval γ₂.extend 0 1) :
    AbsolutelyContinuousOnInterval (γ₁.trans γ₂).extend 0 1 := by
  have hleft : AbsolutelyContinuousOnInterval (γ₁.trans γ₂).extend 0 (1 / 2) := by
    have hmap : MapsTo (fun t : ℝ ↦ 2 * t) (uIcc (0 : ℝ) (1 / 2))
        (uIcc (0 : ℝ) 1) := by
      simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        uIcc_of_le zero_le_one, MapsTo, mem_Icc]
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    apply (AbsolutelyContinuousOnInterval.comp_affine h₁ 2 0
      (by simpa only [add_zero] using hmap)).congr
    intro t ht
    simpa only [Function.comp_apply, add_zero] using (extend_trans_of_le_half γ₁ γ₂
      ((uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)) ▸ ht).2).symm
  have hright : AbsolutelyContinuousOnInterval (γ₁.trans γ₂).extend (1 / 2) 1 := by
    have hmap : MapsTo (fun t : ℝ ↦ 2 * t - 1) (uIcc (1 / 2 : ℝ) 1)
        (uIcc (0 : ℝ) 1) := by
      simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
        uIcc_of_le zero_le_one, MapsTo, mem_Icc]
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    apply (AbsolutelyContinuousOnInterval.comp_affine h₂ 2 (-1)
      (by simpa only [sub_eq_add_neg] using hmap)).congr
    intro t ht
    simpa only [Function.comp_apply, sub_eq_add_neg] using (extend_trans_of_half_le γ₁ γ₂
      ((uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)) ▸ ht).1).symm
  exact hleft.trans hright

/-- Truncating an absolutely continuous path preserves absolute continuity, with arbitrary
real truncation parameters. -/
theorem absolutelyContinuousOnInterval_extend_truncate {γ : Path x y}
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1) (t₀ t₁ : ℝ) :
    AbsolutelyContinuousOnInterval (γ.truncate t₀ t₁).extend 0 1 := by
  let θ : ℝ → ℝ := fun t ↦ min (max t t₀) t₁
  have hθ : AbsolutelyContinuousOnInterval θ 0 1 :=
    ((LipschitzWith.id.max_const t₀).min_const t₁).lipschitzOnWith.absolutelyContinuousOnInterval
  have hm : Monotone θ := (monotone_id.max monotone_const).min monotone_const
  have hmap : MapsTo θ (uIcc (0 : ℝ) 1) (uIcc (θ 0) (θ 1)) := by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (hm zero_le_one)]
    exact hm.mapsTo_Icc
  apply ((absolutelyContinuousOnInterval_extend hγ (θ 0) (θ 1)).comp_monotoneOn
    hθ (hm.monotoneOn _) hmap).congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  rw [extend_apply _ ht, truncate, coe_mk_mk]
  rfl

end Path
