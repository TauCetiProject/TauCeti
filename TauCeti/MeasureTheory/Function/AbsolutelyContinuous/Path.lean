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

namespace Path

variable {X : Type*} [PseudoMetricSpace X] {x y z : X}

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
  change γ (projIcc 0 1 zero_le_one (θ t)) = γ (projIcc 0 1 zero_le_one t)
  congr 1
  apply Subtype.ext
  dsimp [θ, projIcc]
  simp only [min_max_distrib_left, min_eq_right zero_le_one,
    ← max_assoc, max_self, ← min_assoc, min_self]

/-- Reversing a path preserves absolute continuity of its standard real extension. -/
theorem absolutelyContinuousOnInterval_extend_symm {γ : Path x y}
    (hγ : AbsolutelyContinuousOnInterval γ.extend 0 1) :
    AbsolutelyContinuousOnInterval γ.symm.extend 0 1 := by
  have hθ : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ 1 - t) 0 1 := by
    have hc : ContDiffOn ℝ 1 (fun t : ℝ ↦ 1 - t) (uIcc (0 : ℝ) 1) := by fun_prop
    exact hc.absolutelyContinuousOnInterval
  have hmap : MapsTo (fun t : ℝ ↦ 1 - t) (uIcc (0 : ℝ) 1) (uIcc (0 : ℝ) 1) := by
    simp only [uIcc_of_le zero_le_one, MapsTo, mem_Icc]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hm : Antitone (fun t : ℝ ↦ 1 - t) := by intro s t hst; linarith
  simpa only [extend_symm, Function.comp_def] using hγ.comp_antitoneOn hθ (hm.antitoneOn _) hmap

/-- Concatenating two absolutely continuous paths preserves absolute continuity. -/
theorem absolutelyContinuousOnInterval_extend_trans {γ₁ : Path x y} {γ₂ : Path y z}
    (h₁ : AbsolutelyContinuousOnInterval γ₁.extend 0 1)
    (h₂ : AbsolutelyContinuousOnInterval γ₂.extend 0 1) :
    AbsolutelyContinuousOnInterval (γ₁.trans γ₂).extend 0 1 := by
  have hleft : AbsolutelyContinuousOnInterval (γ₁.trans γ₂).extend 0 (1 / 2) := by
    have hc : ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t) (uIcc (0 : ℝ) (1 / 2)) := by fun_prop
    have hm : Monotone (fun t : ℝ ↦ 2 * t) := by intro s t hst; linarith
    have hmap : MapsTo (fun t : ℝ ↦ 2 * t) (uIcc (0 : ℝ) (1 / 2))
        (uIcc (0 : ℝ) 1) := by
      simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
        uIcc_of_le zero_le_one, MapsTo, mem_Icc]
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    apply (h₁.comp_monotoneOn hc.absolutelyContinuousOnInterval (hm.monotoneOn _) hmap).congr
    intro t ht
    exact (extend_trans_of_le_half γ₁ γ₂
      ((uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)) ▸ ht).2).symm
  have hright : AbsolutelyContinuousOnInterval (γ₁.trans γ₂).extend (1 / 2) 1 := by
    have hc : ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t - 1) (uIcc (1 / 2 : ℝ) 1) := by fun_prop
    have hm : Monotone (fun t : ℝ ↦ 2 * t - 1) := by intro s t hst; linarith
    have hmap : MapsTo (fun t : ℝ ↦ 2 * t - 1) (uIcc (1 / 2 : ℝ) 1)
        (uIcc (0 : ℝ) 1) := by
      simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
        uIcc_of_le zero_le_one, MapsTo, mem_Icc]
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    apply (h₂.comp_monotoneOn hc.absolutelyContinuousOnInterval (hm.monotoneOn _) hmap).congr
    intro t ht
    exact (extend_trans_of_half_le γ₁ γ₂
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
  rw [extend_apply _ ht]
  rfl

end Path
