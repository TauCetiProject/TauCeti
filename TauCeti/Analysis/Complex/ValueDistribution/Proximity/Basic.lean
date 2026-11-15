/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import TauCeti.MeasureTheory.Integral.CircleAverage

/-!
# Local radial continuity of the Nevanlinna proximity function

Mathlib's `ValueDistribution.continuous_proximity_top` establishes global continuity of
`ValueDistribution.proximity g ⊤` when `g : ℂ → E` is continuous on all of `ℂ`. When `g` is merely
meromorphic (or defined locally), interior poles prevent global continuity of `g`, yet at any radius
`R` whose circle `sphere 0 |R|` avoids the singularities of `g`, `g` is continuous on a
neighbourhood of `sphere 0 |R|` and `ContinuousOn.continuousAt_circleAverage` yields continuity of
`ValueDistribution.proximity g ⊤` at `R` (including across boundary zeros of `g`).
-/

public section

open Filter Metric Real Set Topology

/-- If `g : ℂ → E` is continuous on a set `s` that is a neighbourhood of `sphere 0 |R|`, then its
Nevanlinna proximity function `ValueDistribution.proximity g ⊤` is continuous at `R` (including
when `g` has poles inside `ball 0 |R|` or zeros on `sphere 0 |R|`). -/
theorem ContinuousOn.continuousAt_proximity_top {E : Type*} [NormedAddCommGroup E]
    {g : ℂ → E} {s : Set ℂ} {R : ℝ} (hg : ContinuousOn g s) (hs : s ∈ 𝓝ˢ (sphere 0 |R|)) :
    ContinuousAt (ValueDistribution.proximity g ⊤) R := by
  rw [ValueDistribution.proximity_top]
  exact (continuous_posLog.comp_continuousOn hg.norm).continuousAt_circleAverage hs

-- `z ↦ z⁻¹` has an interior pole at `0`, yet `proximity (·⁻¹) ⊤` is continuous at `R = 1`.
example : ContinuousAt (ValueDistribution.proximity (fun z : ℂ ↦ z⁻¹) ⊤) 1 := by
  have hs : ({0}ᶜ : Set ℂ) ∈ 𝓝ˢ (sphere (0 : ℂ) |1|) :=
    isOpen_compl_singleton.mem_nhdsSet.mpr fun z hz ↦ by
      rw [mem_compl_singleton_iff]
      rintro rfl
      simp at hz
  exact continuousOn_inv₀.continuousAt_proximity_top hs
