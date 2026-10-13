/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smooth maps composed with absolutely continuous curves

A map that is continuously differentiable near every point of the compact trace of an
absolutely continuous curve preserves absolute continuity under composition.
-/

public section

open Set

namespace AbsolutelyContinuousOnInterval

/-- Composing an absolutely continuous curve with a map that is `C¹` at every point of its trace
preserves absolute continuity. The smoothness assumption is local to the trace. -/
theorem comp_of_contDiffAt {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {γ : ℝ → F} {φ : F → G} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hφ : ∀ x ∈ γ '' uIcc a b, ContDiffAt ℝ 1 φ x) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  have hloc : LocallyLipschitzOn (γ '' uIcc a b) φ := by
    intro x hx
    obtain ⟨K, U, hU, hLip⟩ := (hφ x hx).exists_lipschitzOnWith
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hLip⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn)
  exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

end AbsolutelyContinuousOnInterval
