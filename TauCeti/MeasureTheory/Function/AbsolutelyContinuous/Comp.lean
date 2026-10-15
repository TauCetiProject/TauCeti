/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smooth maps composed with absolutely continuous curves

Locally Lipschitz maps preserve the absolute continuity of metric-valued curves under composition,
and isometries moreover reflect it.
In particular, a map that is continuously differentiable near every point of the compact trace of
an absolutely continuous curve preserves absolute continuity.
-/

public section

open Set

/-- A locally Lipschitz map preserves the absolute continuity of a metric-valued curve whose
trace lies in its domain of local Lipschitz continuity. -/
theorem LocallyLipschitzOn.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {φ : X → Y} {γ : ℝ → X}
    {s : Set X} {a b : ℝ} (hφ : LocallyLipschitzOn s φ)
    (hmap : MapsTo γ (uIcc a b) s) (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (φ ∘ γ) a b := by
  obtain ⟨K, hK⟩ := (hφ.mono hmap.image_subset).exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn')
  exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

/-- Post-composition with an isometry preserves and reflects the absolute continuity of a
metric-valued curve. -/
theorem Isometry.absolutelyContinuousOnInterval_comp_iff
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} (hf : Isometry f)
    {γ : ℝ → X} {a b : ℝ} :
    AbsolutelyContinuousOnInterval (f ∘ γ) a b ↔ AbsolutelyContinuousOnInterval γ a b := by
  simp only [absolutelyContinuousOnInterval_iff, Function.comp_apply, hf.dist_eq]

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
  exact hloc.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hγ

end AbsolutelyContinuousOnInterval
