/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Weighted reparametrization of functions of bounded variation

A continuous map that is locally monotone or antitone pulls back local bounded variation.
A smooth scalar weight then preserves bounded variation on a smaller closed interval.

## References

The proof uses Mathlib's `eVariationOn.comp_le_of_monotoneOn`, its antitone counterpart
and the compact-interval Lipschitz bound `ContDiffOn.exists_lipschitzOnWith`.
-/

public section

open Filter Set
open scoped Topology

/-- A locally monotone or antitone reparametrization with a smooth scalar weight preserves
bounded variation on some closed interval about the base point. -/
theorem BoundedVariationOn.exists_Icc_smul_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {φ w : ℝ → ℝ} {s t : Set ℝ} {a : ℝ}
    (hf : BoundedVariationOn f s) (hs : s ∈ 𝓝 (φ a)) (ht : t ∈ 𝓝 a)
    (hφ : ContinuousAt φ a) (hmono : MonotoneOn φ t ∨ AntitoneOn φ t)
    (hw : ContDiffOn ℝ 1 w t) :
    ∃ r > 0, BoundedVariationOn (fun u ↦ w u • f (φ u)) (Icc (a - r) (a + r)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (hφ.preimage_mem_nhds hs))
  let S := Icc (a - r / 2) (a + r / 2)
  have hS : S ⊆ t ∩ φ ⁻¹' s := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hmaps : MapsTo φ S s := fun _ hu ↦ (hS hu).2
  have hcomp : BoundedVariationOn (f ∘ φ) S := by
    refine ne_top_of_le_ne_top hf (hmono.elim ?_ ?_)
    · exact fun h ↦ eVariationOn.comp_le_of_monotoneOn f φ (h.mono (hS.trans inter_subset_left))
        hmaps
    · exact fun h ↦ eVariationOn.comp_le_of_antitoneOn f φ (h.mono (hS.trans inter_subset_left))
        hmaps
  obtain ⟨C, hC⟩ := (hw.mono (hS.trans inter_subset_left)).exists_lipschitzOnWith
    one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hwv := hC.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc _ _)
  exact ⟨r / 2, by positivity, hwv.fun_smul hcomp⟩
