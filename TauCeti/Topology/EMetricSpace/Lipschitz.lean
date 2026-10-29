/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Lipschitz maps from extended metric spaces

This file gives a real-valued Lipschitz estimate for the extended distance from a fixed point,
and shows that composing a function locally Lipschitz on a set with a locally Lipschitz map keeps
it locally Lipschitz on that set.

The declaration `TauCeti.lipschitzWith_toReal_edist` and its proof follow
[Mathlib pull request #41839](https://github.com/leanprover-community/mathlib4/pull/41839),
available under Apache 2.0.
-/

public section

open Filter
open scoped ENNReal

namespace TauCeti

/-- Distance from a fixed point, converted to a real number, is `1`-Lipschitz. -/
theorem lipschitzWith_toReal_edist {X : Type*} [PseudoEMetricSpace X] (a : X) :
    LipschitzWith 1 (fun x ↦ (edist a x).toReal) := by
  intro x y
  by_cases hxy : edist x y = ∞
  · simp [hxy]
  have hxy' : edist y x ≠ ∞ := by simpa only [edist_comm] using hxy
  by_cases hax : edist a x = ∞
  · have hay : edist a y = ∞ := by
      by_contra hay
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hay, hxy'⟩) (edist_triangle a y x) hax
    simp [hax, hay]
  have hay : edist a y ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hax, hxy⟩) (edist_triangle a x y)
  suffices ENNReal.ofReal (dist (edist a x).toReal (edist a y).toReal) ≤ edist x y by
    simpa only [edist_dist, ENNReal.coe_one, one_mul] using this
  rw [ENNReal.ofReal_le_iff_le_toReal hxy, Real.dist_eq, abs_le]
  have hforward := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hax, hxy⟩)
    (edist_triangle a x y)
  have hbackward := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hay, hxy'⟩)
    (edist_triangle a y x)
  rw [ENNReal.toReal_add hax hxy] at hforward
  rw [ENNReal.toReal_add hay hxy', edist_comm y x] at hbackward
  constructor <;> linarith

end TauCeti

/-- A locally Lipschitz map composed with a function locally Lipschitz on `s` is locally Lipschitz
on `s`. -/
theorem LocallyLipschitz.comp_locallyLipschitzOn {α β γ : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {g : β → γ} {f : α → β} {s : Set α}
    (hg : LocallyLipschitz g) (hf : LocallyLipschitzOn s f) : LocallyLipschitzOn s (g ∘ f) := by
  intro x hx
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, U, hU, hKg⟩ := hg (f x)
  refine ⟨Kg * Kf, t ∩ f ⁻¹' U, inter_mem ht (hf.continuousOn x hx hU), ?_⟩
  exact hKg.comp (hKf.mono Set.inter_subset_left) fun _ hy => hy.2
