/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Topology.Order.IntervalLifting
import Mathlib.Tactic.Linarith

/-!
# Extending interval lifts through local homeomorphisms

A local inverse extends a lift of a continuous real curve beyond a closed interval,
without changing its values on that interval.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter Function
open scoped Topology

namespace IsLocalHomeomorph

/-- A local inverse continues an existing interval lift beyond its endpoint. -/
theorem exists_extend_lift_Icc
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) {c : ℝ → Y} (hc : Continuous c)
    {a T : ℝ} (hT : a ≤ T) {l : ℝ → X} (hl : ContinuousOn l (Icc a T))
    (hproj : EqOn (f ∘ l) c (Icc a T)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ l' : ℝ → X,
      ContinuousOn l' (Icc a (T + δ)) ∧ EqOn l' l (Icc a T) ∧
      EqOn (f ∘ l') c (Icc a (T + δ)) := by
  classical
  obtain ⟨e, hs, he⟩ := hf (l T)
  have ht : c T ∈ e.target := by
    rw [← hproj ⟨hT, le_rfl⟩, comp_apply, he]
    exact e.map_source hs
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht))
  let δ : ℝ := η / 2
  have hδ : 0 < δ := half_pos hη
  have hmaps : MapsTo c (Icc T (T + δ)) e.target := by
    intro t ht'
    apply hsub
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht'.1)]
    dsimp [δ] at ht'
    linarith [ht'.2]
  let l₂ : ℝ → X := e.symm ∘ c
  have hl₂ : ContinuousOn l₂ (Icc T (T + δ)) :=
    e.continuousOn_symm.comp hc.continuousOn hmaps
  have hjoin : l₂ T = l T := by
    dsimp only [l₂, comp_apply]
    rw [← hproj ⟨hT, le_rfl⟩, comp_apply, he]
    exact e.left_inv hs
  refine ⟨δ, hδ, ?_⟩
  apply ContinuousOn.exists_lift_piecewise_Icc hl hl₂ hjoin.symm hproj
  intro t ht'
  dsimp only [l₂, comp_apply]
  rw [he]
  exact e.right_inv (hmaps ht')

end IsLocalHomeomorph
