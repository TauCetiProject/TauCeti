/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import TauCeti.Topology.Compactness.Injectivity
import Mathlib.Topology.Order.Compact

/-!
# Minimal equal-image pairs on compact metric sets

For a map continuous on a compact metric set with Hausdorff target, local injectivity in the
relative topology makes the distinct equal-image pairs compact. If the map is not injective,
the maximum distance of such a pair from any chosen centre attains a positive minimum.
-/

public section

open Set Filter
open scoped Topology

namespace IsCompact

/-- A map continuous on a compact metric set, with Hausdorff target and local injectivity in
the relative topology, has a distinct equal-image pair minimizing the maximum distance from
a chosen centre whenever its restriction is not injective. This minimum is positive. -/
theorem exists_eq_and_ne_and_max_dist_pos_and_le_of_not_injOn
    {E X : Type*} [MetricSpace E] [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {f : E → X} (hf : ContinuousOn f K)
    (hinj : ∀ x ∈ K, ∃ U ∈ 𝓝[K] x, InjOn f U) (hnot : ¬ InjOn f K) (c : E) :
    ∃ v ∈ K, ∃ w ∈ K, f v = f w ∧ v ≠ w ∧ 0 < max (dist v c) (dist w c) ∧
      ∀ x ∈ K, ∀ y ∈ K, f x = f y → x ≠ y →
        max (dist v c) (dist w c) ≤ max (dist x c) (dist y c) := by
  let S : Set (E × E) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hS : IsCompact S := hK.isCompact_setOf_apply_eq_and_ne hf hinj
  have hSne : S.Nonempty := by
    simp only [InjOn, not_forall] at hnot
    obtain ⟨v, hv, w, hw, heq, hne⟩ := hnot
    exact ⟨(v, w), hv, hw, heq, hne⟩
  have hc : Continuous (fun z : E × E ↦ max (dist z.1 c) (dist z.2 c)) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  refine ⟨z.1, hz.1, z.2, hz.2.1, hz.2.2.1, hz.2.2.2, ?_, ?_⟩
  · by_contra h
    have hzero := le_of_not_gt h
    have hv : z.1 = c := dist_eq_zero.mp
      (le_antisymm ((le_max_left _ _).trans hzero) dist_nonneg)
    have hw : z.2 = c := dist_eq_zero.mp
      (le_antisymm ((le_max_right _ _).trans hzero) dist_nonneg)
    exact hz.2.2.2 (hv.trans hw.symm)
  · intro x hx y hy he hne
    exact hmin (show (x, y) ∈ S from ⟨hx, hy, he, hne⟩)

end IsCompact
