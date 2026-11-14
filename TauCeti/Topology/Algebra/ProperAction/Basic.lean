/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Continuous actions of compact groups are proper

A continuous action of a compact group `G` on a Hausdorff space `X` is proper: the map
`(g, x) ↦ (g • x, x)` is proper because its first coordinate ranges over a compact space. In
particular the orbit space `X ⧸ G` is Hausdorff (`t2Space_quotient_mulAction_of_properSMul`), which
is how quotients such as complex projective space, the orbit space of the circle acting on an odd
sphere, are shown to be Hausdorff.

## Main results

* `TauCeti.properSMul_of_compactSpace`, `TauCeti.properVAdd_of_compactSpace`: a continuous action
  of a compact group, or of a compact additive group, on a Hausdorff space is proper.
-/

public section

namespace TauCeti

/-- **A continuous action of a compact group on a Hausdorff space is proper.** This is not an
instance, since `ProperSMul` itself provides `ContinuousSMul`. -/
@[to_additive /-- **A continuous action of a compact additive group on a Hausdorff space is
proper.** This is not an instance, since `ProperVAdd` itself provides `ContinuousVAdd`. -/]
theorem properSMul_of_compactSpace (G X : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
    [MulAction G X] [TopologicalSpace X] [T2Space X] [ContinuousSMul G X] : ProperSMul G X :=
  properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨inferInstance, fun 𝒰 _ _ hxx ↦ by
    -- In the compact space `G` the ultrafilter `𝒰.map Prod.fst` converges to its limit.
    have hg : Filter.Tendsto Prod.fst (𝒰 : Filter (G × X)) (nhds (𝒰.map Prod.fst).lim) := by
      rw [Filter.Tendsto, ← Ultrafilter.coe_map]
      exact (𝒰.map Prod.fst).le_nhds_lim
    exact ⟨_, tendsto_nhds_unique (hg.smul ((continuous_snd.tendsto _).comp hxx))
      ((continuous_fst.tendsto _).comp hxx), hg⟩⟩

end TauCeti
