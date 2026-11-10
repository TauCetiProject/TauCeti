/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Proper actions: compact groups and closed invariant subspaces

A continuous action of a compact group `G` on a Hausdorff space `X` is proper: the map
`(g, x) ↦ (g • x, x)` is proper because its first coordinate ranges over a compact space. In
particular the orbit space `X ⧸ G` is Hausdorff (`t2Space_quotient_mulAction_of_properSMul`), which
is how quotients such as complex projective space, the orbit space of the circle acting on an odd
sphere, are shown to be Hausdorff.

A proper action also restricts to a proper action on every closed invariant subspace, and more
generally pulls back along any equivariant closed embedding. This is the topological half of
restricting a free proper action to an invariant closed submanifold, such as a level of an
equivariant map, before taking its quotient.

## Main results

* `TauCeti.properSMul_of_compactSpace`, `TauCeti.properVAdd_of_compactSpace`: a continuous action
  of a compact group, or of a compact additive group, on a Hausdorff space is proper.
* `Topology.IsClosedEmbedding.properSMul`: an action which a closed embedding intertwines with a
  proper action is proper.
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
    obtain ⟨g, -, hg⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map Prod.fst) (by simp)
    -- `Tendsto Prod.fst 𝒰 (𝓝 g)` is by definition `map Prod.fst 𝒰 ≤ 𝓝 g`.
    rw [Ultrafilter.coe_map] at hg
    change Filter.Tendsto (Prod.fst : G × X → G) 𝒰 (nhds g) at hg
    exact ⟨g, tendsto_nhds_unique (hg.smul ((continuous_snd.tendsto _).comp hxx))
      ((continuous_fst.tendsto _).comp hxx), hg⟩⟩

end TauCeti

open Topology in
/-- **Proper actions restrict to closed invariant subspaces.** If a closed embedding `f : Y → X`
intertwines an action of `G` on `Y` with a proper action of `G` on `X`, then the action on `Y` is
proper. For instance a proper action restricts to a proper action on a closed invariant subset,
with the action of the corresponding `SubMulAction`. -/
@[to_additive /-- If a closed embedding `f : Y → X` intertwines an additive action of `G` on `Y`
with a proper additive action of `G` on `X`, then the additive action on `Y` is proper. -/]
theorem Topology.IsClosedEmbedding.properSMul {G X Y : Type*} [Group G] [TopologicalSpace G]
    [MulAction G X] [TopologicalSpace X] [ProperSMul G X] [MulAction G Y] [TopologicalSpace Y]
    {f : Y → X} (hf : IsClosedEmbedding f) (hsmul : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    ProperSMul G Y where
  isProperMap_smul_pair := by
    have hcomp : (Prod.map f f ∘ fun p : G × Y ↦ (p.1 • p.2, p.2)) =
        (fun p : G × X ↦ (p.1 • p.2, p.2)) ∘ Prod.map id f :=
      funext fun p ↦ by simp [hsmul]
    have hcont : Continuous fun p : G × Y ↦ p.1 • p.2 := by
      refine hf.isEmbedding.continuous_iff.2 ?_
      rw [show (f ∘ fun p : G × Y ↦ p.1 • p.2) = fun p ↦ p.1 • f p.2 from
        funext fun p ↦ hsmul p.1 p.2]
      exact continuous_fst.smul (hf.continuous.comp continuous_snd)
    refine isProperMap_of_comp_of_inj (hcont.prodMk continuous_snd)
      (hf.continuous.prodMap hf.continuous) ?_ (hf.injective.prodMap hf.injective)
    rw [hcomp]
    exact ProperSMul.isProperMap_smul_pair.comp (isProperMap_id.prodMap hf.isProperMap)
