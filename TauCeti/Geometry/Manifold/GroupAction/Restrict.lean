/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Restricting smooth actions to subgroups and to invariant submanifolds

Let a group `G` act on a manifold `M` by a `C^n` map `G × M → M`
(`ContMDiffSMul I I' n G M`). This file records the two ways of restricting such an action that
are used to build quotients of invariant pieces of `M`.

* **Restricting the group.** If `K` acts on `M` through a `C^n` map `f : K → G`, in the sense that
  `k • x = f k • x`, then the action of `K` is `C^n`
  (`ContMDiffSMul.of_contMDiff_of_smul_eq`). The main case is a subgroup `K ≤ G` carrying a
  manifold structure of its own for which the inclusion is `C^n`, such as a closed subgroup of a
  Lie group with its closed-subgroup structure (`ContMDiffSMul.of_contMDiff_subtypeVal`).
* **Restricting the space.** If `i : Z → M` is a `C^n` embedding intertwining an action of `G` on
  `Z` with the action on `M`, then the action on `Z` is `C^n`
  (`ContMDiffSMul.of_isSmoothEmbedding`). The main case is the inclusion of an invariant embedded
  submanifold, with the induced action of a `SubMulAction`. The proof is the smooth universal
  property of an immersion (`ContMDiff.iff_comp_isImmersion`): a map into `Z` is `C^n` once it is
  continuous and its composite with `i` is `C^n`, and continuity comes from `i` being a
  topological embedding.

Combining the two, a closed subgroup of a Lie group stabilizing an embedded submanifold acts
smoothly on it; this is how the stabilizer of a value of an equivariant moment map acts on the
corresponding level.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 5.29
  (restricting the codomain of a smooth map to an embedded submanifold) and Chapter 21.
-/

public section

open Manifold
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] {n : ℕ∞ω}

namespace ContMDiffSMul

/-- **Restricting a smooth action along a smooth map of groups.** If `K` acts on `M` through a
`C^n` map `f : K → G`, that is `k • x = f k • x`, and the action of `G` is `C^n`, then so is the
action of `K`. -/
@[to_additive /-- If `K` acts additively on `M` through a `C^n` map `f : K → G`, that is
`k +ᵥ x = f k +ᵥ x`, and the additive action of `G` is `C^n`, then so is the additive action of
`K`. -/]
theorem of_contMDiff_of_smul_eq {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [SMul G M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {HK : Type*} [TopologicalSpace HK] {J : ModelWithCorners 𝕜 F HK}
    {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [SMul K M] [ContMDiffSMul I I' n G M]
    {f : K → G} (hf : ContMDiff J I n f) (hsmul : ∀ (k : K) (x : M), k • x = f k • x) :
    ContMDiffSMul J I' n K M where
  contMDiff_smul := by
    simp_rw [hsmul]
    exact (hf.comp contMDiff_fst).smul contMDiff_snd

/-- **Restricting a smooth action to a smooth subgroup.** If a subgroup `L` of `G` carries a
manifold structure for which its inclusion into `G` is `C^n`, a `C^n` action of `G` restricts to a
`C^n` action of `L`. For a closed subgroup of a finite-dimensional Lie group, the closed-subgroup
theorem provides such a structure. -/
@[to_additive /-- If an additive subgroup `L` of `G` carries a manifold structure for which its
inclusion into `G` is `C^n`, a `C^n` additive action of `G` restricts to a `C^n` additive action
of `L`. -/]
theorem of_contMDiff_subtypeVal {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    [MulAction G M] [ContMDiffSMul I I' n G M] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {HK : Type*} [TopologicalSpace HK] {J : ModelWithCorners 𝕜 F HK}
    {L : Subgroup G} [ChartedSpace HK L] (hL : ContMDiff J I n (Subtype.val : L → G)) :
    ContMDiffSMul J I' n L M :=
  of_contMDiff_of_smul_eq hL fun _ _ ↦ Subgroup.smul_def _ _

/-- **Restricting a smooth action to an invariant embedded submanifold.** If `i : Z → M` is a
`C^n` embedding which intertwines an action of `G` on `Z` with a `C^n` action of `G` on `M`, then
the action on `Z` is `C^n`. -/
@[to_additive /-- If `i : Z → M` is a `C^n` embedding which intertwines an additive action of `G`
on `Z` with a `C^n` additive action of `G` on `M`, then the additive action on `Z` is `C^n`. -/]
theorem of_isSmoothEmbedding {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [SMul G M]
    {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
    {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] [SMul G Z] [ContMDiffSMul I I' n G M]
    {i : Z → M} (hi : IsSmoothEmbedding IZ I' n i)
    (hsmul : ∀ (g : G) (z : Z), i (g • z) = g • i z) :
    ContMDiffSMul I IZ n G Z where
  contMDiff_smul := by
    have hcomp : (i ∘ fun p : G × Z ↦ p.1 • p.2) = fun p ↦ p.1 • i p.2 :=
      funext fun p ↦ hsmul p.1 p.2
    have hsmooth : ContMDiff (I.prod IZ) I' n fun p : G × Z ↦ p.1 • i p.2 :=
      contMDiff_fst.smul (hi.isImmersion.contMDiff.comp contMDiff_snd)
    refine (ContMDiff.iff_comp_isImmersion hi.isImmersion).2 ⟨?_, hcomp ▸ hsmooth⟩
    exact hi.isEmbedding.continuous_iff.2 (hcomp ▸ hsmooth.continuous)

end ContMDiffSMul
