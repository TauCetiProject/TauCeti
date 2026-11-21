/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Restricting smooth actions to invariant submanifolds

Let a group `G` act on a manifold `M` by a `C^n` map `G × M → M`
(`ContMDiffSMul I I' n G M`). Let `f : G' → G` be a `C^n` map and `i : Z → M` a `C^n` embedding
intertwining an action of `G'` on `Z` with the action on `M` along `f`, that is
`i (g • z) = f g • i z`. Then the action of `G'` on `Z` is `C^n`
(`Manifold.IsSmoothEmbedding.contMDiffSMul`). This is the smooth counterpart of Mathlib's
`Topology.IsInducing.continuousSMul`. The proof is the smooth universal property of a smooth
embedding (`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`): a map into `Z` is `C^n` once its
composite with `i` is `C^n`.

The main case is a subgroup `G'` of `G` with a manifold structure for which its inclusion is
`C^n`, such as a closed subgroup of a Lie group with its closed-subgroup structure, acting on an
invariant embedded submanifold `Z` by the induced action of a `SubMulAction`. This is how the
stabilizer of a value of an equivariant moment map acts on the corresponding level.

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

namespace Manifold.IsSmoothEmbedding

/-- **Restricting a smooth action to an invariant embedded submanifold.** Let `f : G' → G` be a
`C^n` map and `i : Z → M` a `C^n` embedding intertwining an action of `G'` on `Z` with a `C^n`
action of `G` on `M` along `f`. Then the action of `G'` on `Z` is `C^n`. -/
@[to_additive /-- Let `f : G' → G` be a `C^n` map and `i : Z → M` a `C^n` embedding intertwining
an additive action of `G'` on `Z` with a `C^n` additive action of `G` on `M` along `f`. Then the
additive action of `G'` on `Z` is `C^n`. -/]
theorem contMDiffSMul {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [SMul G M]
    [ContMDiffSMul I I' n G M]
    {EG' : Type*} [NormedAddCommGroup EG'] [NormedSpace 𝕜 EG']
    {HG' : Type*} [TopologicalSpace HG'] {IG' : ModelWithCorners 𝕜 EG' HG'}
    {G' : Type*} [TopologicalSpace G'] [ChartedSpace HG' G']
    {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
    {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] [SMul G' Z]
    {i : Z → M} (hi : IsSmoothEmbedding IZ I' n i) {f : G' → G} (hf : ContMDiff IG' I n f)
    (hsmul : ∀ (g : G') (z : Z), i (g • z) = f g • i z) :
    ContMDiffSMul IG' IZ n G' Z where
  contMDiff_smul := by
    have hcomp : (i ∘ fun p : G' × Z ↦ p.1 • p.2) = fun p ↦ f p.1 • i p.2 :=
      funext fun p ↦ hsmul p.1 p.2
    exact hi.contMDiff_iff_comp.2 <|
      hcomp ▸ (hf.comp contMDiff_fst).smul (hi.isImmersion.contMDiff.comp contMDiff_snd)

end Manifold.IsSmoothEmbedding
