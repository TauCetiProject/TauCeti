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
(`ContMDiffSMul I I' n G M`). If `i : Z → M` is a `C^n` embedding intertwining an action of `G` on
`Z` with the action on `M`, then the action on `Z` is `C^n`
(`Manifold.IsSmoothEmbedding.contMDiffSMul`). The main case is the inclusion of an invariant
embedded submanifold, with the induced action of a `SubMulAction`. The proof is the smooth
universal property of a smooth embedding (`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`): a
map into `Z` is `C^n` once its composite with `i` is `C^n`.

Restricting the group instead is Mathlib's `MulAction.contMDiffSMul_compHom`: a subgroup of `G`
with a manifold structure for which its inclusion is `C^n`, such as a closed subgroup of a Lie
group with its closed-subgroup structure, acts in a `C^n` way. Combining the two, a closed subgroup
of a Lie group stabilizing an embedded submanifold acts smoothly on it; this is how the stabilizer
of a value of an equivariant moment map acts on the corresponding level.

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

/-- **Restricting a smooth action to an invariant embedded submanifold.** If `i : Z → M` is a
`C^n` embedding which intertwines an action of `G` on `Z` with a `C^n` action of `G` on `M`, then
the action on `Z` is `C^n`. -/
@[to_additive /-- If `i : Z → M` is a `C^n` embedding which intertwines an additive action of `G`
on `Z` with a `C^n` additive action of `G` on `M`, then the additive action on `Z` is `C^n`. -/]
theorem contMDiffSMul {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [SMul G M]
    {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ]
    {HZ : Type*} [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace HZ Z] [SMul G Z] [ContMDiffSMul I I' n G M]
    {i : Z → M} (hi : IsSmoothEmbedding IZ I' n i)
    (hsmul : ∀ (g : G) (z : Z), i (g • z) = g • i z) :
    ContMDiffSMul I IZ n G Z where
  contMDiff_smul := by
    have hcomp : (i ∘ fun p : G × Z ↦ p.1 • p.2) = fun p ↦ p.1 • i p.2 :=
      funext fun p ↦ hsmul p.1 p.2
    exact hi.contMDiff_iff_comp.2 <|
      hcomp ▸ contMDiff_fst.smul (hi.isImmersion.contMDiff.comp contMDiff_snd)

end Manifold.IsSmoothEmbedding
