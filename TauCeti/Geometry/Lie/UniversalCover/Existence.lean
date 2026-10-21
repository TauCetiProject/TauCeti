/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.UniversalCover

/-!
# Existence of universal covering Lie groups

A connected Lie group with the local hypotheses needed for its based-path cover has a canonical
simply connected covering group: the universal cover of the identity, equipped with the smooth
structure pulled back from the base.
This file packages the existing concrete construction into the existential interface used by
integration and descent arguments.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.UniversalCover

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G]
  [Group G] [LieGroup I ∞ G]

/-- A connected Lie group is covered by its simply connected universal covering Lie group.

The local path-connectedness and semilocal simple-connectedness assumptions are exactly those
used by the canonical based-path universal cover. The covering homomorphism is the endpoint
projection, and its smooth structure and Lie-group laws are the pulled-back canonical instances.
-/
theorem exists_universalCover [IsTopologicalGroup G] [LocallyPathConnectedSpace G]
    [SemilocallySimplyConnectedSpace G] [ConnectedSpace G] :
    ∃ (Gt : Type w) (_ : TopologicalSpace Gt) (_ : ChartedSpace H Gt)
      (_ : IsManifold I ∞ Gt) (_ : Group Gt) (_ : LieGroup I ∞ Gt) (p : Gt →* G),
      SimplyConnectedSpace Gt ∧ IsCoveringMap (p : Gt → G) := by
  let _ : PathConnectedSpace G := PathConnectedSpace.of_locallyPathConnectedSpace
  let Gt := UniversalCover (1 : G)
  let p : Gt →* G := (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G)
  have hp : IsCoveringMap (p : Gt → G) := by
    -- The endpoint projection has distinct monoid-hom and continuous-map coercions;
    -- select the native coercion expected by its covering theorem.
    change IsCoveringMap (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G)
    exact UniversalCover.isCoveringMap_projHom
  exact ⟨Gt, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, p,
    UniversalCover.simplyConnectedSpace (1 : G), hp⟩

end TauCeti.UniversalCover
