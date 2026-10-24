/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.UniversalCover
public import TauCeti.Geometry.Manifold.Topology

/-!
# Existence of universal covering Lie groups

A connected finite-dimensional real Lie group has a canonical simply connected covering group: the
universal cover of the identity, equipped with the smooth structure pulled back from the base.
This file packages the existing concrete construction into the existential interface used by
integration and descent arguments.
-/

public section

noncomputable section

open scoped ContDiff Manifold
open Topology

namespace TauCeti.UniversalCover

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G]
  [Group G] [LieGroup I ∞ G]

/-- A connected finite-dimensional real Lie group admits a simply connected Lie-group cover.

There exist a simply connected Lie group `Gt` and a smooth homomorphism `p : Gt →* G` that is a
covering map and whose induced Lie-algebra map is bijective.
-/
theorem exists_universalCover [ConnectedSpace G] :
    ∃ (Gt : Type w) (_ : TopologicalSpace Gt) (_ : ChartedSpace H Gt)
      (_ : IsManifold I ∞ Gt) (_ : Group Gt) (_ : LieGroup I ∞ Gt) (p : Gt →* G)
      (hsmooth : ContMDiff I I ∞ (p : Gt → G)),
      SimplyConnectedSpace Gt ∧ IsCoveringMap (p : Gt → G) ∧
        Function.Bijective
          (lieMap (⟨p, hsmooth⟩ : ContMDiffMonoidMorphism I I ∞ Gt G)) := by
  let _ : LocallyPathConnectedSpace H := I.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace H G
  let _ : SemilocallySimplyConnectedSpace G := I.semilocallySimplyConnectedSpace G
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : PathConnectedSpace G := PathConnectedSpace.of_locallyPathConnectedSpace
  let Gt := UniversalCover (1 : G)
  let f : ContMDiffMonoidMorphism I I ∞ Gt G :=
    (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G).toContMDiffMonoidMorphism I I
  let p : Gt →* G := f.toMonoidHom
  have hpc : (p : Gt → G) = (UniversalCover.projHom : Gt → G) := by
    dsimp only [p]
    change (f : Gt → G) = (UniversalCover.projHom : Gt → G)
    exact ContinuousMonoidHom.coe_toContMDiffMonoidMorphism _
  have hp : IsCoveringMap (p : Gt → G) := by
    rw [hpc]
    exact UniversalCover.isCoveringMap_projHom
  have hsmooth : ContMDiff I I ∞ (p : Gt → G) := f.contMDiff_toFun
  exact ⟨Gt, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, p, hsmooth,
    UniversalCover.simplyConnectedSpace (1 : G), hp,
    by simpa only [p, f, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism,
      ContinuousMonoidHom.coe_toMonoidHom] using UniversalCover.lieMap_projHom_bijective I G⟩

end TauCeti.UniversalCover
