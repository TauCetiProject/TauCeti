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

/-- A connected finite-dimensional real Lie group is covered by its simply connected universal
covering Lie group. The local path-connectedness and semilocal simple-connectedness needed by the
based-path construction are obtained from convex model neighborhoods and extended charts. The
covering homomorphism is the endpoint projection, with its smoothness, covering property, and
Lie-group laws supplied by the canonical construction and its pulled-back instances.
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
  let p : Gt →* G := (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G)
  have hp : IsCoveringMap (p : Gt → G) := by
    -- The endpoint projection has distinct monoid-hom and continuous-map coercions;
    -- select the native coercion expected by its covering theorem.
    change IsCoveringMap (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G)
    exact UniversalCover.isCoveringMap_projHom
  have hsmooth : ContMDiff I I ∞ (p : Gt → G) := by
    dsimp [p]
    rw [UniversalCover.coe_projHom]
    exact UniversalCover.contMDiff_proj (x₀ := (1 : G))
  have hlie : Function.Bijective
      (lieMap (ContinuousMonoidHom.toContMDiffMonoidMorphism I I
        (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G))) :=
    UniversalCover.lieMap_projHom_bijective I G
  have hpm : (⟨p, hsmooth⟩ : ContMDiffMonoidMorphism I I ∞ Gt G) =
      ContinuousMonoidHom.toContMDiffMonoidMorphism I I
        (UniversalCover.projHom : UniversalCover (1 : G) →ₜ* G) := by
    apply DFunLike.coe_injective
    simp only [ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
    funext x
    change p x = (UniversalCover.projHom : Gt → G) x
    rfl
  exact ⟨Gt, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, p, hsmooth,
    UniversalCover.simplyConnectedSpace (1 : G), hp, by rw [hpm]; exact hlie⟩

end TauCeti.UniversalCover
