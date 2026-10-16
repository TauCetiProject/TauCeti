/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group
public import TauCeti.Geometry.Diffeomorphism.Inversion
public import TauCeti.Geometry.Diffeomorphism.Evaluation

/-!
# The Whitney topology on Riemannian isometries

Riemannian isometries between compact smooth manifolds inherit the weak Whitney topology
from their underlying diffeomorphisms. On compact Hausdorff manifolds with locally compact
model space this makes the full isometry group a Hausdorff topological group. The forgetful
map is an embedding, and evaluation is jointly continuous when the model is locally compact.
Open the scope `TauCeti.RiemannianIsometryWeakWhitney` to use the topology.

This is the topology used when identifying the full isometry group of a compact geometric
model with a classical group.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33, Chapter 2 (Whitney topologies).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2 (isometries).
-/

public section

open Bundle Manifold
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : N => TangentSpace J x)]
  [CompactSpace M] [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- The subspace topology inherited from the weak Whitney topology on diffeomorphisms. -/
@[instance_reducible]
noncomputable def weakWhitneyTopology : TopologicalSpace (RiemannianIsometry I J M N) :=
  .induced toDiffeomorph inferInstance

scoped[TauCeti.RiemannianIsometryWeakWhitney] attribute [instance]
  TauCeti.RiemannianIsometry.weakWhitneyTopology

open scoped TauCeti.RiemannianIsometryWeakWhitney

/-- Forgetting the metric condition embeds Riemannian isometries in the diffeomorphisms. -/
theorem isEmbedding_toDiffeomorph :
    Topology.IsEmbedding (toDiffeomorph : RiemannianIsometry I J M N → M ≃ₘ⟮I, J⟯ N) := by
  have hinj : Function.Injective
      (toDiffeomorph : RiemannianIsometry I J M N → M ≃ₘ⟮I, J⟯ N) :=
    fun _ _ h => ext fun x => DFunLike.congr_fun h x
  exact hinj.isEmbedding_induced

/-- A family of Riemannian isometries is continuous exactly when its diffeomorphisms are. -/
theorem continuous_weakWhitney_iff {X : Type*} [TopologicalSpace X]
    {f : X → RiemannianIsometry I J M N} :
    Continuous f ↔ Continuous fun x => (f x).toDiffeomorph :=
  isEmbedding_toDiffeomorph.continuous_iff

/-- Joint evaluation of Riemannian isometries is continuous. -/
theorem continuousEval_weakWhitney [LocallyCompactSpace E] :
    ContinuousEval (RiemannianIsometry I J M N) M N :=
  ContinuousEval.of_continuous_forget isEmbedding_toDiffeomorph.continuous

scoped[TauCeti.RiemannianIsometryWeakWhitney] attribute [instance]
  TauCeti.RiemannianIsometry.continuousEval_weakWhitney

/-- A Hausdorff target gives a Hausdorff space of Riemannian isometries. -/
theorem t2Space_weakWhitney [T2Space N] : T2Space (RiemannianIsometry I J M N) :=
  isEmbedding_toDiffeomorph.t2Space

scoped[TauCeti.RiemannianIsometryWeakWhitney] attribute [instance]
  TauCeti.RiemannianIsometry.t2Space_weakWhitney

/-- The full isometry group of a compact Hausdorff smooth manifold with locally compact model
space is a topological group for the weak Whitney topology. -/
theorem isTopologicalGroup [T2Space M] [LocallyCompactSpace E] :
    IsTopologicalGroup (Isom I M) := by
  apply Topology.IsInducing.isTopologicalGroup toDiff
  convert isEmbedding_toDiffeomorph.isInducing using 1
  exact funext toDiff_apply

scoped[TauCeti.RiemannianIsometryWeakWhitney] attribute [instance]
  TauCeti.RiemannianIsometry.isTopologicalGroup

end TauCeti.RiemannianIsometry
