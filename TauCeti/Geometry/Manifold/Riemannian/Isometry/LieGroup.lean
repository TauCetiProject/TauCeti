/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CompactUnitary
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.CompactOpen
import TauCeti.Geometry.Diffeomorphism.NoSmallSubgroups

/-!
# A Lie-group structure on the isometries of a closed Riemannian manifold

The compact-open topology on metric isometries controls coordinate derivatives via
`IsometryEquiv.continuous_toRiemannianIsometry`. Thus no-small-subgroups for the diffeomorphism
group passes to the metric isometries. Compactness then supplies a Lie-group structure in the
original compact-open topology. No connectedness assumption is needed.

This is the Lie-group existence part of the Myers–Steenrod theorem (S. B. Myers and N. E.
Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of Math. (2) 40 (1939),
400–416).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold TauCeti.DiffeomorphWeakWhitney TauCeti.RiemannianIsometryWeakWhitney

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [hfd : FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [hB : I.Boundaryless]
  (M : Type*) [EMetricSpace M] [hchart : ChartedSpace H M] [hM : IsManifold I ∞ M] [CompactSpace M]
  [hg : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [hcg : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [hdist : IsRiemannianManifold I M]

include I hfd hB hchart hM hg hcg hdist

/-- The isometries of the Riemannian extended distance of a closed manifold have no small
subgroups in the compact-open topology. -/
theorem hasNoSmallSubgroups_isometryEquiv : HasNoSmallSubgroups (M ≃ᵢ M) := by
  let e := RiemannianIsometry.isometryEquivContinuousMulEquiv I M
  let f := (RiemannianIsometry.toDiff (I := I) (M := M)).comp e.symm.toMonoidHom
  have hcont : Continuous f :=
    (RiemannianIsometry.isEmbedding_toDiffeomorph.continuous.comp e.symm.continuous).congr
      (fun x ↦ (RiemannianIsometry.toDiff_apply (e.symm x)).symm)
  exact (Diffeomorph.hasNoSmallSubgroups_weakWhitney (by simp)).of_injective f hcont.continuousAt
    (RiemannianIsometry.toDiff_injective.comp e.symm.injective)

/-- The isometries of the Riemannian extended distance of a closed manifold admit a
finite-dimensional smooth Lie-group atlas compatible with the compact-open topology. -/
theorem exists_chartedSpace_isometryEquiv_lieGroup :
    ∃ (d : ℕ) (atlas : ChartedSpace (EuclideanSpace ℝ (Fin d)) (M ≃ᵢ M)),
      letI := atlas
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (M ≃ᵢ M) :=
  Lie.HasNoSmallSubgroups.exists_lieGroup (hasNoSmallSubgroups_isometryEquiv I M)

end TauCeti
