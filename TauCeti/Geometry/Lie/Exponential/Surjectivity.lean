/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Subgroup.Embedded
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.AdjointInvariant
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.Surjectivity

/-!
# Surjectivity of the exponential for compact connected Lie groups

A compact Lie group has an adjoint-invariant positive form on its Lie algebra. Transporting
that form to the tangent space at the identity gives a smooth left-invariant metric with
ad-invariant inner product. The geodesic criterion then makes the Lie exponential surjective
when the group is connected. No metric is assumed in the statement.

The conclusion applies to any real model with corners. The closed-subgroup theorem gives the
whole subgroup a boundaryless vector-space model with its inherited topology; exponential
naturality along its smooth inclusion transfers the metric conclusion to the original model.

## Main results

* `TauCeti.Lie.lieExp_surjective_of_compact_connected`:
  every element is the exponential of a derivation.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Corollary 4.48.
  The proof here uses the invariant-metric route, rather than Knapp's maximal-torus argument.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Theorem 3.7(4) and Remark 3.8.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [ConnectedSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- Compact-connected exponential surjectivity in a boundaryless model. -/
private theorem lieExp_surjective_of_compact_connected_of_boundaryless [I.Boundaryless] :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Function.Surjective (lieExp (I := I) (G := G)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  obtain ⟨b, hb_symm, hb_pos, hb_ad⟩ :=
    exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant (I := I) (G := G)
  let metric := leftInvariantMetric (m := ∞) (n := ∞) (by simp)
    b hb_symm hb_pos
  let : RiemannianBundle (fun x : G ↦ TangentSpace I x) := ⟨metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun x : G ↦ TangentSpace I x) :=
    Bundle.instIsContMDiffRiemannianBundle metric
  exact TauCeti.Manifold.lieExp_surjective_of_invariantMetric
    (inner_mulInvariantVectorField_leftInvariantMetric
      (m := ∞) (n := ∞) le_rfl b hb_symm hb_pos)
    (ContinuousLinearMap.lieInvariant_inner_leftInvariantMetric b hb_symm hb_pos hb_ad)

/-- The Lie exponential of a compact connected finite-dimensional real Lie group is surjective. -/
theorem lieExp_surjective_of_compact_connected :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Function.Surjective (lieExp (I := I) (G := G)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  -- Cartan's theorem supplies a boundaryless model for the whole subgroup.
  let K : Subgroup G := ⊤
  let L := (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨d⟩ := nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed
    (I := I) (K := K) (by simp [K])
  let _ : ChartedSpace L K := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, L) ∞ K := d.lieGroup
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp
    (by simpa only [K, Subgroup.coe_top] using (isCompact_univ : IsCompact (Set.univ : Set G)))
  let _ : ConnectedSpace K := isConnected_iff_connectedSpace.mp
    (by simpa only [K, Subgroup.coe_top] using (isConnected_univ : IsConnected (Set.univ : Set G)))
  let f : ContMDiffMonoidMorphism 𝓘(ℝ, L) I ∞ K G := ⟨K.subtype, d.contMDiff_subtypeVal⟩
  intro g
  obtain ⟨X, hX⟩ := (lieExp_surjective_of_compact_connected_of_boundaryless (I := 𝓘(ℝ, L)))
    (⟨g, Subgroup.mem_top g⟩ : K)
  -- The inclusion's Lie map sends the native logarithm to a logarithm in the original model.
  refine ⟨lieMap f X, ?_⟩
  rw [← map_lieExp f X, hX]
  rfl


end TauCeti.Lie
