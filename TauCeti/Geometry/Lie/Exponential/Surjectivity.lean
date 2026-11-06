/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
-- Supplies carrier boundarylessness in the public exponential statement.
public import TauCeti.Geometry.Lie.Interior
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Manifold.ModelTransport.LieGroup
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.AdjointInvariant
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.Surjectivity

/-!
# Surjectivity of the exponential for compact connected Lie groups

A compact finite-dimensional real Lie group has an adjoint-invariant positive form on its
Lie algebra. Transporting that form to the tangent space at the identity gives a smooth
left-invariant metric with
ad-invariant inner product. The geodesic criterion then makes the Lie exponential surjective
when the group is connected. No metric is assumed in the statement.

The model with corners is arbitrary; only the carrier must be a Lie group. No global
surjectivity of the model is assumed.

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

/-- The Lie exponential of a compact connected finite-dimensional real Lie group is surjective,
for an arbitrary model with corners. -/
theorem lieExp_surjective_of_compact_connected :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Function.Surjective (lieExp (I := I) (G := G)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : CompactSpace (BoundarylessModel I G) := (BoundarylessModel.homeomorph I G).compactSpace
  let _ : ConnectedSpace (BoundarylessModel I G) :=
    (BoundarylessModel.homeomorph I G).connectedSpace_iff.mp inferInstance
  let _ : T2Space (BoundarylessModel I G) := (𝓘(ℝ, E)).t2Space_of_lieGroup ∞
  let φ := BoundarylessModel.contMDiffMonoidMorphismSymm I G ∞
  dsimp only
  intro g
  obtain ⟨X, hX⟩ := (lieExp_surjective_of_compact_connected_of_boundaryless
    (I := 𝓘(ℝ, E)) (G := BoundarylessModel I G)) (BoundarylessModel.homeomorph I G g)
  refine ⟨lieMap φ X, ?_⟩
  calc
    lieExp (lieMap φ X) = φ (lieExp X) := (map_lieExp φ X).symm
    _ = φ (BoundarylessModel.homeomorph I G g) := congrArg φ hX
    _ = g := by
      simp only [φ, BoundarylessModel.coe_contMDiffMonoidMorphismSymm,
        BoundarylessModel.coe_continuousMulEquiv_symm, Homeomorph.symm_apply_apply]

end TauCeti.Lie
