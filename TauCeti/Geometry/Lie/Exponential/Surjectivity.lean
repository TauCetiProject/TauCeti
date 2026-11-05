/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.AdjointInvariant
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.Surjectivity

/-!
# Surjectivity of the exponential for compact connected Lie groups

A compact Lie group has an adjoint-invariant positive form on its Lie algebra. Transporting
that form to the tangent space at the identity gives a smooth left-invariant metric with
ad-invariant inner product. The geodesic criterion then makes the Lie exponential surjective
when the group is connected. No metric is assumed in the statement.

The model is boundaryless, as required by the minimizing-geodesic theorem used here.

## Main results

* `TauCeti.Lie.lieExp_surjective_of_compact_connected`:
  every element is the exponential of a derivation.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Corollary 4.48.
  The proof here uses the invariant-metric route, rather than Knapp's maximal-torus argument.
* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Remark 3.8.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G] [ConnectedSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- On a boundaryless model, the Lie exponential of a compact connected real Lie group is
surjective. -/
theorem lieExp_surjective_of_compact_connected :
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

end TauCeti.Lie
