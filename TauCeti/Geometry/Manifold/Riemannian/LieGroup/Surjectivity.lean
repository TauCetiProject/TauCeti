/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.LieGroup.Geodesic
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.LeftInvariant

/-!
# Surjectivity of the exponential for an invariant metric

On a connected real Lie group, a smooth left-invariant Riemannian metric is complete. The
minimizing-geodesic theorem reaches every group element. When the inner product at the identity
is ad-invariant, the Riemannian and Lie exponentials agree, proving surjectivity of the Lie
exponential.

The model is boundaryless, as in the minimizing-geodesic theorem. Compactness is not assumed:
these results apply whenever the invariant metric is available.

## Main results

* `TauCeti.Manifold.mulInvariantExp_surjective_of_invariantMetric`: the tangent-space version.
* `TauCeti.Manifold.lieExp_surjective_of_invariantMetric`: the derivation-based version.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Remark 3.8, for the compact-group application.
* The minimizing-geodesic argument is reused from
  `TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing`.
-/

public section

open Bundle Manifold Set VectorField
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [RiemannianBundle (fun g : G ↦ TangentSpace I g)]
  [IsContMDiffRiemannianBundle I ∞ E (fun g : G ↦ TangentSpace I g)]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable
  (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
    inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
  (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
    (innerₗ (TangentSpace I (1 : G))))

include hL had

/-- An ad-invariant left-invariant metric makes the tangent-space Lie exponential surjective
on a connected Lie group with boundaryless model. -/
theorem mulInvariantExp_surjective_of_invariantMetric [ConnectedSpace G] :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Function.Surjective (mulInvariantExp (I := I) (G := G)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : IsContinuousRiemannianBundle E (fun g : G ↦ TangentSpace I g) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
      (F := E) (V := fun g : G ↦ TangentSpace I g)
  let _ : MetricSpace G := TauCeti.MetricSpace.ofRiemannianMetric I G
  have := completeSpace_ofRiemannianMetric_of_inner_mulInvariantVectorField hL
  intro g
  obtain ⟨a, ha, -⟩ := exists_riemannianExp_eq_and_norm_eq_dist
    (expDomain_eq_univ_of_completeSpace (I := I) (1 : G)) g
  exact ⟨a, (riemannianExp_one_eq_mulInvariantExp hL had a).symm.trans ha⟩

/-- An ad-invariant left-invariant metric makes the derivation-based Lie exponential surjective
on a connected Lie group with boundaryless model. -/
theorem lieExp_surjective_of_invariantMetric [ConnectedSpace G] :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Function.Surjective (lieExp (I := I) (G := G)) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  intro g
  obtain ⟨a, ha⟩ := mulInvariantExp_surjective_of_invariantMetric hL had g
  obtain ⟨X, hX⟩ := (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint).surjective a
  exact ⟨X, by rw [lieExp_eq_mulInvariantExp, hX, ha]⟩

end TauCeti.Manifold
