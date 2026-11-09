/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondBianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The second Bianchi identity with torsion

For a smooth connection on a vector bundle, differentiating its curvature with an arbitrary
connection on the tangent bundle gives

`(∇_u R)(v,w) + (∇_v R)(w,u) + (∇_w R)(u,v)
  = -R(T(u,v),w) - R(T(v,w),u) - R(T(w,u),v)`.

Here `T(u,v) = ∇ᵀ_u v - ∇ᵀ_v u - [u,v]` is the native torsion tensor. The sign uses
`R(u,v) = [∇_u,∇_v] - ∇_[u,v]`. This is the tensor formula for the covariant exterior
closedness of curvature when the auxiliary tangent connection has torsion. It includes the
usual differential Bianchi identity when torsion vanishes at the point in question.

The auxiliary tangent connection need not be smooth: only its values at the point enter the
formula. No metric is needed. The proof uses the torsion-independent identity
`CovariantDerivative.curvatureOperator_commutator_cyclic_eq_zero` and the characteristic
evaluation formula for `CovariantDerivative.derivCurvatureTensor`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Chapter III
  (the Bianchi identities for connections with torsion).
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **The second Bianchi identity with torsion.** The cyclic covariant derivative of curvature
is minus the cyclic curvature contraction with the torsion of the tangent connection. The
identity is an equality of endomorphisms of the bundle fibre. -/
theorem derivCurvatureTensor_cyclic_eq_neg_torsion (x : M) (u v w : TangentSpace I x) :
    cov.derivCurvatureTensor covT x u v w + cov.derivCurvatureTensor covT x v w u +
        cov.derivCurvatureTensor covT x w u v =
      -(cov.curvatureTensor x (covT.torsion x u v) w +
        cov.curvatureTensor x (covT.torsion x v w) u +
        cov.curvatureTensor x (covT.torsion x w u) v) := by
  ext s
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F ∞ s
  have h := cov.curvatureOperator_commutator_cyclic_eq_zero hX hY hZ hσ x
  -- Express the commutators in terms of the pointwise tensor, leaving its derivative intact.
  rw [← cov.curvatureTensor_apply x hY hZ (cov.contMDiff_apply hX hσ),
    ← cov.curvatureTensor_apply x hZ hX (cov.contMDiff_apply hY hσ),
    ← cov.curvatureTensor_apply x hX hY (cov.contMDiff_apply hZ hσ),
    ← cov.curvatureTensor_apply x hX (contMDiff_mlieBracket hY hZ) hσ,
    ← cov.curvatureTensor_apply x hY (contMDiff_mlieBracket hZ hX) hσ,
    ← cov.curvatureTensor_apply x hZ (contMDiff_mlieBracket hX hY) hσ] at h
  simp only [LinearMap.add_apply, LinearMap.neg_apply,
    derivCurvatureTensor_apply cov covT x _ hY hZ hσ,
    derivCurvatureTensor_apply cov covT x _ hZ hX hσ,
    derivCurvatureTensor_apply cov covT x _ hX hY hσ,
    covT.torsion_apply (hX.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x),
    covT.torsion_apply (hY.mdifferentiable (by simp) x) (hZ.mdifferentiable (by simp) x),
    covT.torsion_apply (hZ.mdifferentiable (by simp) x) (hX.mdifferentiable (by simp) x),
    map_sub, LinearMap.sub_apply]
  -- Skew-symmetry pairs the six connection corrections with the three torsion terms.
  rw [cov.curvatureTensor_antisymm x (Y x) (covT Z x (X x)),
    cov.curvatureTensor_antisymm x (Z x) (covT X x (Y x)),
    cov.curvatureTensor_antisymm x (X x) (covT Y x (Z x))]
  simp only [LinearMap.neg_apply]
  rw [cov.curvatureTensor_antisymm x (X x) (mlieBracket I Y Z x),
    cov.curvatureTensor_antisymm x (Y x) (mlieBracket I Z X x),
    cov.curvatureTensor_antisymm x (Z x) (mlieBracket I X Y x)] at h
  simp only [LinearMap.neg_apply] at h
  linear_combination (norm := module) h

end CovariantDerivative
