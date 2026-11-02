/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Ricci identity for the second covariant derivative

Let `∇` be a smooth connection on a vector bundle `V` and `∇ᵀ` a connection on the tangent
bundle, and let `∇²σ(X, Y) = ∇_X (∇_Y σ) - ∇_{∇ᵀ_X Y} σ` be the second covariant derivative of a
smooth section `σ` of `V` (`CovariantDerivative.secondCovariantDerivative`).

The **Ricci identity** expresses the failure of `∇²σ` to be symmetric through the curvature `R`
of `∇` and the torsion `T` of `∇ᵀ`:

`∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ - ∇_{T(u, v)} σ`,

where `T(X, Y) = ∇ᵀ_X Y - ∇ᵀ_Y X - [X, Y]` is Mathlib's `CovariantDerivative.torsion`.
For a torsion-free `∇ᵀ`, such as a Levi-Civita connection, the torsion term disappears and the
antisymmetric part of `∇²σ` is the curvature `R(u, v) σ`. For `V` the tangent bundle this is the
Ricci identity for vector fields. It is the rule for commuting covariant derivatives used in
Bochner and Weitzenböck formulas.

## Main results

* `CovariantDerivative.secondCovariantDerivative_sub_swap`: the Ricci identity with its torsion
  correction.
* `CovariantDerivative.secondCovariantDerivative_sub_swap_of_isTorsionFree`: the Ricci identity
  `∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ` for a torsion-free connection on the tangent bundle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the Ricci identities).
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {σ : Π y : M, V y}
  [FiniteDimensional ℝ E] [T2Space M]

section RicciIdentity

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- **The Ricci identity**, with its torsion correction. For a smooth section `σ`, the
antisymmetric part of its second covariant derivative is the curvature of `∇` applied to `σ`,
corrected by the covariant derivative of `σ` along the torsion of `∇ᵀ`:

`∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ - ∇_{T(u, v)} σ`. -/
theorem secondCovariantDerivative_sub_swap (hσ : CMDiff ∞ (T% σ)) (x : M)
    (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v - cov.secondCovariantDerivative covT σ x v u =
      cov.curvatureTensor x u v (σ x) - cov σ x (covT.torsion x u v) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  rw [secondCovariantDerivative_apply cov covT hσ x hY,
    secondCovariantDerivative_apply cov covT hσ x hX, curvatureTensor_apply cov x hX hY hσ,
    curvatureOperator_apply,
    covT.torsion_apply (hX.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)]
  simp only [map_sub]
  abel

/-- **The Ricci identity.** For a torsion-free connection `∇ᵀ` on the tangent bundle, the
antisymmetric part of the second covariant derivative of a smooth section `σ` is the curvature
of `∇` applied to `σ`: `∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ`. -/
theorem secondCovariantDerivative_sub_swap_of_isTorsionFree (ht : covT.IsTorsionFree)
    (hσ : CMDiff ∞ (T% σ)) (x : M) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v - cov.secondCovariantDerivative covT σ x v u =
      cov.curvatureTensor x u v (σ x) := by
  rw [secondCovariantDerivative_sub_swap cov covT hσ x u v,
    (isTorsionFree_iff_torsion_eq_zero covT).1 ht]
  simp

/-- If the torsion of `∇ᵀ` and the curvature of `∇` both vanish at `x`, then the second
covariant derivative of every section at `x` is symmetric. (For a section that is not smooth,
both sides are the junk value `0`.) -/
theorem secondCovariantDerivative_comm_of_curvatureTensor_eq_zero {x : M}
    (hT : covT.torsion x = 0) (hR : cov.curvatureTensor x = 0) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v = cov.secondCovariantDerivative covT σ x v u := by
  by_cases hσ : CMDiff ∞ (T% σ)
  · rw [← sub_eq_zero, secondCovariantDerivative_sub_swap cov covT hσ x, hR, hT]
    simp
  · simp only [secondCovariantDerivative_of_not_contMDiff cov covT hσ, LinearMap.zero_apply]

end RicciIdentity

end CovariantDerivative
