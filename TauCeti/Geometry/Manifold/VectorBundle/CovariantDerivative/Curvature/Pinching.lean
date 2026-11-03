/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ExteriorSquare
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
import TauCeti.Analysis.InnerProductSpace.CourantFischer
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Curvature-operator bounds and Ricci curvature

The curvature endomorphism on the exterior square has convention
`⟪Rop(u ∧ v), w ∧ z⟫ = ⟪R(u,v)z,w⟫`. Contracting it in an orthonormal tangent basis
recovers the Ricci tensor. Consequently a quadratic-form lower bound `Rop ≥ α Id` gives
`Ric(u,u) ≥ (n - 1) α |u|²`, and an upper bound gives the reverse inequality.
These statements include dimensions zero and one; no two-plane existence is assumed.

For a metric-compatible torsion-free connection the endomorphism is self-adjoint.
Bounds on all its eigenvalues therefore give the same Ricci bounds, using the spectral
diagonalization of the entire exterior square. Bounds on diagonal entries in a wedge basis
alone are not sufficient. This is the Ricci input in curvature-operator pinching arguments.

The construction uses `CovariantDerivative.curvatureEndomorphism`, its pure-wedge pairing,
and `CovariantDerivative.ricciTensor_eq_sum_inner`. The spectral step uses
`LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices` and its upper-bound counterpart.

## References

* P. Petersen, *Riemannian Geometry*, third edition, Chapter 9 (curvature operators and
  curvature pinching).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- Ricci curvature is the contraction of the curvature endomorphism against the wedges
`eᵢ ∧ u` and `eᵢ ∧ v` in any orthonormal tangent basis. No torsion hypothesis is needed. -/
theorem ricciTensor_eq_sum_inner_curvatureEndomorphism {ι : Type*} [Fintype ι]
    (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = ∑ i,
      ⟪cov.curvatureEndomorphism hcov x (exteriorPower.ιMulti ℝ 2 ![b i, u]),
        exteriorPower.ιMulti ℝ 2 ![b i, v]⟫ := by
  rw [cov.ricciTensor_eq_sum_inner x b]
  simp only [cov.inner_curvatureEndomorphism_ιMulti, Matrix.cons_val_zero,
    Matrix.cons_val_one, real_inner_comm]

/-- A lower quadratic-form bound on the whole curvature endomorphism gives the sharp
Ricci lower bound. The metric connection need not be torsion-free. -/
theorem le_ricciTensor_self_of_le_curvatureEndomorphism (x : M) {α : ℝ}
    (hα : ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      α * ‖z‖ ^ 2 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫)
    (u : TangentSpace I x) :
    ((Module.finrank ℝ E : ℝ) - 1) * α * ‖u‖ ^ 2 ≤ cov.ricciTensor x u u := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    hα (exteriorPower.ιMulti ℝ 2 ![b i, u])
  rw [← cov.ricciTensor_eq_sum_inner_curvatureEndomorphism hcov x b] at hs
  rw [← Finset.mul_sum, b.sum_norm_sq_ιMulti_two] at hs
  simpa only [Fintype.card_fin, TauCeti.finrank_tangentSpace, mul_assoc, mul_left_comm] using hs

/-- An upper quadratic-form bound on the whole curvature endomorphism gives the sharp
Ricci upper bound. The metric connection need not be torsion-free. -/
theorem ricciTensor_self_le_of_curvatureEndomorphism_le (x : M) {β : ℝ}
    (hβ : ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      ⟪cov.curvatureEndomorphism hcov x z, z⟫ ≤ β * ‖z‖ ^ 2)
    (u : TangentSpace I x) :
    cov.ricciTensor x u u ≤ ((Module.finrank ℝ E : ℝ) - 1) * β * ‖u‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    hβ (exteriorPower.ιMulti ℝ 2 ![b i, u])
  rw [← cov.ricciTensor_eq_sum_inner_curvatureEndomorphism hcov x b] at hs
  rw [← Finset.mul_sum, b.sum_norm_sq_ιMulti_two] at hs
  simpa only [Fintype.card_fin, TauCeti.finrank_tangentSpace, mul_assoc, mul_left_comm] using hs

/-- If every eigenvalue of the curvature endomorphism is at least `α`, then
`Ric ≥ (n - 1) α g`. This uses self-adjointness on the entire exterior square. -/
theorem le_ricciTensor_self_of_le_eigenvalues_curvatureEndomorphism
    (ht : cov.torsion = 0) (x : M) {α : ℝ}
    (hα : ∀ μ : ℝ, (cov.curvatureEndomorphism hcov x).HasEigenvalue μ → α ≤ μ)
    (u : TangentSpace I x) :
    ((Module.finrank ℝ E : ℝ) - 1) * α * ‖u‖ ^ 2 ≤ cov.ricciTensor x u u := by
  apply cov.le_ricciTensor_self_of_le_curvatureEndomorphism hcov x _ u
  intro z
  have hA := cov.isSymmetric_curvatureEndomorphism hcov ht x
  simpa only [RCLike.re_to_real] using
    hA.le_re_inner_apply_self_of_mem_spanIndices rfl
      (s := Set.univ) (fun i _ ↦ hα _ (hA.hasEigenvalue_eigenvalues rfl i))
      (x := z) (by simp)

/-- If every eigenvalue of the curvature endomorphism is at most `β`, then
`Ric ≤ (n - 1) β g`. This uses self-adjointness on the entire exterior square. -/
theorem ricciTensor_self_le_of_eigenvalues_curvatureEndomorphism_le
    (ht : cov.torsion = 0) (x : M) {β : ℝ}
    (hβ : ∀ μ : ℝ, (cov.curvatureEndomorphism hcov x).HasEigenvalue μ → μ ≤ β)
    (u : TangentSpace I x) :
    cov.ricciTensor x u u ≤ ((Module.finrank ℝ E : ℝ) - 1) * β * ‖u‖ ^ 2 := by
  apply cov.ricciTensor_self_le_of_curvatureEndomorphism_le hcov x _ u
  intro z
  have hA := cov.isSymmetric_curvatureEndomorphism hcov ht x
  simpa only [RCLike.re_to_real] using
    hA.re_inner_apply_self_le_of_mem_spanIndices rfl
      (s := Set.univ) (fun i _ ↦ hβ _ (hA.hasEigenvalue_eigenvalues rfl i))
      (x := z) (by simp)

end CovariantDerivative
