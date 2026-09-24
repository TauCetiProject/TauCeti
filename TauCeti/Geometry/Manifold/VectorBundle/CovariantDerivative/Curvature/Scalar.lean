/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci

/-!
# Scalar curvature of a smooth connection

The scalar curvature of a connection on a Riemannian tangent bundle is the metric trace of its
Ricci tensor. The definition is basis-free; in an orthonormal basis it is the sum of the diagonal
Ricci curvatures. Applying it to the Levi-Civita connection gives the scalar curvature of a
Riemannian manifold.

As for `CovariantDerivative.ricciTensor`, the connection need not preserve the metric or be torsion
free. The metric need not vary smoothly, because this file concerns the pointwise contraction.
Compactness and absence of boundary are not required.

For the convention
`R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)`, the scalar curvature is `n (n - 1) κ` in
real dimension `n`.

The definition and convention follow J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 7.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The scalar curvature of a smooth connection on the tangent bundle, defined as the metric
trace of its Ricci tensor. -/
def scalarCurvature (x : M) : ℝ :=
  TauCeti.bilinFormTrace (cov.ricciTensor x)

/-- Scalar curvature is the metric trace of Ricci curvature. -/
theorem scalarCurvature_apply (x : M) :
    cov.scalarCurvature x = TauCeti.bilinFormTrace (cov.ricciTensor x) :=
  (rfl)

/-- In an orthonormal basis, scalar curvature is the sum of the diagonal Ricci curvatures. -/
theorem scalarCurvature_eq_sum {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) :
    cov.scalarCurvature x = ∑ j, cov.ricciTensor x (b j) (b j) := by
  rw [scalarCurvature_apply]
  exact TauCeti.bilinFormTrace_eq_sum _ b

/-- In an orthonormal basis, scalar curvature is the double contraction of the curvature
tensor. The inner sum contracts the curvature output against its first argument; the outer sum
contracts the two Ricci arguments. -/
theorem scalarCurvature_eq_sum_inner_curvatureTensor {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) :
    cov.scalarCurvature x =
      ∑ j, ∑ k, inner ℝ (b k) (curvature x (b k) (b j) (b j)) := by
  rw [scalarCurvature_eq_sum cov x b]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact ricciTensor_eq_sum_inner cov x b (b j) (b j)

/-- Vanishing Ricci curvature implies vanishing scalar curvature. -/
theorem scalarCurvature_eq_zero_of_ricciTensor_eq_zero (x : M)
    (h : cov.ricciTensor x = 0) : cov.scalarCurvature x = 0 := by
  rw [scalarCurvature_apply, h, map_zero]

/-- A point with zero curvature tensor has zero scalar curvature. -/
theorem scalarCurvature_eq_zero_of_curvatureTensor_eq_zero (x : M)
    (h : curvature x = 0) : cov.scalarCurvature x = 0 :=
  scalarCurvature_eq_zero_of_ricciTensor_eq_zero cov x
    (ricciTensor_eq_zero_of_curvatureTensor_eq_zero cov x h)

/-- If Ricci curvature is a scalar multiple of the metric, scalar curvature is that scalar times
the real dimension. -/
theorem scalarCurvature_eq_of_ricciTensor_eq_smul_inner (x : M) (c : ℝ)
    (h : cov.ricciTensor x = c • innerₗ (TangentSpace I x)) :
    cov.scalarCurvature x = (Module.finrank ℝ (TangentSpace I x) : ℝ) * c := by
  rw [scalarCurvature_apply, h, map_smul, TauCeti.bilinFormTrace_inner]
  simp only [smul_eq_mul]
  ring

/-- Contracting curvature of the form `R(w,u)v = B(u,v)w - B(w,v)u` gives scalar curvature
`(dim - 1) trace(B)`. -/
theorem scalarCurvature_eq_of_curvatureTensor_eq_smul_sub (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (h : ∀ w u v, curvature x w u v = B u v • w - B w v • u) :
    cov.scalarCurvature x =
      (Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) * TauCeti.bilinFormTrace B := by
  rw [scalarCurvature_apply, ricciTensor_eq_of_curvatureTensor_eq_smul_sub cov x B h,
    map_smul]
  simp only [smul_eq_mul]

/-- The scalar curvature of the constant-curvature model
`R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)` is `n (n - 1) κ`. -/
theorem scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub (x : M) (k : ℝ)
    (h : ∀ w u v, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.scalarCurvature x = (Module.finrank ℝ (TangentSpace I x) : ℝ) *
      (Module.finrank ℝ (TangentSpace I x) - 1) * k := by
  have hmodel : ∀ w u v, curvature x w u v =
      (k • innerₗ (TangentSpace I x)) u v • w -
        (k • innerₗ (TangentSpace I x)) w v • u := by
    intro w u v
    rw [h w u v]
    simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_sub, smul_smul, smul_eq_mul]
  rw [scalarCurvature_eq_of_curvatureTensor_eq_smul_sub cov x
    (k • innerₗ (TangentSpace I x)) hmodel, map_smul,
    TauCeti.bilinFormTrace_inner]
  simp only [smul_eq_mul]
  ring

end CovariantDerivative
