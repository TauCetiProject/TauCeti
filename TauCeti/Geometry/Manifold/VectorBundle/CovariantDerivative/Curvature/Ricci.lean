/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Ricci curvature of a smooth connection

The Ricci tensor of a connection on the tangent bundle is the bilinear form
`Ric(u,v) = trace (w ↦ R(w,u)v)`. The trace makes this definition independent of a choice
of basis. Applying it to the Levi-Civita connection gives Riemannian Ricci curvature.
A general connection need not have symmetric Ricci curvature.

We work with a `RiemannianBundle` on the tangent bundle to supply the fibre norms used
by `curvatureTensor`. The connection need not preserve this metric or be torsion free,
and the metric need not vary smoothly. Compactness and absence of boundary are not required.

We give the coordinate formula in any basis and the inner-product formula in an
orthonormal basis. The constant-curvature calculation fixes the sign convention:
`R(w,u)v = κ (⟪u,v⟫ w - ⟪w,v⟫ u)` gives `Ric = (dim - 1) κ g`.
Here the calculation is stated for any bilinear form in place of `κ g`.

The convention follows J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed.,
Springer GTM 176 (2018), Chapter 7. The curvature tensor being contracted is
`CovariantDerivative.curvatureTensor`, with convention
`R(X,Y)Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`.
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

-- Fix the fibre norm before elaborating the contraction: tangent spaces deliberately have
-- no default norm, and their implementation as copies of E otherwise selects the model norm.
local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)
  (fiberNorm := fun x : M ↦ (inferInstance : NormedAddCommGroup (TangentSpace I x)))

/-- The Ricci tensor of a smooth connection on the tangent bundle, defined by
`Ric(u,v) = trace (w ↦ R(w,u)v)`. Metric compatibility and vanishing torsion are not
assumed; symmetry is not asserted for an arbitrary connection. -/
def ricciTensor (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.lflip.toLinearMap.comp (curvature x).flip).compr₂
    (LinearMap.trace ℝ (TangentSpace I x))

/-- The defining trace formula for Ricci curvature. The two flips leave the first
curvature argument free, so it is this argument that is traced against the output. -/
theorem ricciTensor_apply (x : M) (u v : TangentSpace I x) :
    cov.ricciTensor x u v =
      LinearMap.trace ℝ (TangentSpace I x) (((curvature x).flip u).flip v) :=
  (rfl)

/-- Ricci curvature in an arbitrary basis: sum the diagonal coefficients of
`w ↦ R(w,u)v`. The basis need not be orthogonal. -/
theorem ricciTensor_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : Module.Basis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = ∑ i, b.repr (curvature x (b i) u v) i := by
  classical
  rw [ricciTensor_apply, LinearMap.trace_eq_matrix_trace ℝ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

/-- In an orthonormal basis, Ricci curvature is the sum of the corresponding inner
products for the given fibre metric. -/
theorem ricciTensor_eq_sum_inner {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = ∑ i, inner ℝ (b i) (curvature x (b i) u v) := by
  rw [ricciTensor_apply, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- A point with zero curvature tensor has zero Ricci tensor. -/
@[simp]
theorem ricciTensor_eq_zero_of_curvatureTensor_eq_zero (x : M)
    (h : curvature x = 0) : cov.ricciTensor x = 0 := by
  ext u v
  have hz : ((curvature x).flip u).flip v = 0 := by
    ext w
    simp [h]
  rw [ricciTensor_apply, hz, map_zero]
  rfl

/-- Contracting curvature of the form `R(w,u)v = B(u,v)w - B(w,v)u` gives
`Ric = (dim - 1) B`. In particular, the constant-curvature model with `B = κ g`
has Ricci tensor `(dim - 1) κ g`, with the sign fixed by the curvature convention. -/
theorem ricciTensor_eq_of_curvatureTensor_eq_smul_sub (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (h : ∀ w u v, curvature x w u v = B u v • w - B w v • u) :
    cov.ricciTensor x = (Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) • B := by
  ext u v
  have hmap : ((curvature x).flip u).flip v =
      B u v • LinearMap.id - (B.flip v).smulRight u := by
    ext w
    exact h w u v
  rw [ricciTensor_apply, hmap, map_sub, map_smul, LinearMap.trace_id,
    LinearMap.trace_smulRight]
  simp only [LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul]
  ring

end CovariantDerivative
