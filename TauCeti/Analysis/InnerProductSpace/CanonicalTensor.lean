/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Analysis.InnerProductSpace.Nondegenerate

/-!
# Inverse-Gram expansions of the canonical covariant tensor

Mathlib's `InnerProductSpace.canonicalCovariantTensor W : W ⊗[ℝ] W` represents the metric of a
finite-dimensional real inner product space `W` as a covariant 2-tensor, expanding in any
orthonormal basis `v` as `∑ i, v i ⊗ₜ v i` (`InnerProductSpace.canonicalCovariantTensor_eq_sum`).

In coordinate geometry on a Riemannian manifold, local chart frames are bases that are generally not
orthogonal. This file expresses `canonicalCovariantTensor W` in an arbitrary basis `b` of `W`
through its metric dual basis and the inverse Gram matrix `(Matrix.gram ℝ b)⁻¹`, and records the
resulting `gⁱʲ B(bᵢ, bⱼ)` contraction formula for bilinear maps into an arbitrary real module.

## Main results

* `InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis`: in any basis `b`,
  `canonicalCovariantTensor W = ∑ i, b i ⊗ₜ b♯ i`, where `b♯` is the metric dual basis.
* `InnerProductSpace.canonicalCovariantTensor_eq_sum_inv_gram`: in any basis `b`,
  `canonicalCovariantTensor W = ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • (b i ⊗ₜ b j)`.
* `TensorProduct.lift_canonicalCovariantTensor_eq_sum`: contracting a vector-valued bilinear map
  against `canonicalCovariantTensor W` sums its diagonal in any orthonormal basis.
* `TensorProduct.lift_canonicalCovariantTensor_eq_sum_inv_gram`: contracting a vector-valued
  bilinear map against `canonicalCovariantTensor W` computes `∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j •
  B (b i) (b j)` in any basis `b`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (raising indices and metric traces in local frames).
-/

public section

open scoped InnerProductSpace TensorProduct

variable {W V ι : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [AddCommGroup V] [Module ℝ V] [Fintype ι]

/-- In an arbitrary basis `b` of `W`, the canonical covariant tensor is `∑ i, b i ⊗ₜ b♯ i`, where
`b♯` is the dual basis with respect to the inner product. -/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis [DecidableEq ι]
    (b : Module.Basis ι ℝ W) :
    InnerProductSpace.canonicalCovariantTensor W =
      ∑ i, b i ⊗ₜ[ℝ] LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner b i := by
  let d := LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner b
  let v := stdOrthonormalBasis ℝ W
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum W v]
  calc ∑ k, v k ⊗ₜ[ℝ] v k
      = ∑ k, (∑ i, ⟪d i, v k⟫_ℝ • b i) ⊗ₜ[ℝ] v k := by
        simp only [d, b.inner_dualBasis_left, b.sum_repr]
    _ = ∑ i, b i ⊗ₜ[ℝ] ∑ k, ⟪v k, d i⟫_ℝ • v k := by
        simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul,
          real_inner_comm (d _)]
        exact Finset.sum_comm
    _ = ∑ i, b i ⊗ₜ[ℝ] d i := by simp only [v.sum_repr']

/-- In an arbitrary basis `b` of `W`, the canonical covariant tensor expands with coefficients given
by the inverse Gram matrix `(Matrix.gram ℝ b)⁻¹`:
`canonicalCovariantTensor W = ∑ i, ∑ j, (G⁻¹)ᵢⱼ • (bᵢ ⊗ₜ bⱼ)`. -/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum_inv_gram [DecidableEq ι]
    (b : Module.Basis ι ℝ W) :
    InnerProductSpace.canonicalCovariantTensor W =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • (b i ⊗ₜ[ℝ] b j) := by
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Module.Basis.dualBasis_innerₗ_eq_sum, TensorProduct.tmul_sum]
  simp only [TensorProduct.tmul_smul]

/-- Contracting a vector-valued bilinear map against `canonicalCovariantTensor W` sums its diagonal
entries in any orthonormal basis of `W`. -/
theorem TensorProduct.lift_canonicalCovariantTensor_eq_sum (B : W →ₗ[ℝ] W →ₗ[ℝ] V)
    (v : OrthonormalBasis ι ℝ W) :
    TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor W) =
      ∑ i, B (v i) (v i) := by
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum W v, map_sum]
  simp only [TensorProduct.lift.tmul]

/-- Contracting a vector-valued bilinear map `B` against `canonicalCovariantTensor W` in an
arbitrary basis `b` contracts `B (b i) (b j)` against the inverse Gram matrix `(Matrix.gram ℝ b)⁻¹`,
giving the coordinate trace `∑ i, ∑ j, (G⁻¹)ᵢⱼ • B (b i) (b j)`. -/
theorem TensorProduct.lift_canonicalCovariantTensor_eq_sum_inv_gram [DecidableEq ι]
    (B : W →ₗ[ℝ] W →ₗ[ℝ] V) (b : Module.Basis ι ℝ W) :
    TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor W) =
      ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • B (b i) (b j) := by
  rw [InnerProductSpace.canonicalCovariantTensor_eq_sum_inv_gram b, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum]
  simp only [map_smul, TensorProduct.lift.tmul]

end
