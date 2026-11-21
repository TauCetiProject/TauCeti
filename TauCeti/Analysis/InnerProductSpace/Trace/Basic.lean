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
import TauCeti.LinearAlgebra.BilinearForm.Dual.Basis

/-!
# Metric trace of a bilinear map

This file defines the metric trace of a bilinear map `W × W → N`, with values in any real vector
space `N`, on a finite-dimensional real inner product space `W`. For `N = ℝ` this is the metric
trace of a bilinear form; for a vector-valued form, such as the second covariant derivative of a
section, it is again vector-valued. The definition contracts the form against Mathlib's canonical
covariant tensor, making it independent of any choice of basis.

## Main definitions

* `LinearMap.BilinMap.metricTrace`: the metric trace of a real bilinear map.

## Main statements

* `InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis`: in an arbitrary basis `b`, the
  canonical covariant tensor is `∑ᵢ bᵢ ⊗ b'ᵢ`, where `b'` is the dual basis of `b` for the inner
  product.
* `LinearMap.BilinMap.metricTrace_eq_sum`: in an orthonormal basis, the metric trace is the sum of
  the diagonal values.
* `LinearMap.BilinMap.metricTrace_eq_sum_dualBasis`: in an arbitrary basis, the metric trace pairs
  the basis with its metric dual basis.
* `LinearMap.BilinMap.metricTrace_eq_sum_inv_gram`: in an arbitrary basis, the metric trace
  contracts the form against the inverse Gram matrix of the basis.
* `LinearMap.BilinMap.metricTrace_flip`: the metric trace is invariant under transposing the
  arguments.
* `LinearMap.BilinMap.metricTrace_compr₂`: the metric trace commutes with a linear map applied to
  the values.
* `LinearMap.BilinMap.metricTrace_compl₁₂_linearIsometryEquiv`: the metric trace is invariant
  under pulling the form back along a linear isometric equivalence.
* `LinearMap.BilinMap.metricTrace_inner`: the metric trace of the inner product is the real
  dimension.
-/

public section

open LinearMap (BilinMap)
open scoped InnerProductSpace TensorProduct

/-- **The canonical covariant tensor in an arbitrary basis**: `∑ᵢ bᵢ ⊗ b'ᵢ`, where `b'` is the
dual basis of `b` for the inner product. The basis need not be orthonormal; for an orthonormal
basis `b' = b` and this is `InnerProductSpace.canonicalCovariantTensor_eq_sum`. -/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis (W : Type*)
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ W) :
    canonicalCovariantTensor W =
      ∑ i, b i ⊗ₜ[ℝ] LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner b i := by
  let v := stdOrthonormalBasis ℝ W
  -- The dual basis of an orthonormal basis is the basis itself.
  have hv (k) : LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner v.toBasis k =
      v k :=
    ext_inner_right ℝ fun w ↦ by
      rw [v.toBasis.inner_dualBasis_left, v.coe_toBasis_repr_apply, v.repr_apply_apply]
  rw [canonicalCovariantTensor_eq_sum W v]
  simpa [hv] using (TensorProduct.mk ℝ W W).sum_apply_dualBasis_eq TauCeti.nondegenerate_inner
    v.toBasis b

namespace LinearMap.BilinMap

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Type*} [AddCommMonoid N] [Module ℝ N]

/-- The metric trace of an `N`-valued bilinear map on `W`, obtained by contracting it against the
canonical covariant tensor of the inner product. -/
noncomputable def metricTrace : BilinMap ℝ W N →ₗ[ℝ] N :=
  (LinearMap.applyₗ (InnerProductSpace.canonicalCovariantTensor W)).comp
    (TensorProduct.uncurry (.id ℝ) W W N)

/-- The metric trace is evaluation on the canonical covariant tensor. -/
theorem metricTrace_apply (B : BilinMap ℝ W N) :
    metricTrace B = TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor W) := by
  have h : TensorProduct.uncurry (.id ℝ) W W N B = TensorProduct.lift B :=
    TensorProduct.lift.unique fun m n ↦ TensorProduct.uncurry_apply B m n
  rw [metricTrace, LinearMap.comp_apply, h, LinearMap.applyₗ_apply_apply]

/-- In an orthonormal basis, the metric trace is the sum of the diagonal values. -/
theorem metricTrace_eq_sum {ι : Type*} [Fintype ι] (B : BilinMap ℝ W N)
    (b : OrthonormalBasis ι ℝ W) : metricTrace B = ∑ i, B (b i) (b i) := by
  rw [metricTrace_apply, InnerProductSpace.canonicalCovariantTensor_eq_sum W b, map_sum]
  simp only [TensorProduct.lift.tmul]

/-- In an arbitrary basis `b`, the metric trace is `∑ᵢ B(bᵢ, b'ᵢ)`, where `b'` is the dual basis of
`b` for the inner product. The basis need not be orthogonal. -/
theorem metricTrace_eq_sum_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinMap ℝ W N) (b : Module.Basis ι ℝ W) :
    metricTrace B =
      ∑ i, B (b i) (LinearMap.BilinForm.dualBasis (innerₗ W) TauCeti.nondegenerate_inner b i) := by
  simp only [metricTrace_apply, InnerProductSpace.canonicalCovariantTensor_eq_sum_dualBasis W b,
    map_sum, TensorProduct.lift.tmul]

/-- In an arbitrary basis `b`, the metric trace contracts the form against the inverse Gram
matrix of `b`: `tr_g B = ∑ i j, (G⁻¹)ᵢⱼ B(bᵢ, bⱼ)` with `Gᵢⱼ = ⟪bᵢ, bⱼ⟫`. This is the classical
index formula `gⁱʲ Bᵢⱼ`; the basis need not be orthogonal. -/
theorem metricTrace_eq_sum_inv_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinMap ℝ W N) (b : Module.Basis ι ℝ W) :
    metricTrace B = ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j • B (b i) (b j) := by
  simp only [metricTrace_eq_sum_dualBasis B b, b.dualBasis_innerₗ_eq_sum, map_sum, map_smul]

/-- Transposing the arguments of a bilinear map preserves its metric trace. -/
@[simp]
theorem metricTrace_flip (B : BilinMap ℝ W N) : metricTrace B.flip = metricTrace B := by
  simp only [metricTrace_eq_sum _ (stdOrthonormalBasis ℝ W), LinearMap.flip_apply]

/-- The metric trace commutes with a linear map `f` applied to the values of the form. -/
@[simp]
theorem metricTrace_compr₂ {P : Type*} [AddCommMonoid P] [Module ℝ P] (B : BilinMap ℝ W N)
    (f : N →ₗ[ℝ] P) : metricTrace (B.compr₂ f) = f (metricTrace B) := by
  rw [metricTrace_apply, metricTrace_apply, TensorProduct.lift_compr₂, LinearMap.comp_apply]

/-- The metric trace is invariant under pulling the form back along a linear isometric
equivalence `e : W ≃ₗᵢ[ℝ] W'`. -/
@[simp]
theorem metricTrace_compl₁₂_linearIsometryEquiv {W' : Type*} [NormedAddCommGroup W']
    [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W'] (B : BilinMap ℝ W' N) (e : W ≃ₗᵢ[ℝ] W') :
    metricTrace (B.compl₁₂ e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap) =
      metricTrace B := by
  let b := stdOrthonormalBasis ℝ W
  rw [metricTrace_eq_sum _ b, metricTrace_eq_sum B (b.map e)]
  simp only [LinearMap.compl₁₂_apply, OrthonormalBasis.map_apply]
  rfl

/-- The metric trace of the inner product is the real dimension. -/
@[simp]
theorem metricTrace_inner : metricTrace (innerₗ W) = Module.finrank ℝ W := by
  rw [metricTrace_eq_sum (innerₗ W) (stdOrthonormalBasis ℝ W)]
  simp

end LinearMap.BilinMap
