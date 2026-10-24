/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Metric trace of a bilinear form

This file defines the metric trace of a bilinear form on a finite-dimensional real inner product
space. The definition contracts the form against Mathlib's canonical covariant tensor, making it
independent of any choice of basis.

## Main definitions

* `TauCeti.bilinFormTrace`: the metric trace of a real bilinear form.

## Main statements

* `TauCeti.bilinFormTrace_eq_sum`: in an orthonormal basis, the metric trace is the sum of the
  diagonal values.
* `TauCeti.bilinFormTrace_eq_sum_inv_gram`: in an arbitrary basis, the metric trace contracts the
  form against the inverse Gram matrix of the basis.
* `TauCeti.bilinFormTrace_inner`: the metric trace of the inner product is the real dimension.
-/

public section

open LinearMap (BilinForm)
open scoped InnerProductSpace TensorProduct

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The metric trace of a bilinear form, obtained by contracting it against the canonical
covariant tensor of the inner product. -/
noncomputable def bilinFormTrace : BilinForm ℝ W →ₗ[ℝ] ℝ :=
  (LinearMap.applyₗ (InnerProductSpace.canonicalCovariantTensor W)).comp
    (TensorProduct.lift.equiv (RingHom.id ℝ) W W ℝ).toLinearMap

/-- The metric trace is evaluation on the canonical covariant tensor. -/
theorem bilinFormTrace_apply (B : BilinForm ℝ W) :
    bilinFormTrace B = TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor W) :=
  (rfl)

/-- In an orthonormal basis, the metric trace is the sum of the diagonal values. -/
theorem bilinFormTrace_eq_sum {i : Type*} [Fintype i] (B : BilinForm ℝ W)
    (b : OrthonormalBasis i ℝ W) : bilinFormTrace B = ∑ j, B (b j) (b j) := by
  rw [bilinFormTrace_apply, InnerProductSpace.canonicalCovariantTensor_eq_sum W b, map_sum]
  simp only [TensorProduct.lift.tmul]

/-- In an arbitrary basis `b`, the metric trace contracts the form against the inverse Gram
matrix of `b`: `tr_g B = ∑ i j, (G⁻¹)ᵢⱼ B(bᵢ, bⱼ)` with `Gᵢⱼ = ⟪bᵢ, bⱼ⟫`. This is the classical
index formula `gⁱʲ Bᵢⱼ`; the basis need not be orthogonal. -/
theorem bilinFormTrace_eq_sum_inv_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinForm ℝ W) (b : Module.Basis ι ℝ W) :
    bilinFormTrace B = ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * B (b i) (b j) := by
  set Ginv := (Matrix.gram ℝ b)⁻¹
  have hinv : Ginv * Matrix.gram ℝ b = 1 :=
    Matrix.nonsing_inv_mul _ <| isUnit_iff_ne_zero.mpr <|
      Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  -- `d i` is the vector representing the `i`-th coordinate functional of `b`.
  let d : ι → W := fun i ↦ ∑ j, Ginv i j • b j
  have hd (i : ι) (w : W) : ⟪d i, w⟫_ℝ = b.repr w i := by
    have hlin : (innerₛₗ ℝ (d i) : W →ₗ[ℝ] ℝ) = b.coord i := by
      refine b.ext fun k ↦ ?_
      have hik := congrFun (congrFun hinv i) k
      simp only [Matrix.mul_apply, Matrix.gram_apply, Matrix.one_apply] at hik
      simp only [innerₛₗ_apply_apply, d, sum_inner, real_inner_smul_left, hik,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
    simpa only [innerₛₗ_apply_apply, Module.Basis.coord_apply] using LinearMap.congr_fun hlin w
  have htensor : InnerProductSpace.canonicalCovariantTensor W = ∑ i, b i ⊗ₜ[ℝ] d i := by
    let v := stdOrthonormalBasis ℝ W
    rw [InnerProductSpace.canonicalCovariantTensor_eq_sum W v]
    calc ∑ k, v k ⊗ₜ[ℝ] v k = ∑ k, (∑ i, ⟪d i, v k⟫_ℝ • b i) ⊗ₜ[ℝ] v k := by
          simp only [hd, b.sum_repr]
      _ = ∑ i, b i ⊗ₜ[ℝ] ∑ k, ⟪v k, d i⟫_ℝ • v k := by
          simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul,
            real_inner_comm (d _)]
          exact Finset.sum_comm
      _ = ∑ i, b i ⊗ₜ[ℝ] d i := by simp only [v.sum_repr']
  rw [bilinFormTrace_apply, htensor, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [TensorProduct.lift.tmul, d, map_sum, map_smul, smul_eq_mul]

/-- The metric trace of the inner product is the real dimension. -/
@[simp]
theorem bilinFormTrace_inner : bilinFormTrace (innerₗ W) = Module.finrank ℝ W := by
  rw [bilinFormTrace_eq_sum (innerₗ W) (stdOrthonormalBasis ℝ W)]
  simp

end TauCeti
