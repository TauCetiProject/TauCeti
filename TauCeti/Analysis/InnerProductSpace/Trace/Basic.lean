/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Analysis.InnerProductSpace.Nondegenerate

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
* `TauCeti.bilinFormTrace_comp_adjoint`: pulling back a bilinear form along the adjoint of a linear
  isometry preserves its metric trace.
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
  -- `d i` is the vector representing the `i`-th coordinate functional of `b`.
  let d : ι → W := fun i ↦ ∑ j, Ginv i j • b j
  have hd (i : ι) (w : W) : ⟪d i, w⟫_ℝ = b.repr w i := by
    simpa only [Module.Basis.dualBasis_innerₗ_eq_sum] using b.inner_dualBasis_left i w
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

/-- Pulling back a bilinear form along the adjoint of a linear isometry preserves its metric
trace. -/
theorem bilinFormTrace_comp_adjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (f : W →ₗᵢ[ℝ] V) (B : BilinForm ℝ W) :
    bilinFormTrace
        (B.comp (ContinuousLinearMap.adjoint f.toContinuousLinearMap).toLinearMap
          (ContinuousLinearMap.adjoint f.toContinuousLinearMap).toLinearMap) =
      bilinFormTrace B := by
  set p := ContinuousLinearMap.adjoint f.toContinuousLinearMap
  let bW := stdOrthonormalBasis ℝ W
  let bV := stdOrthonormalBasis ℝ V
  rw [bilinFormTrace_eq_sum _ bV, bilinFormTrace_eq_sum B bW]
  have hexp (k) : p (bV k) = ∑ i, ⟪bV k, f (bW i)⟫_ℝ • bW i := by
    conv_lhs => rw [← bW.sum_repr' (p (bV k))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hterm (k) : B (p (bV k)) (p (bV k)) =
      ∑ i, ∑ j, (⟪bV k, f (bW i)⟫_ℝ * ⟪bV k, f (bW j)⟫_ℝ) * B (bW i) (bW j) := by
    rw [hexp k]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [LinearMap.BilinForm.comp_apply, ContinuousLinearMap.coe_coe, hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]
  have hparseval (j) :
      (∑ k, (⟪bV k, f (bW i)⟫_ℝ * ⟪bV k, f (bW j)⟫_ℝ) * B (bW i) (bW j)) =
        ⟪bW i, bW j⟫_ℝ * B (bW i) (bW j) := by
    rw [← Finset.sum_mul]
    congr 1
    have hp := bV.sum_inner_mul_inner (f (bW i)) (f (bW j))
    simpa only [real_inner_comm (f (bW i)), f.inner_map_map] using hp
  simp only [hparseval, bW.inner_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

end TauCeti
