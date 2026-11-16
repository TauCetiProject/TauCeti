/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `ContinuousLinearMap.hilbertSchmidtInner`: the Hilbert–Schmidt inner product
  `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of two linear maps out of a finite-dimensional space, the metric
  trace of `(u, v) ↦ ⟪A u, B v⟫`.

## Main statements

* `TauCeti.bilinFormTrace_eq_sum`: in an orthonormal basis, the metric trace is the sum of the
  diagonal values.
* `TauCeti.bilinFormTrace_eq_sum_inv_gram`: in an arbitrary basis, the metric trace contracts the
  form against the inverse Gram matrix of the basis.
* `TauCeti.bilinFormTrace_inner`: the metric trace of the inner product is the real dimension.
* `ContinuousLinearMap.hilbertSchmidtInner_eq_sum`,
  `ContinuousLinearMap.hilbertSchmidtInner_comm`,
  `ContinuousLinearMap.hilbertSchmidtInner_self_nonneg` and
  `ContinuousLinearMap.hilbertSchmidtInner_self_eq_zero_iff`: the Hilbert–Schmidt inner product
  in an orthonormal basis, its symmetry, and its positive definiteness.
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

end TauCeti

namespace ContinuousLinearMap

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **Hilbert–Schmidt inner product** `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫` of two linear maps out of
a finite-dimensional real inner product space, for any orthonormal basis `eᵢ` of the source
(`ContinuousLinearMap.hilbertSchmidtInner_eq_sum`): the metric trace of the bilinear form
`(u, v) ↦ ⟪A u, B v⟫`, so it does not depend on a basis. -/
noncomputable def hilbertSchmidtInner (A B : W →L[ℝ] V) : ℝ :=
  TauCeti.bilinFormTrace ((innerₗ V).compl₁₂ (A : W →ₗ[ℝ] V) (B : W →ₗ[ℝ] V))

/-- The Hilbert–Schmidt inner product is the metric trace of `(u, v) ↦ ⟪A u, B v⟫`. -/
theorem hilbertSchmidtInner_def (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner B =
      TauCeti.bilinFormTrace ((innerₗ V).compl₁₂ (A : W →ₗ[ℝ] V) (B : W →ₗ[ℝ] V)) :=
  (rfl)

/-- The Hilbert–Schmidt inner product in an orthonormal basis: `⟪A, B⟫_HS = ∑ᵢ ⟪A eᵢ, B eᵢ⟫`. -/
theorem hilbertSchmidtInner_eq_sum (A B : W →L[ℝ] V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ W) : A.hilbertSchmidtInner B = ∑ i, ⟪A (b i), B (b i)⟫_ℝ := by
  simp only [hilbertSchmidtInner_def, TauCeti.bilinFormTrace_eq_sum _ b, LinearMap.compl₁₂_apply,
    innerₗ_apply_apply, coe_coe]

/-- The Hilbert–Schmidt inner product is symmetric. -/
theorem hilbertSchmidtInner_comm (A B : W →L[ℝ] V) :
    A.hilbertSchmidtInner B = B.hilbertSchmidtInner A := by
  simp only [hilbertSchmidtInner_eq_sum _ _ (stdOrthonormalBasis ℝ W), real_inner_comm (A _)]

/-- `⟪A, A⟫_HS = ∑ᵢ ‖A eᵢ‖²` in an orthonormal basis. -/
theorem hilbertSchmidtInner_self_eq_sum (A : W →L[ℝ] V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ W) : A.hilbertSchmidtInner A = ∑ i, ‖A (b i)‖ ^ 2 := by
  simp only [hilbertSchmidtInner_eq_sum _ _ b, real_inner_self_eq_norm_sq]

/-- The Hilbert–Schmidt inner product is nonnegative on the diagonal. -/
theorem hilbertSchmidtInner_self_nonneg (A : W →L[ℝ] V) : 0 ≤ A.hilbertSchmidtInner A := by
  rw [hilbertSchmidtInner_self_eq_sum A (stdOrthonormalBasis ℝ W)]
  exact Finset.sum_nonneg fun i _ ↦ by positivity

/-- The Hilbert–Schmidt inner product is positive definite: `⟪A, A⟫_HS = 0` exactly when
`A = 0`. -/
theorem hilbertSchmidtInner_self_eq_zero_iff (A : W →L[ℝ] V) :
    A.hilbertSchmidtInner A = 0 ↔ A = 0 := by
  set b := stdOrthonormalBasis ℝ W
  rw [hilbertSchmidtInner_self_eq_sum A b,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by positivity]
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, norm_eq_zero]
  refine ⟨fun h ↦ ext fun v ↦ ?_, fun h i ↦ by simp [h]⟩
  rw [← b.sum_repr' v]
  simp [h]

end ContinuousLinearMap
