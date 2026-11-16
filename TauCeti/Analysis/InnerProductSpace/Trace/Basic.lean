/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Analysis.InnerProductSpace.CanonicalTensor

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
  rw [bilinFormTrace_apply, TensorProduct.lift_canonicalCovariantTensor_eq_sum B b]

/-- In an arbitrary basis `b`, the metric trace contracts the form against the inverse Gram
matrix of `b`: `tr_g B = ∑ i j, (G⁻¹)ᵢⱼ B(bᵢ, bⱼ)` with `Gᵢⱼ = ⟪bᵢ, bⱼ⟫`. This is the classical
index formula `gⁱʲ Bᵢⱼ`; the basis need not be orthogonal. -/
theorem bilinFormTrace_eq_sum_inv_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinForm ℝ W) (b : Module.Basis ι ℝ W) :
    bilinFormTrace B = ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j * B (b i) (b j) := by
  simp_rw [bilinFormTrace_apply, TensorProduct.lift_canonicalCovariantTensor_eq_sum_inv_gram B b,
    smul_eq_mul]

/-- The metric trace of the inner product is the real dimension. -/
@[simp]
theorem bilinFormTrace_inner : bilinFormTrace (innerₗ W) = Module.finrank ℝ W := by
  rw [bilinFormTrace_eq_sum (innerₗ W) (stdOrthonormalBasis ℝ W)]
  simp

end TauCeti
