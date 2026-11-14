/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# Contractions along orthonormal bases pulled back by a coisometry

Let `P : W →L[ℝ] V` be a continuous linear coisometry between complete real inner product spaces,
that is, `P ∘L P.adjoint = id`. Pulling back real linear functionals or bilinear forms on `V` along
`P` and contracting them over a finite orthonormal basis of `W` yields the same contraction over
any finite orthonormal basis of `V`. This unifies orthogonal change-of-frame invariance (when `P`
is a linear isometric equivalence) and invariance under zero extension along an orthogonal
projection (such as `WithLp.fstL : WithLp 2 (V × U) →L[ℝ] V`).

## Main statements

* `OrthonormalBasis.sum_mul_linearMap_comp_of_comp_adjoint_eq_id`: single-slot contraction of two
  real linear functionals pulled back along `P`.
* `OrthonormalBasis.sum_mul_bilinForm_comp_of_comp_adjoint_eq_id`: double contraction of two real
  bilinear forms pulled back along `P`.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {V W α β : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype α] [Fintype β]

/-- Single-slot contraction of two real linear functionals pulled back along a continuous linear
coisometry `P : W →L[ℝ] V` (`P ∘L P.adjoint = id`). -/
theorem sum_mul_linearMap_comp_of_comp_adjoint_eq_id
    (bW : OrthonormalBasis α ℝ W) (bV : OrthonormalBasis β ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (φ ψ : V →ₗ[ℝ] ℝ) :
    ∑ a, φ (P (bW a)) * ψ (P (bW a)) = ∑ p, φ (bV p) * ψ (bV p) := by
  have hP' (x : V) : P (P.adjoint x) = x := by
    simpa using DFunLike.congr_fun hP x
  calc ∑ a, φ (P (bW a)) * ψ (P (bW a))
      = ∑ a, (∑ p, φ (bV p) * ⟪bV p, P (bW a)⟫_ℝ) * ψ (P (bW a)) := by
        simp_rw [bV.sum_apply_mul_inner φ]
    _ = ∑ p, φ (bV p) * ∑ a, (ψ.comp P.toLinearMap) (bW a) * ⟪bW a, P.adjoint (bV p)⟫_ℝ := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_comm (P.adjoint (bV p)),
          LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        ring
    _ = ∑ p, φ (bV p) * ψ (bV p) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [bW.sum_apply_mul_inner, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hP']

/-- Double contraction of two real bilinear forms pulled back along a continuous linear coisometry
`P : W →L[ℝ] V` (`P ∘L P.adjoint = id`). -/
theorem sum_mul_bilinForm_comp_of_comp_adjoint_eq_id
    (bW : OrthonormalBasis α ℝ W) (bV : OrthonormalBasis β ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (F G : LinearMap.BilinForm ℝ V) :
    ∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b)) =
      ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := by
  calc ∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b))
      = ∑ a, ∑ q, F (P (bW a)) (bV q) * G (P (bW a)) (bV q) :=
        Finset.sum_congr rfl fun a _ ↦
          bW.sum_mul_linearMap_comp_of_comp_adjoint_eq_id bV hP (F (P (bW a))) (G (P (bW a)))
    _ = ∑ q, ∑ a, F.flip (bV q) (P (bW a)) * G.flip (bV q) (P (bW a)) := by
        simp only [LinearMap.BilinForm.flip_apply]; exact Finset.sum_comm
    _ = ∑ q, ∑ p, F.flip (bV q) (bV p) * G.flip (bV q) (bV p) :=
        Finset.sum_congr rfl fun q _ ↦
          bW.sum_mul_linearMap_comp_of_comp_adjoint_eq_id bV hP (F.flip (bV q)) (G.flip (bV q))
    _ = ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := by
        simp only [LinearMap.BilinForm.flip_apply]; exact Finset.sum_comm

end OrthonormalBasis
