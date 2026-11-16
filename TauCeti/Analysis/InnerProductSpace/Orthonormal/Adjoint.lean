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

Let `P : W →L[𝕜] V` be a continuous linear coisometry between complete `RCLike` inner product
spaces, that is, `P ∘L P.adjoint = id`. Pulling back linear functionals or bilinear forms on `V`
along `P` and contracting them with conjugation on the first factor over a finite orthonormal basis
of `W` yields the same contraction over any finite orthonormal basis of `V`. Over `ℝ` the
conjugation drops out. This unifies orthogonal/unitary change-of-frame invariance (when `P` is a
linear isometric equivalence) and invariance under zero extension along an orthogonal projection
(such as `WithLp.fstL : WithLp 2 (V × U) →L[ℝ] V`).

## Main statements

* `OrthonormalBasis.sum_conj_mul_linearMap_comp_of_comp_adjoint_eq_id`: single-slot conjugate
  contraction of two `𝕜`-linear functionals pulled back along `P`.
* `OrthonormalBasis.sum_mul_linearMap_comp_of_comp_adjoint_eq_id`: real specialization without
  conjugation.
* `OrthonormalBasis.sum_conj_mul_bilinForm_comp_of_comp_adjoint_eq_id`: double conjugate
  contraction of two `𝕜`-bilinear forms pulled back along `P`.
* `OrthonormalBasis.sum_mul_bilinForm_comp_of_comp_adjoint_eq_id`: real specialization without
  conjugation.
-/

public section

open scoped InnerProductSpace ComplexConjugate

namespace OrthonormalBasis

section RCLike

variable {𝕜 V W α β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
  [Fintype α] [Fintype β]

/-- Single-slot conjugate contraction of two `𝕜`-linear functionals pulled back along a continuous
linear coisometry `P : W →L[𝕜] V` (`P ∘L P.adjoint = id`). -/
theorem sum_conj_mul_linearMap_comp_of_comp_adjoint_eq_id
    {G₁ G₂ : Type*} [FunLike G₁ V 𝕜] [LinearMapClass G₁ 𝕜 V 𝕜]
    [FunLike G₂ V 𝕜] [LinearMapClass G₂ 𝕜 V 𝕜]
    (bW : OrthonormalBasis α 𝕜 W) (bV : OrthonormalBasis β 𝕜 V)
    {P : W →L[𝕜] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id 𝕜 V)
    (φ : G₁) (ψ : G₂) :
    ∑ a, conj (φ (P (bW a))) * ψ (P (bW a)) = ∑ p, conj (φ (bV p)) * ψ (bV p) := by
  have hP' (x : V) : P (P.adjoint x) = x := by
    simpa using DFunLike.congr_fun hP x
  calc ∑ a, conj (φ (P (bW a))) * ψ (P (bW a))
      = ∑ a, (∑ p, conj (φ (bV p)) * ⟪P (bW a), bV p⟫_𝕜) * ψ (P (bW a)) := by
        refine Finset.sum_congr rfl fun a _ ↦ congrArg (· * _) ?_
        rw [← bV.sum_apply_mul_inner φ (P (bW a)), map_sum]
        exact Finset.sum_congr rfl fun p _ ↦ by rw [map_mul, inner_conj_symm]
    _ = ∑ p, conj (φ (bV p)) *
          ∑ a, ((LinearMap.ofClass ψ).comp P.toLinearMap) (bW a) * ⟪bW a, P.adjoint (bV p)⟫_𝕜 := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← ContinuousLinearMap.adjoint_inner_right, LinearMap.comp_apply,
          LinearMap.coe_ofClass, ContinuousLinearMap.coe_coe]
        ring
    _ = ∑ p, conj (φ (bV p)) * ψ (bV p) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [bW.sum_apply_mul_inner, LinearMap.comp_apply, LinearMap.coe_ofClass,
          ContinuousLinearMap.coe_coe, hP']

/-- Double conjugate contraction of two `𝕜`-bilinear forms pulled back along a continuous linear
coisometry `P : W →L[𝕜] V` (`P ∘L P.adjoint = id`). -/
theorem sum_conj_mul_bilinForm_comp_of_comp_adjoint_eq_id
    (bW : OrthonormalBasis α 𝕜 W) (bV : OrthonormalBasis β 𝕜 V)
    {P : W →L[𝕜] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id 𝕜 V)
    (F G : LinearMap.BilinForm 𝕜 V) :
    ∑ a, ∑ b, conj (F (P (bW a)) (P (bW b))) * G (P (bW a)) (P (bW b)) =
      ∑ p, ∑ q, conj (F (bV p) (bV q)) * G (bV p) (bV q) := by
  calc ∑ a, ∑ b, conj (F (P (bW a)) (P (bW b))) * G (P (bW a)) (P (bW b))
      = ∑ a, ∑ q, conj (F (P (bW a)) (bV q)) * G (P (bW a)) (bV q) :=
        Finset.sum_congr rfl fun a _ ↦
          bW.sum_conj_mul_linearMap_comp_of_comp_adjoint_eq_id bV hP
            (F (P (bW a))) (G (P (bW a)))
    _ = ∑ q, ∑ a, conj (F.flip (bV q) (P (bW a))) * G.flip (bV q) (P (bW a)) := by
        simp only [LinearMap.BilinForm.flip_apply]; exact Finset.sum_comm
    _ = ∑ q, ∑ p, conj (F.flip (bV q) (bV p)) * G.flip (bV q) (bV p) :=
        Finset.sum_congr rfl fun q _ ↦
          bW.sum_conj_mul_linearMap_comp_of_comp_adjoint_eq_id bV hP
            (F.flip (bV q)) (G.flip (bV q))
    _ = ∑ p, ∑ q, conj (F (bV p) (bV q)) * G (bV p) (bV q) := by
        simp only [LinearMap.BilinForm.flip_apply]; exact Finset.sum_comm

end RCLike

section Real

variable {V W α β : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype α] [Fintype β]

/-- Single-slot contraction of two real linear functionals pulled back along a continuous linear
coisometry `P : W →L[ℝ] V` (`P ∘L P.adjoint = id`). -/
theorem sum_mul_linearMap_comp_of_comp_adjoint_eq_id
    {G₁ G₂ : Type*} [FunLike G₁ V ℝ] [LinearMapClass G₁ ℝ V ℝ]
    [FunLike G₂ V ℝ] [LinearMapClass G₂ ℝ V ℝ]
    (bW : OrthonormalBasis α ℝ W) (bV : OrthonormalBasis β ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (φ : G₁) (ψ : G₂) :
    ∑ a, φ (P (bW a)) * ψ (P (bW a)) = ∑ p, φ (bV p) * ψ (bV p) := by
  simpa using bW.sum_conj_mul_linearMap_comp_of_comp_adjoint_eq_id bV hP φ ψ

/-- Double contraction of two real bilinear forms pulled back along a continuous linear coisometry
`P : W →L[ℝ] V` (`P ∘L P.adjoint = id`). -/
theorem sum_mul_bilinForm_comp_of_comp_adjoint_eq_id
    (bW : OrthonormalBasis α ℝ W) (bV : OrthonormalBasis β ℝ V)
    {P : W →L[ℝ] V} (hP : P ∘L P.adjoint = ContinuousLinearMap.id ℝ V)
    (F G : LinearMap.BilinForm ℝ V) :
    ∑ a, ∑ b, F (P (bW a)) (P (bW b)) * G (P (bW a)) (P (bW b)) =
      ∑ p, ∑ q, F (bV p) (bV q) * G (bV p) (bV q) := by
  simpa using bW.sum_conj_mul_bilinForm_comp_of_comp_adjoint_eq_id bV hP F G

end Real

end OrthonormalBasis
