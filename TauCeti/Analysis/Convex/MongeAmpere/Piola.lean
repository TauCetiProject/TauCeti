/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Calculus.FDeriv.Adjugate
public import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The Hessian Piola identity and divergence-form linearization

The adjugate of the Hessian of a `C³` real function has divergence-free rows. Consequently,
the divergence of the cofactor flux `adj(Hess u) ∇v` is the trace contraction
`trace (adj(Hess u) * Hess v)`. The divergence is `trace (D ·)`, as for the standard
`TestFunction.divergenceCLM`; the Hessian is `TauCeti.hessianOperator` in an orthonormal basis.
The identity includes singular Hessians and the zero-dimensional case.

The row-cancellation argument is adapted from the smooth Piola theorem in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean).
The cofactor flux is the divergence-form linearized Monge–Ampère operator.
-/

public section

open TauCeti
open scoped Gradient Matrix.Norms.Operator ContDiff

namespace OrthonormalBasis

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The rows of the adjugate Hessian of a `C³` function are divergence free. -/
theorem sum_fderiv_adjugate_hessian_eq_zero (b : OrthonormalBasis ι ℝ E)
    {u : E → ℝ} (hu : ContDiff ℝ 3 u) (x : E) (i : ι) :
    ∑ j, fderiv ℝ (fun y ↦
      (LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap).adjugate i j)
      x (b j) = 0 := by
  have hD : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := hD.fderiv_right (by norm_num)
  have hcoords (y : E) (k l : ι) :
      LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap k l =
        fderiv ℝ (fderiv ℝ u) y (b k) (b l) := by
    rw [b.toMatrix_hessianOperator_apply]
    exact hu.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _
  refine Matrix.sum_fderiv_adjugate_eq_zero_of_comm
    (fun y ↦ LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap)
    (fun j ↦ b j) x ?_ ?_ i
  · intro k l
    simp_rw [hcoords]
    exact ((hD2.clm_apply contDiff_const).clm_apply contDiff_const).differentiable
      (by norm_num) x
  · intro j k l
    simp_rw [hcoords]
    rw [fderiv_clm_apply_const_apply₂ (hD2.differentiable (by norm_num) x),
      fderiv_clm_apply_const_apply₂ (hD2.differentiable (by norm_num) x)]
    exact congrArg (fun L : E →L[ℝ] ℝ ↦ L (b l))
      (hD.contDiffAt.isSymmSndFDerivAt (by norm_num) (b j) (b k))

/-- The divergence of the cofactor Hessian flux is its contraction with the Hessian of the
scalar test function. -/
theorem trace_fderiv_adjugate_hessian_gradient (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 2 v) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ (fun y ↦
      Matrix.toLin b.toBasis b.toBasis
        (LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap).adjugate
        (∇ v y)) x).toLinearMap =
      ((LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u x).toLinearMap).adjugate *
        LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap).trace := by
  let : FiniteDimensional ℝ E := Module.Finite.of_basis b.toBasis
  let H (y : E) : Matrix ι ι ℝ :=
    LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator u y).toLinearMap
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have hentry (i j : ι) : DifferentiableAt ℝ (fun y ↦ H y i j) x := by
    simp only [H, b.toMatrix_hessianOperator_apply]
    exact ((hD2.clm_apply contDiff_const).clm_apply contDiff_const).differentiable
      (by norm_num) x
  have hAdj (i j : ι) : DifferentiableAt ℝ (fun y ↦ (H y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply Matrix.differentiable_det.differentiableAt.comp x
    apply differentiableAt_pi.mpr
    intro k
    apply differentiableAt_pi.mpr
    intro l
    by_cases hk : k = j
    · simp only [Matrix.updateRow_apply, hk, ite_true]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_apply, hk, ite_false]
      exact hentry k l
  have hDv (j : ι) : DifferentiableAt ℝ (fun y ↦ fderiv ℝ v y (b j)) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num) x
  have hsym (y : E) : (H y).IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, H, b.toMatrix_hessianOperator_apply]
    exact hu.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _
  have hcol (j : ι) :
      ∑ i, fderiv ℝ (fun y ↦ (H y).adjugate i j) x (b i) = 0 := by
    have heq (i : ι) : (fun y ↦ (H y).adjugate i j) = fun y ↦ (H y).adjugate j i := by
      funext y
      exact (congrArg (fun A : Matrix ι ι ℝ ↦ A i j) (hsym y).adjugate).symm
    simp_rw [heq]
    exact b.sum_fderiv_adjugate_hessian_eq_zero hu x j
  let c (i : ι) (y : E) := ∑ j, (H y).adjugate i j * fderiv ℝ v y (b j)
  have hc (i : ι) : DifferentiableAt ℝ (c i) x :=
    DifferentiableAt.fun_sum fun j _ ↦ (hAdj i j).mul (hDv j)
  have hflux : (fun y ↦ Matrix.toLin b.toBasis b.toBasis (H y).adjugate (∇ v y)) =
      fun y ↦ ∑ i, c i y • b i := by
    funext y
    simp only [Matrix.toLin_apply, Matrix.mulVec, dotProduct, b.coe_toBasis,
      b.coe_toBasis_repr_apply, b.repr_apply_apply, inner_gradient_right, conj_trivial, c]
  have hdiv : LinearMap.trace ℝ E
      (fderiv ℝ (fun y ↦ ∑ i, c i y • b i) x).toLinearMap =
        ∑ i, fderiv ℝ (c i) x (b i) := by
    rw [fderiv_fun_sum (fun i _ ↦ (hc i).smul_const (b i)),
      ContinuousLinearMap.toLinearMap_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_smul_const (hc i)]
    exact LinearMap.trace_smulRight _ _
  have hdc (i : ι) : fderiv ℝ (c i) x (b i) =
      ∑ j, ((H x).adjugate i j * fderiv ℝ (fun y ↦ fderiv ℝ v y (b j)) x (b i) +
        fderiv ℝ v x (b j) * fderiv ℝ (fun y ↦ (H y).adjugate i j) x (b i)) := by
    simp only [c]
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j y ↦ (H y).adjugate i j * fderiv ℝ v y (b j))
      (fun j _ ↦ (hAdj i j).mul (hDv j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hAdj i j) (hDv j)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hcancel :
      (∑ i, ∑ j, fderiv ℝ v x (b j) *
        fderiv ℝ (fun y ↦ (H y).adjugate i j) x (b i)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.mul_sum, hcol j, mul_zero]
  have hmain : LinearMap.trace ℝ E
      (fderiv ℝ (fun y ↦ Matrix.toLin b.toBasis b.toBasis (H y).adjugate (∇ v y)) x).toLinearMap =
      ((H x).adjugate *
        LinearMap.toMatrix b.toBasis b.toBasis (hessianOperator v x).toLinearMap).trace := by
    rw [hflux, hdiv]
    simp_rw [hdc, Finset.sum_add_distrib]
    rw [hcancel, add_zero]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      b.toMatrix_hessianOperator_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_clm_apply_const_apply
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)]
  simpa only [H] using hmain

end OrthonormalBasis
