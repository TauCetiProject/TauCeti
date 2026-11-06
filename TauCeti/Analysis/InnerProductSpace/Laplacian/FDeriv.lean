/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Laplacian commutes with derivatives

On a finite-dimensional real inner product space the Laplacian commutes with derivatives of `C³`
maps: `Δ (∂ᵥ u) = ∂ᵥ (Δ u)` (`ContDiffAt.laplacian_fderiv_apply`, `ContDiffAt.laplacian_fderiv`),
and `Δ (∇ u) = ∇ (Δ u)` for real functions (`ContDiffAt.laplacian_gradient`).
So the derivatives of a solution of a semilinear equation `Δ u = F(u)` satisfy the linearized
equation `Δ (∂ᵥ u) = F'(u) ∂ᵥ u`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian
open scoped Gradient RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Laplacian commutes with directional derivatives.** For a map `u` which is `C³` at `x`,
`Δ (∂ᵥ u) = ∂ᵥ (Δ u)` at `x`. -/
theorem _root_.ContDiffAt.laplacian_fderiv_apply {u : E → F} {x : E} (hu : ContDiffAt ℝ 3 u x)
    (v : E) : Δ (fun y ↦ fderiv ℝ u y v) x = fderiv ℝ (Δ u) x v := by
  set b := stdOrthonormalBasis ℝ E
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (m := 2) (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) x := hDu.fderiv_right (m := 1) (by norm_num)
  have hD2d : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x := hD2.differentiableAt (by norm_num)
  -- `Δ u` is the sum of the diagonal second derivatives in the basis `b`, at every point.
  have hΔ : Δ u = fun y ↦ ∑ i, fderiv ℝ (fderiv ℝ u) y (b i) (b i) := by
    funext y
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis u b) y]
    simp [iteratedFDeriv_two_apply]
  have hd (i : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ u) y (b i) (b i)) x :=
    (hD2d.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x, hΔ,
    fderiv_fun_sum fun i _ ↦ hd i]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_fderiv_fderiv_apply hu, fderiv_clm_apply_const_apply
      (hD2d.clm_apply (differentiableAt_const _)),
    fderiv_clm_apply_const_apply hD2d,
    fderiv_fderiv_fderiv_apply_comm hu (by simp) (b i) (b i) v,
    hDu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) (b i) v]

/-- **The Laplacian commutes with the derivative.** For a map `u` which is `C³` at `x`,
`Δ (Du) = D (Δ u)` at `x`, as continuous linear maps. -/
theorem _root_.ContDiffAt.laplacian_fderiv {u : E → F} {x : E} (hu : ContDiffAt ℝ 3 u x) :
    Δ (fderiv ℝ u) x = fderiv ℝ (Δ u) x := by
  have hDu : ContDiffAt ℝ 2 (fderiv ℝ u) x := hu.fderiv_right (m := 2) (by norm_num)
  ext v
  rw [← hu.laplacian_fderiv_apply v]
  exact (hDu.laplacian_CLM_comp_left (l := ContinuousLinearMap.apply ℝ F v)).symm

/-- **The Laplacian commutes with the gradient.** For a real function `u` which is `C³` at `x`,
`Δ (∇ u) = ∇ (Δ u)` at `x`. -/
theorem _root_.ContDiffAt.laplacian_gradient {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 3 u x) :
    Δ (∇ u) x = ∇ (Δ u) x := by
  have hg : ContDiffAt ℝ 2 (∇ u) x := hu.gradient_right (by norm_num)
  refine ext_inner_left ℝ fun a ↦ ?_
  have hcomp : (innerSL ℝ a ∘ ∇ u) = fun y ↦ fderiv ℝ u y a := by
    funext y
    simp [inner_gradient_right]
  have h := hg.laplacian_CLM_comp_left (l := innerSL ℝ a)
  rw [hcomp, hu.laplacian_fderiv_apply, Function.comp_apply, innerSL_apply_apply] at h
  rw [← h, inner_gradient_right, conj_trivial]

end TauCeti
