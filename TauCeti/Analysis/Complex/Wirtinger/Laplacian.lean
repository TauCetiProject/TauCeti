/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed Wirtinger derivatives and the planar Laplacian

For a complex-valued function on the plane, the mixed Wirtinger derivative `bar∂ ∂ u`
is one quarter of the real Laplacian. This identity converts Laplacian potentials into
solutions of the inhomogeneous Cauchy–Riemann equation.
-/

public noncomputable section

open Complex InnerProductSpace Laplacian

namespace TauCeti

/-- The mixed Wirtinger derivative of a complex-valued function on the plane is one quarter
of its real Laplacian. -/
theorem conjWirtingerDeriv_wirtingerDeriv_apply_one_eq_laplacian {u : ℂ → ℂ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) :
    conjWirtingerDeriv (fun w ↦ wirtingerDeriv u w 1) z 1 = (4 : ℂ)⁻¹ * Δ u z := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w v) z :=
    hd.clm_apply (differentiableAt_const _)
  have hc := (hu.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  rw [laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI hd,
    Fin.sum_univ_two]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [conjWirtingerDeriv_apply, wirtingerDeriv_apply, smul_eq_mul, mul_one]
  have hW := (((hp 1).hasFDerivAt.fun_sub
    ((hp I).hasFDerivAt.const_mul I)).const_mul (2 : ℂ)⁻¹)
  rw [hW.fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul,
    fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  rw [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end TauCeti
