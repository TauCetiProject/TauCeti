/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville

/-!
# Vanishing of the smooth L² adjoint kernel of a plane vortex

At any solution `x` of the plane vortex equations, a `C²` field `η` satisfying
`L_x L_x* η = 0` has subharmonic squared norm. The Weitzenböck formula expresses its Laplacian
as a sum of covariant-gradient squares and nonnegative potentials, including the strictly
positive section potential `1 / 8 + |α|² / 8`. If `η` is in `L²`, the sub-mean-value inequality
on arbitrarily large balls forces `η = 0`. In particular the smooth `L²` kernel of `L_x*`
vanishes, at every vortex, without a degree restriction or an assumed pointwise decay rate.

These statements concern classical fields. Identifying the completed operator's cokernel
also requires its Fredholm and weak elliptic regularity theorems.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2,
  Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex InnerProductSpace Laplacian MeasureTheory
open scoped RealInnerProductSpace

/-- At a vortex, the squared norm of a classical solution of `L_x L_x* η = 0` is subharmonic.
No decay or integrability hypothesis is needed for this pointwise statement. -/
theorem laplacian_norm_sq_nonneg_of_gaugeFixedOperator_gaugeFixedAdjoint_eq_zero
    {x η : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z)
    (hsol : equation x z = 0) (hker : gaugeFixedOperator x (gaugeFixedAdjoint x η) z = 0) :
    0 ≤ Δ (fun w ↦ ‖η w‖ ^ 2) z := by
  have hW := gaugeFixedOperator_gaugeFixedAdjoint_of_equation_eq_zero hx hη hsol
  rw [hker] at hW
  have h₀ := congrArg (fun v ↦ v 0) hW
  have h₁ := congrArg (fun v ↦ v 1) hW
  have h₂ := congrArg (fun v ↦ v 2) hW
  have h₃ := congrArg (fun v ↦ v 3) hW
  simp only [PiLp.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h₀ h₁ h₂ h₃
  have hΔ (i : Fin 4) : Δ η z i = Δ (fun w ↦ η w i) z :=
    (hη.laplacian_CLM_comp_left (l := EuclideanSpace.proj i)).symm
  have hD (i : Fin 4) (v : ℂ) : fderiv ℝ η z v i = fderiv ℝ (fun w ↦ η w i) z v := by
    exact congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z
        (hη.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  rw [hη.laplacian_norm_sq orthonormalBasisOneI]
  simp only [Fin.sum_univ_two, coe_orthonormalBasisOneI, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, EuclideanSpace.real_norm_sq_eq,
    PiLp.inner_apply, Fin.sum_univ_four, hD, hΔ, RCLike.inner_apply,
    conj_trivial, mul_comm]
  -- Complete the ordinary derivatives of the section components to covariant squares.
  have hp : 0 ≤ (x z 2 ^ 2 + x z 3 ^ 2) * (η z 0 ^ 2 + η z 1 ^ 2) := by positivity
  have hq : 0 ≤ (1 / 8 + (x z 2 ^ 2 + x z 3 ^ 2) / 2) *
      (η z 2 ^ 2 + η z 3 ^ 2) := by positivity
  nlinarith only [hp, hq, congrArg (fun t ↦ η z 0 * t) h₀,
    congrArg (fun t ↦ η z 1 * t) h₁,
    congrArg (fun t ↦ η z 2 * t) h₂,
    congrArg (fun t ↦ η z 3 * t) h₃,
    sq_nonneg (fderiv ℝ (fun w ↦ η w 0) z 1),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 0) z I),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 1) z 1),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 1) z I),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 2) z 1 - x z 0 * η z 3),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 2) z I - x z 1 * η z 3),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 3) z 1 + x z 0 * η z 2),
    sq_nonneg (fderiv ℝ (fun w ↦ η w 3) z I + x z 1 * η z 2)]

/-- The smooth `L²` kernel of `L_x L_x*` at any plane vortex is zero. -/
theorem eq_zero_of_memLp_of_gaugeFixedOperator_gaugeFixedAdjoint_eq_zero
    {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    {x η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hη : ContDiff ℝ 2 η) (hη₂ : MemLp η 2 μ)
    (hsol : ∀ z, equation x z = 0)
    (hker : ∀ z, gaugeFixedOperator x (gaugeFixedAdjoint x η) z = 0) : η = 0 := by
  have hnorm := eq_zero_of_integrable_of_nonneg_of_laplacian_nonneg (hη.norm_sq ℝ)
    ((memLp_two_iff_integrable_sq_norm hη₂.aestronglyMeasurable).mp hη₂)
    (fun z ↦ sq_nonneg ‖η z‖)
    (fun z ↦ laplacian_norm_sq_nonneg_of_gaugeFixedOperator_gaugeFixedAdjoint_eq_zero
      (hx z) (hη.contDiffAt) (hsol z) (hker z))
  funext z
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using congrFun hnorm z))

/-- The smooth `L²` kernel of the formal adjoint of the gauge-fixed plane-vortex operator
vanishes. No finite-energy or asymptotic hypothesis on the vortex is required. -/
theorem eq_zero_of_memLp_of_gaugeFixedAdjoint_eq_zero
    {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    {x η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Differentiable ℝ x) (hη : ContDiff ℝ 2 η) (hη₂ : MemLp η 2 μ)
    (hsol : ∀ z, equation x z = 0) (hker : gaugeFixedAdjoint x η = 0) : η = 0 := by
  refine eq_zero_of_memLp_of_gaugeFixedOperator_gaugeFixedAdjoint_eq_zero hx hη hη₂ hsol
    fun z ↦ ?_
  rw [hker]
  ext i
  fin_cases i <;> simp [linearizedEquation_zero]

end TauCeti.Vortex
