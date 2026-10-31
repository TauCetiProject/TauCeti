/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Deformation
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Reconstructing plane vortices from a regularized scalar equation

For a holomorphic function `f` and a real function `u`, set
`α = exp(u) f` and `a = i (-∂₂u ds + ∂₁u dt)`. The holomorphicity equation
`∂bar_a α = 0` then holds even at the zeros of `f`, and the curvature equation is equivalent to

`Δu = (exp(2u) |f|² - 1) / 8`.

Unlike the equation for `log |α|²`, this equation has no singularities at the prescribed zeros.
The construction uses the real field coordinates of `Vortex.equation`: `α = 2(p + iq)`.
It gives an exact scalar-to-vortex reduction, not existence of a solution of the scalar equation,
finite energy, an end framing, or a choice of gauge for an arbitrary vortex.
`exists_scalarField_section_eq_pow_mul` preserves each finite holomorphic zero multiplicity as a
factorization by the same complex power and a nonvanishing smooth factor. In particular,
repeated divisor points require no singular connection or division by the section.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex InnerProductSpace Laplacian

/-- The field with section `α = exp(u) f` and connection
`a = i (-∂₂u ds + ∂₁u dt)`. The function `u` is the logarithm of the amplitude factor,
not the logarithm of the full section norm, so it can be smooth at zeros of `f`. -/
def scalarField (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ u z I, fderiv ℝ u z 1,
    Real.exp (u z) * (f z).re / 2, Real.exp (u z) * (f z).im / 2]

@[simp]
theorem scalarField_apply_zero (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    scalarField u f z 0 = -fderiv ℝ u z I := (rfl)

@[simp]
theorem scalarField_apply_one (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    scalarField u f z 1 = fderiv ℝ u z 1 := (rfl)

@[simp]
theorem scalarField_apply_two (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    scalarField u f z 2 = Real.exp (u z) * (f z).re / 2 := (rfl)

@[simp]
theorem scalarField_apply_three (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    scalarField u f z 3 = Real.exp (u z) * (f z).im / 2 := (rfl)

/-- The reconstructed section is exactly `exp(u) f`, with the charge-one normalization. -/
theorem scalarField_section (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    2 * ((scalarField u f z 2 : ℂ) + I * scalarField u f z 3) =
      (Real.exp (u z) : ℂ) * f z := by
  apply Complex.ext <;> simp <;> ring

/-- The squared norm of the reconstructed section. -/
theorem scalarField_normSq (u : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) :
    4 * (scalarField u f z 2 ^ 2 + scalarField u f z 3 ^ 2) =
      Real.exp (2 * u z) * ‖f z‖ ^ 2 := by
  rw [two_mul, Real.exp_add, Complex.sq_norm]
  simp only [scalarField_apply_two, scalarField_apply_three, normSq_apply]
  ring

/-- A `C^(n+1)` amplitude and a `C^n` factor give a `C^n` field, including at the zeros
of the factor. -/
theorem contDiff_scalarField {u : ℂ → ℝ} {f : ℂ → ℂ} {n : ℕ∞}
    (hu : ContDiff ℝ (n + 1) u) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (scalarField u f) := by
  have hdu := hu.fderiv_right (m := n) (by simp)
  have hu' : ContDiff ℝ n u := hu.of_le (by simp)
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i
  · exact (hdu.clm_apply contDiff_const).neg
  · exact hdu.clm_apply contDiff_const
  · exact (hu'.exp.mul (Complex.reCLM.contDiff.comp hf)).div_const 2
  · exact (hu'.exp.mul (Complex.imCLM.contDiff.comp hf)).div_const 2

private theorem fderiv_scalarField_section {u : ℂ → ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    (fderiv ℝ (fun w ↦ scalarField u f w 2) z v =
      Real.exp (u z) * (fderiv ℝ u z v * (f z).re + (fderiv ℝ f z v).re) / 2) ∧
    (fderiv ℝ (fun w ↦ scalarField u f w 3) z v =
      Real.exp (u z) * (fderiv ℝ u z v * (f z).im + (fderiv ℝ f z v).im) / 2) := by
  have hr := Complex.reCLM.hasFDerivAt.comp z hf.hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z hf.hasFDerivAt
  simp only [Function.comp_def, reCLM_apply] at hr
  simp only [Function.comp_def, imCLM_apply] at hi
  constructor
  · simp only [scalarField_apply_two, div_eq_mul_inv]
    rw [((hu.hasFDerivAt.exp.fun_mul hr).mul_const (2 : ℝ)⁻¹).fderiv]
    simp
    ring
  · simp only [scalarField_apply_three, div_eq_mul_inv]
    rw [((hu.hasFDerivAt.exp.fun_mul hi).mul_const (2 : ℝ)⁻¹).fderiv]
    simp
    ring

/-- Holomorphicity of the divisor factor solves both real components of `∂bar_a α = 0`,
without dividing by the section. -/
theorem equation_scalarField_holomorphic {u : ℂ → ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (hf : DifferentiableAt ℂ f z) :
    equation (scalarField u f) z 1 = 0 ∧ equation (scalarField u f) z 2 = 0 := by
  have hfr := hf.restrictScalars ℝ
  have hcr : fderiv ℝ f z I = I * fderiv ℝ f z 1 := by
    rw [hf.fderiv_restrictScalars ℝ]
    simp [← smul_eq_mul]
  have hr := congrArg Complex.re hcr
  have hi := congrArg Complex.im hcr
  simp only [I_mul_re, I_mul_im] at hr hi
  have h₁ := fderiv_scalarField_section hu hfr 1
  have h₂ := fderiv_scalarField_section hu hfr I
  constructor
  · rw [equation_apply_one, h₁.1, h₂.2]
    simp only [scalarField_apply_zero, scalarField_apply_one, scalarField_apply_two,
      scalarField_apply_three]
    rw [hi]
    ring
  · rw [equation_apply_two, h₁.2, h₂.1]
    simp only [scalarField_apply_zero, scalarField_apply_one, scalarField_apply_two,
      scalarField_apply_three]
    rw [hr]
    ring

/-- The curvature defect of the reconstructed field is the defect of the regularized
scalar equation. -/
theorem equation_scalarField_curvature {u : ℂ → ℝ} (f : ℂ → ℂ) {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) :
    equation (scalarField u f) z 0 =
      -Δ u z + (Real.exp (2 * u z) * ‖f z‖ ^ 2 - 1) / 8 := by
  have hdu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [equation_apply_zero, ← scalarField_normSq u f z,
    laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI hdu, Fin.sum_univ_two]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    scalarField_apply_zero, scalarField_apply_one]
  rw [fderiv_fun_neg]
  simp
  ring

/-- The smooth ansatz is a vortex exactly when its amplitude solves the regularized scalar
PDE. This equivalence holds at zeros of the holomorphic factor as well. -/
theorem equation_scalarField_eq_zero_iff {u : ℂ → ℝ} {f : ℂ → ℂ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hf : DifferentiableAt ℂ f z) :
    equation (scalarField u f) z = 0 ↔
      Δ u z = (Real.exp (2 * u z) * ‖f z‖ ^ 2 - 1) / 8 := by
  have hh := equation_scalarField_holomorphic (hu.differentiableAt (by norm_num)) hf
  constructor
  · intro h
    have h₀ := congrArg (fun x : EuclideanSpace ℝ (Fin 3) ↦ x 0) h
    rw [equation_scalarField_curvature f hu] at h₀
    simp only [PiLp.zero_apply] at h₀
    linarith
  · intro h
    ext i
    fin_cases i
    · simp [equation_scalarField_curvature f hu, h]
    · exact hh.1
    · exact hh.2

/-- A zero of finite holomorphic order `m` retains its multiplicity: the reconstructed
section locally factors as `(w - z)^m` times a nonvanishing `C^n` function. This statement
also includes `m = 0`, and does not require solving the scalar equation. -/
theorem exists_scalarField_section_eq_pow_mul {u : ℂ → ℝ} {f : ℂ → ℂ} {z : ℂ} {m : ℕ}
    {n : ℕ∞} (hu : ContDiffAt ℝ n u z) (hf : AnalyticAt ℂ f z)
    (hm : analyticOrderAt f z = m) :
    ∃ g : ℂ → ℂ, ContDiffAt ℝ n g z ∧ g z ≠ 0 ∧
      ∀ᶠ w in nhds z,
        2 * ((scalarField u f w 2 : ℂ) + I * scalarField u f w 3) = (w - z) ^ m * g w := by
  obtain ⟨g, hg, hg₀, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  refine ⟨fun w ↦ (Real.exp (u w) : ℂ) * g w,
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hu.exp).mul
      (hg.contDiffAt.restrict_scalars ℝ), mul_ne_zero (by simp) hg₀, ?_⟩
  filter_upwards [hfg] with w hw
  rw [scalarField_section, hw, smul_eq_mul]
  ring

end TauCeti.Vortex
