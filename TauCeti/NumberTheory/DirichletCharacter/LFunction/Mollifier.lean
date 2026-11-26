/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LSeries.GaussianTheta
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds

/-!
# A truncated Gaussian mollifier for Dirichlet L-functions

The Mellin integral of the theta series with coefficients `μ(n) χ(n)`, truncated below `r`,
approximates `Γℝ(s+j)/(2 L(s,χ))` on `Re s = 2`. Multiplying by the gamma-weighted L-function
shows that the error is `O(r)`, uniformly in the character, its modulus and the imaginary part.
This provides the right boundary estimate in the three-lines argument that detects zeros from
theta integrals. The estimate corresponds to `New.norm_mul_mollifier_sub_le` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC), revision `72fead1`.
-/

public section

open Complex MeasureTheory Set TauCeti
open scoped ArithmeticFunction.Moebius

namespace DirichletCharacter

/-- The Mellin integral above `r` of the Gaussian theta sum with coefficients `χ(n) μ(n)` and
monomial weight of degree `j`. For a character of parity `j ∈ {0,1}`, this mollifies the
L-function with its matching gamma factor. -/
noncomputable def gaussianMollifier {N : ℕ} (χ : DirichletCharacter ℂ N)
    (j : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) *
    gaussianTheta j (fun n ↦ χ n * (μ n : ℂ)) t

/-- The defining truncated Mellin integral for the Gaussian mollifier. -/
theorem gaussianMollifier_def {N : ℕ} (χ : DirichletCharacter ℂ N)
    (j : ℕ) (r : ℝ) (s : ℂ) :
    χ.gaussianMollifier j r s =
    ∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) *
      gaussianTheta j (fun n ↦ χ n * (μ n : ℂ)) t := (rfl)

/-- On `Re s = 2`, the completed product of a Dirichlet L-function and its Gaussian
mollifier differs from the square of the half-gamma factor by at most `C r`. The constant
depends only on the degree `j` of the monomial weight. -/
theorem exists_norm_LFunction_mul_gaussianMollifier_sub_le (j : ℕ) :
    ∃ C > (0 : ℝ), ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      {r : ℝ}, 0 ≤ r → ∀ {s : ℂ}, s.re = 2 →
      ‖(Gammaℝ (s + j) / 2) * χ.LFunction s * χ.gaussianMollifier j r s -
        (Gammaℝ (s + j) / 2) ^ 2‖ ≤ C * r := by
  let G : ℝ := Real.pi ^ (-(2 + (j : ℝ)) / 2) * Real.Gamma ((2 + (j : ℝ)) / 2) / 2
  have hGpos : 0 < G := by dsimp [G]; positivity
  refine ⟨G * 2 * ((j.factorial : ℝ) * Real.exp 1), mul_pos (mul_pos hGpos (by norm_num))
    (by positivity),
    fun {N} _ χ {r} hr {s} hs ↦ ?_⟩
  have hs₁ : 1 < s.re := by linarith
  have hχ : ‖χ.LFunction s‖ ≤ 2 := by
    rw [LFunction_eq_LSeries χ hs₁]
    simpa only [one_add_one_eq_two] using
      χ.norm_LSeries_le_one_add (s := s) (A := 1) (by norm_num) (by norm_num [hs])
  have hΓ : ‖Gammaℝ (s + j) / 2‖ ≤ G := by
    have hσ : (s + (j : ℂ)).re = 2 + (j : ℝ) := by simp [hs]
    have hσ' : ((s + (j : ℂ)) / 2).re = (2 + (j : ℝ)) / 2 := by rw [div_ofNat_re, hσ]
    rw [norm_div, norm_ofNat, norm_Gammaℝ, hσ]
    dsimp only [G]
    gcongr
    simpa only [hσ'] using norm_Gamma_le_Gamma_re (s := (s + j) / 2) (by rw [hσ']; positivity)
  have hcoeff (n : ℕ+) : ‖χ n * (μ n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one n)).trans ?_
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (n : ℕ))
  let γ := Gammaℝ (s + j) / 2
  have hinv : χ.LFunction s * LSeries (fun n ↦ χ n * (μ n : ℂ)) s = 1 := by
    rw [LFunction_eq_LSeries χ hs₁]
    exact LSeries.mul_mu_eq_one χ hs₁
  have heq : γ * χ.LFunction s * χ.gaussianMollifier j r s - γ ^ 2 =
      γ * χ.LFunction s *
        (χ.gaussianMollifier j r s - LSeries (fun n ↦ χ n * (μ n : ℂ)) s * γ) := by
    rw [mul_sub]
    congr 1
    rw [← mul_assoc, mul_assoc γ, hinv, mul_one, pow_two]
  calc
    _ = ‖γ‖ * ‖χ.LFunction s‖ *
        ‖χ.gaussianMollifier j r s - LSeries (fun n ↦ χ n * (μ n : ℂ)) s * γ‖ := by
      rw [heq, norm_mul, norm_mul]
    _ ≤ G * 2 * (1 * (j.factorial : ℝ) * Real.exp 1 * r) := by
      gcongr
      rw [gaussianMollifier_def]
      exact norm_integral_gaussianTheta_sub_le j hcoeff hr hs
    _ = _ := by ring

end DirichletCharacter
