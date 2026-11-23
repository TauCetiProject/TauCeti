/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Analysis.Normed.Operator.Exponential
import Mathlib.Analysis.Normed.Algebra.Spectrum
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.EqOne
import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# The spectrum of the exponential of a matrix

For a complex square matrix `Y`, the eigenvalues of `exp Y` are the exponentials of the eigenvalues
of `Y` (`Matrix.spectrum_exp`): this is the spectral mapping theorem for the exponential of an
operator on a finite-dimensional complex space, `ContinuousLinearMap.spectrum_exp`, read through
the star algebra equivalence `Matrix.toEuclideanCLM`.

The eigenvalues of `exp Y` are therefore the values `exp ν` at eigenvalues `ν` of `Y`, and these
satisfy `‖ν‖ ≤ ‖Y‖` for the `ℓ²` operator norm (`Matrix.exists_norm_le_exp_eq_of_mem_spectrum`).
This is how one shows that `exp Y` has no eigenvalue `1`, or no eigenvalue `-1`, when `Y` is small:
such an eigenvalue forces `ν ∈ 2π i ℤ`, respectively `ν ∈ π i (2 ℤ + 1)`
(`Complex.eq_zero_of_exp_eq_one_of_norm_lt`, `Complex.pi_le_norm_of_exp_eq_neg_one`). A real matrix
`Y` is handled by viewing it as a complex matrix (`Matrix.exp_map_ofReal`).

## Main results

* `Matrix.spectrum_exp`: the spectrum of `exp Y` is the image of the spectrum of `Y` under `exp`.
* `Matrix.exp_map_ofReal`: the exponential commutes with viewing a real matrix as a complex one.
* `Matrix.exists_norm_le_exp_eq_of_mem_spectrum`: every eigenvalue of `exp Y`, for a complex matrix
  `Y`, is `exp ν` for an eigenvalue `ν` of `Y` with `‖ν‖ ≤ ‖Y‖`.
* `Matrix.isUnit_exp_sub_one`: if a complex matrix `Y` is invertible and `‖Y‖ < 2π`, then `exp Y`
  has no eigenvalue `1`; `Matrix.isUnit_exp_sub_one_real` is the real case.
* `Matrix.isUnit_exp_add_one`: if a complex matrix `Y` has `‖Y‖ < π`, then `exp Y` has no
  eigenvalue `-1`; `Matrix.isUnit_exp_add_one_real` is the real case.
-/

public section

open NormedSpace
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Spectral mapping for the matrix exponential.** The spectrum of the exponential of a complex
square matrix is the image under the exponential of its spectrum. -/
theorem spectrum_exp (Y : Matrix m m ℂ) : spectrum ℂ (exp Y) = exp '' spectrum ℂ Y := by
  let +nondep : NormedAlgebra ℚ (Matrix m m ℂ) := .restrictScalars ℚ ℂ _
  let e := (toEuclideanCLM (n := m) (𝕜 := ℂ)).toAlgEquiv
  have he : Continuous e := LinearMap.continuous_of_finiteDimensional e.toLinearMap
  rw [← AlgEquiv.spectrum_eq e, ← AlgEquiv.spectrum_eq e Y, ← ContinuousLinearMap.spectrum_exp,
    NormedSpace.map_exp e he Y]

/-- Taking the exponential of a real matrix commutes with viewing it as a complex matrix. -/
theorem exp_map_ofReal (Y : Matrix m m ℝ) :
    exp (Y.map ((↑) : ℝ → ℂ)) = (exp Y).map ((↑) : ℝ → ℂ) := by
  let +nondep : NormedAlgebra ℚ (Matrix m m ℝ) := .restrictScalars ℚ ℝ _
  exact (NormedSpace.map_exp (Complex.ofRealHom.mapMatrix (m := m))
    (continuous_id.matrix_map Complex.continuous_ofReal) Y).symm

/-- **The eigenvalues of the exponential of a complex matrix.** Every eigenvalue `z` of `exp Y` is
`exp ν` for an eigenvalue `ν` of `Y` with `‖ν‖ ≤ ‖Y‖`, where `‖Y‖` is the `ℓ²` operator norm. -/
theorem exists_norm_le_exp_eq_of_mem_spectrum (Y : Matrix m m ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (exp Y)) :
    ∃ ν : ℂ, ‖ν‖ ≤ ‖Y‖ ∧ ν ∈ spectrum ℂ Y ∧ Complex.exp ν = z := by
  rcases isEmpty_or_nonempty m with hm | hm
  · simp [spectrum.of_subsingleton] at hz
  rw [spectrum_exp] at hz
  obtain ⟨ν, hν, rfl⟩ := hz
  exact ⟨ν, spectrum.norm_le_norm_of_mem hν, hν, by rw [Complex.exp_eq_exp_ℂ]⟩

/-- **A small invertible matrix has exponential without eigenvalue `1`.** If a complex matrix `Y` is
invertible and `‖Y‖ < 2π`, then `exp Y - 1` is invertible. -/
theorem isUnit_exp_sub_one {Y : Matrix m m ℂ} (hY : IsUnit Y) (hY2π : ‖Y‖ < 2 * Real.pi) :
    IsUnit (exp Y - 1) := by
  rw [← neg_sub, IsUnit.neg_iff]
  -- An eigenvalue `exp ν = 1` has `ν = 0`, which is not an eigenvalue of `Y`.
  by_contra h
  obtain ⟨ν, hνY, hν, hνe⟩ := exists_norm_le_exp_eq_of_mem_spectrum Y (z := 1) (by
    rw [spectrum.mem_iff, map_one]
    exact h)
  rw [Complex.eq_zero_of_exp_eq_one_of_norm_lt hνe (hνY.trans_lt hY2π),
    spectrum.zero_mem_iff] at hν
  exact hν hY

/-- **A small matrix has exponential without eigenvalue `-1`.** If a complex matrix `Y` has
`‖Y‖ < π`, then `exp Y + 1` is invertible. -/
theorem isUnit_exp_add_one {Y : Matrix m m ℂ} (hYπ : ‖Y‖ < Real.pi) : IsUnit (exp Y + 1) := by
  rw [← sub_neg_eq_add, ← neg_sub, IsUnit.neg_iff]
  by_contra h
  obtain ⟨ν, hνY, -, hνe⟩ := exists_norm_le_exp_eq_of_mem_spectrum Y (z := -1) (by
    rw [spectrum.mem_iff, map_neg, map_one]
    exact h)
  exact (Complex.pi_le_norm_of_exp_eq_neg_one hνe).not_gt (hνY.trans_lt hYπ)

/-- The real case of `Matrix.isUnit_exp_sub_one`: if a real matrix `Y` is invertible and
`‖Y‖ < 2π`, then `exp Y - 1` is invertible. -/
theorem isUnit_exp_sub_one_real {Y : Matrix m m ℝ} (hY : IsUnit Y) (hY2π : ‖Y‖ < 2 * Real.pi) :
    IsUnit (exp Y - 1) := by
  rw [← isUnit_map_ofReal_iff, Matrix.map_sub _ Complex.ofReal_sub,
    Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, ← exp_map_ofReal]
  exact isUnit_exp_sub_one (isUnit_map_ofReal_iff.2 hY) (by rwa [l2_opNorm_map_ofReal])

/-- The real case of `Matrix.isUnit_exp_add_one`: if a real matrix `Y` has `‖Y‖ < π`, then
`exp Y + 1` is invertible. -/
theorem isUnit_exp_add_one_real {Y : Matrix m m ℝ} (hYπ : ‖Y‖ < Real.pi) :
    IsUnit (exp Y + 1) := by
  rw [← isUnit_map_ofReal_iff, Matrix.map_add _ Complex.ofReal_add,
    Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, ← exp_map_ofReal]
  exact isUnit_exp_add_one (by rwa [l2_opNorm_map_ofReal])

end Matrix
