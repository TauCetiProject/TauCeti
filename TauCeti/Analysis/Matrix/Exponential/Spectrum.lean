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
import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# The spectrum of the exponential of a matrix

For a complex square matrix `Y`, the eigenvalues of `exp Y` are the exponentials of the eigenvalues
of `Y` (`Matrix.spectrum_exp`): this is the spectral mapping theorem for the exponential of an
operator on a finite-dimensional complex space, `ContinuousLinearMap.spectrum_exp`, read through
the star algebra equivalence `Matrix.toEuclideanCLM`.

For a real square matrix `Y` the complex eigenvalues of `exp Y` are therefore the values `exp ν` at
complex eigenvalues `ν` of `Y`, and these satisfy `‖ν‖ ≤ ‖Y‖` for the `ℓ²` operator norm
(`Matrix.exists_norm_le_exp_eq_of_mem_spectrum`). This is how one shows that `exp Y` has no
eigenvalue `1`, or no eigenvalue `-1`, when `Y` is small: such an eigenvalue forces `ν ∈ 2π i ℤ`,
respectively `ν ∈ π i (2 ℤ + 1)`.

## Main results

* `Matrix.spectrum_exp`: the spectrum of `exp Y` is the image of the spectrum of `Y` under `exp`.
* `Matrix.exp_map_ofReal`: the exponential commutes with viewing a real matrix as a complex one.
* `Matrix.exists_norm_le_exp_eq_of_mem_spectrum`: every complex eigenvalue of `exp Y`, for a real
  matrix `Y`, is `exp ν` for a complex eigenvalue `ν` of `Y` with `‖ν‖ ≤ ‖Y‖`.
* `Matrix.isUnit_exp_sub_one`: if `Y` is invertible and `‖Y‖ < 2π`, then `exp Y` has no
  eigenvalue `1`.
* `Matrix.isUnit_exp_add_one`: if `‖Y‖ < π`, then `exp Y` has no eigenvalue `-1`.
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

/-- The exponential of a real matrix, viewed as a complex matrix, is the exponential of the
complex matrix. -/
theorem exp_map_ofReal (Y : Matrix m m ℝ) :
    (exp Y).map ((↑) : ℝ → ℂ) = exp (Y.map ((↑) : ℝ → ℂ)) := by
  let +nondep : NormedAlgebra ℚ (Matrix m m ℝ) := .restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (Complex.ofRealHom.mapMatrix (m := m))
    (continuous_id.matrix_map Complex.continuous_ofReal) Y

/-- **The eigenvalues of the exponential of a real matrix.** Every complex eigenvalue `z` of
`exp Y`, for a real matrix `Y`, is `exp ν` for a complex eigenvalue `ν` of `Y` with
`‖ν‖ ≤ ‖Y‖`, where `‖Y‖` is the `ℓ²` operator norm. -/
theorem exists_norm_le_exp_eq_of_mem_spectrum (Y : Matrix m m ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ ((exp Y).map ((↑) : ℝ → ℂ))) :
    ∃ ν : ℂ, ‖ν‖ ≤ ‖Y‖ ∧ ν ∈ spectrum ℂ (Y.map ((↑) : ℝ → ℂ)) ∧ Complex.exp ν = z := by
  rcases isEmpty_or_nonempty m with hm | hm
  · simp [spectrum.of_subsingleton] at hz
  rw [exp_map_ofReal, spectrum_exp] at hz
  obtain ⟨ν, hν, rfl⟩ := hz
  exact ⟨ν, (spectrum.norm_le_norm_of_mem hν).trans_eq (l2_opNorm_map_ofReal Y), hν,
    by rw [Complex.exp_eq_exp_ℂ]⟩

/-- **A small invertible real matrix has exponential without eigenvalue `1`.** If `Y` is invertible
and `‖Y‖ < 2π`, then `exp Y - 1` is invertible. -/
theorem isUnit_exp_sub_one {Y : Matrix m m ℝ} (hY : IsUnit Y) (hY2π : ‖Y‖ < 2 * Real.pi) :
    IsUnit (exp Y - 1) := by
  rw [← isUnit_map_ofReal_iff, Matrix.map_sub _ Complex.ofReal_sub,
    Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, ← neg_sub, IsUnit.neg_iff]
  -- An eigenvalue `exp ν = 1` has `ν ∈ 2π i ℤ` with `‖ν‖ < 2π`, so `ν = 0`, which is not an
  -- eigenvalue of `Y`.
  by_contra h
  obtain ⟨ν, hνY, hν, hνe⟩ := exists_norm_le_exp_eq_of_mem_spectrum Y (z := 1) (by
    rw [spectrum.mem_iff, map_one]
    exact h)
  obtain ⟨k, rfl⟩ := Complex.exp_eq_one_iff.1 hνe
  have hk : k = 0 := by
    by_contra hk
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hnorm : ‖(k : ℂ) * (2 * Real.pi * Complex.I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_I, mul_one, norm_mul,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  subst hk
  rw [Int.cast_zero, zero_mul, spectrum.zero_mem_iff, isUnit_map_ofReal_iff] at hν
  exact hν hY

/-- **A small real matrix has exponential without eigenvalue `-1`.** If `‖Y‖ < π`, then
`exp Y + 1` is invertible. -/
theorem isUnit_exp_add_one {Y : Matrix m m ℝ} (hYπ : ‖Y‖ < Real.pi) : IsUnit (exp Y + 1) := by
  rw [← isUnit_map_ofReal_iff, Matrix.map_add _ Complex.ofReal_add,
    Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one, ← sub_neg_eq_add, ← neg_sub,
    IsUnit.neg_iff]
  by_contra h
  obtain ⟨ν, hνY, -, hνe⟩ := exists_norm_le_exp_eq_of_mem_spectrum Y (z := -1) (by
    rw [spectrum.mem_iff, map_neg, map_one]
    exact h)
  -- `exp ν = -1` forces `ν = (2k + 1) π i`.
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (show Complex.exp (ν - Real.pi * Complex.I) = 1 by
    rw [Complex.exp_sub, hνe, Complex.exp_pi_mul_I, neg_div_neg_eq, div_one])
  have hν : ν = ((2 * k + 1 : ℤ) : ℂ) * (Real.pi * Complex.I) := by
    rw [sub_eq_iff_eq_add] at hk
    rw [hk]
    push_cast
    ring
  have h1 : (1 : ℝ) ≤ |((2 * k + 1 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (by omega)
  have hnorm : ‖ν‖ = |((2 * k + 1 : ℤ) : ℝ)| * Real.pi := by
    rw [hν, norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

end Matrix
