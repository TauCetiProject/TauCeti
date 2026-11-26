/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# The polynomials in `z` of degree `< n` as a copy of `ℂⁿ`

The Fourier monomials `z⁰, …, z^{n-1}` are orthonormal in `L²(AddCircle T)`, so sending the `j`-th
basis vector of `ℂⁿ` to `zʲ` is an isometric embedding `Vₙ : ℂⁿ → L²(AddCircle T)` onto
`span {z⁰, …, z^{n-1}}` (`TauCeti.fourierEmbedding`), the synthesis isometry
`Orthonormal.synthesisMapIsometry` of `z⁰, …, z^{n-1}`. Its adjoint takes the first `n` Fourier
coefficients (`Orthonormal.adjoint_synthesisMapIsometry_apply`), so it sends `zᵏ` to `eₖ` for
`0 ≤ k < n` and to `0` otherwise (`TauCeti.adjoint_fourierEmbedding_fourierLp`).

The multiplication representation of `C(AddCircle T, ℂ)` on `L²` sends the Fourier monomial `zᵐ`
to the shift `zᵏ ↦ z^{m+k}` (`TauCeti.continuousMapMultiplication_fourier_fourierLp`).
-/

public section

open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {T : ℝ} [Fact (0 < T)]

/-- The Fourier monomials `z⁰, …, z^{n-1}` are orthonormal in `L²(AddCircle T)`. -/
theorem orthonormal_fourierLp_fin (n : ℕ) :
    Orthonormal ℂ fun j : Fin n ↦ fourierLp (T := T) 2 (j : ℤ) :=
  orthonormal_fourier.comp _ fun i j h ↦ Fin.ext (by exact_mod_cast h)

/-- The isometric embedding of `ℂⁿ` onto the polynomials in `z` of degree `< n`,
`span {z⁰, …, z^{n-1}}`, in `L²(AddCircle T)`: the synthesis isometry of the orthonormal family
`z⁰, …, z^{n-1}`, sending the basis vector `eⱼ` to the Fourier monomial `zʲ`. -/
noncomputable abbrev fourierEmbedding (n : ℕ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] Lp ℂ 2 (haarAddCircle (T := T)) :=
  (orthonormal_fourierLp_fin n).synthesisMapIsometry.toContinuousLinearMap

/-- The adjoint of `fourierEmbedding n` sends the Fourier monomial `zᵏ` to the basis vector `eₖ`
when `0 ≤ k < n`, and to `0` otherwise. -/
theorem adjoint_fourierEmbedding_fourierLp (n : ℕ) (k : ℤ) :
    (fourierEmbedding (T := T) n).adjoint (fourierLp (T := T) 2 k) =
      if h : 0 ≤ k ∧ k < n then EuclideanSpace.single ⟨k.toNat, by omega⟩ 1 else 0 := by
  ext j
  rw [Orthonormal.adjoint_synthesisMapIsometry_apply, orthonormal_iff_ite.mp orthonormal_fourier]
  split_ifs with hjk h h
  · simp [← hjk]
  · omega
  · have hj : j ≠ ⟨k.toNat, by omega⟩ := by
      rintro rfl
      exact hjk (by simp [h.1])
    simp [hj]
  · simp

/-- Multiplication by the Fourier monomial `zᵐ` sends `zᵏ` to `z^{m+k}`. -/
@[simp]
theorem continuousMapMultiplication_fourier_fourierLp (m k : ℤ) :
    continuousMapMultiplication haarAddCircle (fourier m) (fourierLp (T := T) 2 k) =
      fourierLp (T := T) 2 (m + k) := by
  rw [continuousMapMultiplication_apply, Lp.multiplicationOperator_apply]
  exact fourierLp_smul_fourierLp m k

end TauCeti
