/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# Singular values in dimension two

A linear map out of a two-dimensional inner product space has at most two nonzero singular values,
`σ₀ ≥ σ₁ ≥ 0`. This file computes them in closed form, which makes planar operators usable as
explicit models when testing whether a singular-value or unitarily-invariant-norm estimate is
sharp.

For `A : E →ₗ[𝕜] F` with `dim E = 2`, the squared singular values are the two eigenvalues of the
source Gram operator `A† A`, so their sum is `tr (A† A)` and their product is `det (A† A)`. Since
`σ₀² - σ₁² = √(tr (A† A)² - 4 det (A† A))`, the ordered pair `(σ₀², σ₁²)`, and hence the whole
singular-value sequence, is recovered from these two numbers.

For an orthonormal basis `(e₀, e₁)` of a two-dimensional space and the operators whose matrices in
that basis are `diag(d₀, d₁)` and `[[0, b], [c, 0]]`, the singular values are listed explicitly.
The symmetric off-diagonal matrix `[[0, r], [r, 0]]` has singular values `(‖r‖, ‖r‖)`, while the
one-sided triangular matrix `[[0, 0], [r, 0]]` has singular values `(‖r‖, 0, 0, …)`.

## Main declarations

* `LinearMap.singularValues_eq_single_add_single_of_finrank_eq_two`: on a two-dimensional source,
  the singular-value sequence is `(σ₀, σ₁, 0, 0, …)`.
* `LinearMap.trace_adjoint_comp_self_eq_of_finrank_eq_two`,
  `LinearMap.det_adjoint_comp_self_eq_of_finrank_eq_two`: `tr (A† A) = σ₀² + σ₁²` and
  `det (A† A) = σ₀² σ₁²`.
* `LinearMap.sq_singularValues_zero_of_finrank_eq_two`,
  `LinearMap.sq_singularValues_one_of_finrank_eq_two`: `σ₀², σ₁² = (t ± √(t² - 4δ)) / 2` with
  `t = tr (A† A)` and `δ = det (A† A)`.
* `LinearMap.singularValues_eq_iff_trace_eq_and_det_eq`: two maps out of two-dimensional spaces have
  the same singular values exactly when their Gram operators have the same trace and determinant.
* `Matrix.singularValues_toLin_diagonal_fin_two`: the singular values of `diag(d₀, d₁)` are
  `(‖d₀‖, ‖d₁‖, 0, …)` when `‖d₁‖ ≤ ‖d₀‖`.
* `Matrix.singularValues_toLin_offDiag_fin_two`: the singular values of `[[0, b], [c, 0]]` are
  `(‖c‖, ‖b‖, 0, …)` when `‖b‖ ≤ ‖c‖`, with the special cases
  `Matrix.singularValues_toLin_offDiag_self_fin_two` (`[[0, r], [r, 0]]`) and
  `Matrix.singularValues_toLin_offDiag_zero_fin_two` (`[[0, 0], [r, 0]]`).

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section I.2
  (singular values) and Section IV.2 (unitarily invariant norms).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.3.
-/

public section

open Module

namespace LinearMap

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

/-- On a two-dimensional source, the singular-value sequence of `A` is `(σ₀, σ₁, 0, 0, …)`. -/
theorem singularValues_eq_single_add_single_of_finrank_eq_two (A : E →ₗ[𝕜] F)
    (hE : finrank 𝕜 E = 2) :
    A.singularValues =
      Finsupp.single 0 (A.singularValues 0) + Finsupp.single 1 (A.singularValues 1) := by
  ext i
  rcases i with _ | _ | i
  · simp
  · simp
  · simp [A.singularValues_of_finrank_le (hE ▸ by omega : finrank 𝕜 E ≤ i + 2)]

/-- On a two-dimensional source, the trace of the Gram operator `A† A` is `σ₀² + σ₁²`. -/
theorem trace_adjoint_comp_self_eq_of_finrank_eq_two (A : E →ₗ[𝕜] F) (hE : finrank 𝕜 E = 2) :
    trace 𝕜 E (adjoint A ∘ₗ A) =
      ((A.singularValues 0 ^ 2 + A.singularValues 1 ^ 2 : ℝ) : 𝕜) := by
  rw [trace_adjoint_comp_self_eq_sum_sq_singularValues,
    Finsupp.sum_of_support_subset _ (s := Finset.range 2) (by
      rw [support_singularValues, Finset.range_subset_range, ← hE]
      exact A.finrank_range_le) _ fun _ _ ↦ by simp]
  simp [Finset.sum_range_succ]

/-- On a two-dimensional source, the determinant of the Gram operator `A† A` is `σ₀² σ₁²`. -/
theorem det_adjoint_comp_self_eq_of_finrank_eq_two (A : E →ₗ[𝕜] F) (hE : finrank 𝕜 E = 2) :
    (adjoint A ∘ₗ A).det = ((A.singularValues 0 ^ 2 * A.singularValues 1 ^ 2 : ℝ) : 𝕜) := by
  rw [A.isSymmetric_adjoint_comp_self.det_eq_prod_eigenvalues hE, Fin.prod_univ_two,
    ← A.sq_singularValues_fin hE, ← A.sq_singularValues_fin hE]
  simp

/-- On a two-dimensional source, the gap `σ₀² - σ₁²` between the squared singular values is the
square root of the discriminant `tr (A† A)² - 4 det (A† A)`. -/
private theorem sqrt_discrim_eq_of_finrank_eq_two (A : E →ₗ[𝕜] F) (hE : finrank 𝕜 E = 2) :
    √(RCLike.re (trace 𝕜 E (adjoint A ∘ₗ A)) ^ 2 - 4 * RCLike.re (adjoint A ∘ₗ A).det) =
      A.singularValues 0 ^ 2 - A.singularValues 1 ^ 2 := by
  rw [A.trace_adjoint_comp_self_eq_of_finrank_eq_two hE,
    A.det_adjoint_comp_self_eq_of_finrank_eq_two hE, RCLike.ofReal_re, RCLike.ofReal_re]
  have hle : A.singularValues 1 ^ 2 ≤ A.singularValues 0 ^ 2 :=
    pow_le_pow_left₀ (A.singularValues_nonneg 1) (A.singularValues_antitone zero_le_one) 2
  rw [← Real.sqrt_sq (sub_nonneg.mpr hle)]
  congr 1
  ring

/-- **Largest singular value in dimension two.** On a two-dimensional source,
`σ₀² = (t + √(t² - 4δ)) / 2` with `t = tr (A† A)` and `δ = det (A† A)`. -/
theorem sq_singularValues_zero_of_finrank_eq_two (A : E →ₗ[𝕜] F) (hE : finrank 𝕜 E = 2) :
    A.singularValues 0 ^ 2 = (RCLike.re (trace 𝕜 E (adjoint A ∘ₗ A)) +
      √(RCLike.re (trace 𝕜 E (adjoint A ∘ₗ A)) ^ 2 - 4 * RCLike.re (adjoint A ∘ₗ A).det)) / 2 := by
  rw [A.sqrt_discrim_eq_of_finrank_eq_two hE, A.trace_adjoint_comp_self_eq_of_finrank_eq_two hE,
    RCLike.ofReal_re]
  ring

/-- **Smallest singular value in dimension two.** On a two-dimensional source,
`σ₁² = (t - √(t² - 4δ)) / 2` with `t = tr (A† A)` and `δ = det (A† A)`. -/
theorem sq_singularValues_one_of_finrank_eq_two (A : E →ₗ[𝕜] F) (hE : finrank 𝕜 E = 2) :
    A.singularValues 1 ^ 2 = (RCLike.re (trace 𝕜 E (adjoint A ∘ₗ A)) -
      √(RCLike.re (trace 𝕜 E (adjoint A ∘ₗ A)) ^ 2 - 4 * RCLike.re (adjoint A ∘ₗ A).det)) / 2 := by
  rw [A.sqrt_discrim_eq_of_finrank_eq_two hE, A.trace_adjoint_comp_self_eq_of_finrank_eq_two hE,
    RCLike.ofReal_re]
  ring

/-- **Trace-determinant recovery in dimension two.** Two maps out of two-dimensional spaces have
the same singular values if and only if their Gram operators `A† A` and `B† B` have the same trace
and the same determinant. -/
theorem singularValues_eq_iff_trace_eq_and_det_eq (A : E →ₗ[𝕜] F) (B : E' →ₗ[𝕜] F')
    (hE : finrank 𝕜 E = 2) (hE' : finrank 𝕜 E' = 2) :
    A.singularValues = B.singularValues ↔
      trace 𝕜 E (adjoint A ∘ₗ A) = trace 𝕜 E' (adjoint B ∘ₗ B) ∧
        (adjoint A ∘ₗ A).det = (adjoint B ∘ₗ B).det := by
  refine ⟨fun h ↦ ?_, fun ⟨htr, hdet⟩ ↦ ?_⟩
  · rw [A.trace_adjoint_comp_self_eq_of_finrank_eq_two hE,
      B.trace_adjoint_comp_self_eq_of_finrank_eq_two hE',
      A.det_adjoint_comp_self_eq_of_finrank_eq_two hE,
      B.det_adjoint_comp_self_eq_of_finrank_eq_two hE', h]
    exact ⟨rfl, rfl⟩
  · have h0 : A.singularValues 0 = B.singularValues 0 := by
      rw [← sq_eq_sq₀ (A.singularValues_nonneg 0) (B.singularValues_nonneg 0),
        A.sq_singularValues_zero_of_finrank_eq_two hE,
        B.sq_singularValues_zero_of_finrank_eq_two hE', htr, hdet]
    have h1 : A.singularValues 1 = B.singularValues 1 := by
      rw [← sq_eq_sq₀ (A.singularValues_nonneg 1) (B.singularValues_nonneg 1),
        A.sq_singularValues_one_of_finrank_eq_two hE,
        B.sq_singularValues_one_of_finrank_eq_two hE', htr, hdet]
    rw [A.singularValues_eq_single_add_single_of_finrank_eq_two hE,
      B.singularValues_eq_single_add_single_of_finrank_eq_two hE', h0, h1]

end LinearMap

namespace Matrix

open LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Diagonal planar model.** If `‖d₁‖ ≤ ‖d₀‖`, the operator whose matrix in an orthonormal basis
`(e₀, e₁)` is `diag(d₀, d₁)` has singular-value sequence `(‖d₀‖, ‖d₁‖, 0, 0, …)`. For real
`s₀ ≥ s₁ ≥ 0` this is `(s₀, s₁, 0, 0, …)`. -/
theorem singularValues_toLin_diagonal_fin_two (e : OrthonormalBasis (Fin 2) 𝕜 E) {d₀ d₁ : 𝕜}
    (h : ‖d₁‖ ≤ ‖d₀‖) :
    (toLin e.toBasis e.toBasis (diagonal ![d₀, d₁])).singularValues =
      Finsupp.single 0 ‖d₀‖ + Finsupp.single 1 ‖d₁‖ := by
  have hanti : Antitone fun k ↦ ‖![d₀, d₁] (Equiv.refl (Fin 2) k)‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  rw [singularValues_eq_single_add_single_of_finrank_eq_two _
    (by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin])]
  congr 2
  · simpa using singularValues_toLin_diagonal e ![d₀, d₁] (Equiv.refl _) hanti 0
  · simpa using singularValues_toLin_diagonal e ![d₀, d₁] (Equiv.refl _) hanti 1

/-- **Off-diagonal planar model.** If `‖b‖ ≤ ‖c‖`, the operator whose matrix in an orthonormal
basis `(e₀, e₁)` is `[[0, b], [c, 0]]` has singular-value sequence `(‖c‖, ‖b‖, 0, 0, …)`: it is the
diagonal operator `diag(c, b)` followed by the isometry exchanging `e₀` and `e₁`. -/
theorem singularValues_toLin_offDiag_fin_two (e : OrthonormalBasis (Fin 2) 𝕜 E) {b c : 𝕜}
    (h : ‖b‖ ≤ ‖c‖) :
    (toLin e.toBasis e.toBasis !![0, b; c, 0]).singularValues =
      Finsupp.single 0 ‖c‖ + Finsupp.single 1 ‖b‖ := by
  have hswap : toLin e.toBasis e.toBasis !![0, b; c, 0] =
      (e.equiv e (Equiv.swap 0 1) : E →ₗ[𝕜] E) ∘ₗ toLin e.toBasis e.toBasis (diagonal ![c, b]) := by
    refine e.toBasis.ext fun i ↦ ?_
    rw [coe_comp, Function.comp_apply, toLin_self, toLin_self]
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hswap, singularValues_linearIsometryEquiv_comp, singularValues_toLin_diagonal_fin_two e h]

/-- **Symmetric off-diagonal planar model.** The operator whose matrix in an orthonormal basis
`(e₀, e₁)` is `[[0, r], [r, 0]]` has singular-value sequence `(‖r‖, ‖r‖, 0, 0, …)`. -/
@[simp]
theorem singularValues_toLin_offDiag_self_fin_two (e : OrthonormalBasis (Fin 2) 𝕜 E) (r : 𝕜) :
    (toLin e.toBasis e.toBasis !![0, r; r, 0]).singularValues =
      Finsupp.single 0 ‖r‖ + Finsupp.single 1 ‖r‖ :=
  singularValues_toLin_offDiag_fin_two e le_rfl

/-- **One-sided triangular planar model.** The operator whose matrix in an orthonormal basis
`(e₀, e₁)` is `[[0, 0], [r, 0]]` has singular-value sequence `(‖r‖, 0, 0, …)`. -/
@[simp]
theorem singularValues_toLin_offDiag_zero_fin_two (e : OrthonormalBasis (Fin 2) 𝕜 E) (r : 𝕜) :
    (toLin e.toBasis e.toBasis !![0, 0; r, 0]).singularValues = Finsupp.single 0 ‖r‖ := by
  simpa using singularValues_toLin_offDiag_fin_two e (b := 0) (c := r) (by simp)

end Matrix
