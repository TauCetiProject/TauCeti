/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import TauCeti.RingTheory.Polynomial.Subresultant.Polynomial
import Mathlib.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.Matrix

/-!
# Analyticity of subresultant coefficients and resultants

Fixed-bound subresultant coefficient minors, principal subresultant coefficients, and resultants are
determinants of Sylvester-type matrices whose entries are either zero or coefficients of the two
input polynomials up to the prescribed formal degree bounds `m` and `n`. When those finitely many
coefficients depend analytically on a parameter, so do all fixed-bound subresultant minors:

* `TauCeti.analyticWithinAt_subresultantCoeff`, `TauCeti.analyticAt_subresultantCoeff`,
  `TauCeti.analyticOn_subresultantCoeff`, `TauCeti.analyticOnNhd_subresultantCoeff`: analyticity of
  `x ↦ (F x).subresultantCoeff (G x) m n j k`.
* `TauCeti.analyticWithinAt_psc`, `TauCeti.analyticAt_psc`, `TauCeti.analyticOn_psc`,
  `TauCeti.analyticOnNhd_psc`: analyticity of principal subresultant coefficients
  `x ↦ (F x).psc (G x) m n j`.
* `TauCeti.analyticWithinAt_resultant`, `TauCeti.analyticAt_resultant`,
  `TauCeti.analyticOn_resultant`, `TauCeti.analyticOnNhd_resultant`: analyticity of fixed-bound
  resultants `x ↦ (F x).resultant (G x) m n`.
-/

public section

open Polynomial Set

namespace TauCeti

variable {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] {F G : E → 𝔸[X]} {s : Set E} {x₀ : E} {m n : ℕ}

/-- A fixed-bound subresultant coefficient minor depends analytically within `s` at `x₀` on the
input polynomial coefficients up to the formal degree bounds `m` and `n`. -/
theorem analyticWithinAt_subresultantCoeff
    (hF : ∀ i ≤ m, AnalyticWithinAt 𝕜 (fun x ↦ (F x).coeff i) s x₀)
    (hG : ∀ i ≤ n, AnalyticWithinAt 𝕜 (fun x ↦ (G x).coeff i) s x₀) (j k : ℕ) :
    AnalyticWithinAt 𝕜 (fun x ↦ (F x).subresultantCoeff (G x) m n j k) s x₀ := by
  simp_rw [Polynomial.subresultantCoeff_def]
  refine analyticWithinAt_matrix_det fun r c ↦ ?_
  induction c using Fin.addCases with
  | left c =>
    simp only [subresultantCoeffMatrix_castAdd]
    split_ifs <;> first | exact hG _ (by omega) | exact analyticWithinAt_const
  | right c =>
    simp only [subresultantCoeffMatrix_natAdd]
    split_ifs <;> first | exact hF _ (by omega) | exact analyticWithinAt_const

/-- A fixed-bound subresultant coefficient minor depends analytically at `x₀` on the input
polynomial coefficients up to the formal degree bounds `m` and `n`. -/
theorem analyticAt_subresultantCoeff
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀) (j k : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x).subresultantCoeff (G x) m n j k) x₀ := by
  simp_rw [← analyticWithinAt_univ] at hF hG ⊢
  exact analyticWithinAt_subresultantCoeff hF hG j k

/-- A fixed-bound subresultant coefficient minor is analytic on `s` when the input polynomial
coefficients up to `m` and `n` are analytic on `s`. -/
theorem analyticOn_subresultantCoeff
    (hF : ∀ i ≤ m, AnalyticOn 𝕜 (fun x ↦ (F x).coeff i) s)
    (hG : ∀ i ≤ n, AnalyticOn 𝕜 (fun x ↦ (G x).coeff i) s) (j k : ℕ) :
    AnalyticOn 𝕜 (fun x ↦ (F x).subresultantCoeff (G x) m n j k) s :=
  fun x hx ↦ analyticWithinAt_subresultantCoeff (fun i hi ↦ hF i hi x hx)
    (fun i hi ↦ hG i hi x hx) j k

/-- A fixed-bound subresultant coefficient minor is neighborhood-analytic on `s` when the input
polynomial coefficients up to `m` and `n` are neighborhood-analytic on `s`. -/
theorem analyticOnNhd_subresultantCoeff
    (hF : ∀ i ≤ m, AnalyticOnNhd 𝕜 (fun x ↦ (F x).coeff i) s)
    (hG : ∀ i ≤ n, AnalyticOnNhd 𝕜 (fun x ↦ (G x).coeff i) s) (j k : ℕ) :
    AnalyticOnNhd 𝕜 (fun x ↦ (F x).subresultantCoeff (G x) m n j k) s :=
  fun x hx ↦ analyticAt_subresultantCoeff (fun i hi ↦ hF i hi x hx) (fun i hi ↦ hG i hi x hx) j k

/-- A fixed-bound principal subresultant coefficient depends analytically within `s` at `x₀` on the
input polynomial coefficients up to the formal degree bounds `m` and `n`. -/
theorem analyticWithinAt_psc
    (hF : ∀ i ≤ m, AnalyticWithinAt 𝕜 (fun x ↦ (F x).coeff i) s x₀)
    (hG : ∀ i ≤ n, AnalyticWithinAt 𝕜 (fun x ↦ (G x).coeff i) s x₀) (j : ℕ) :
    AnalyticWithinAt 𝕜 (fun x ↦ (F x).psc (G x) m n j) s x₀ := by
  simp_rw [← Polynomial.subresultantCoeff_self]
  exact analyticWithinAt_subresultantCoeff hF hG j j

/-- A fixed-bound principal subresultant coefficient depends analytically at `x₀` on the input
polynomial coefficients up to the formal degree bounds `m` and `n`. -/
theorem analyticAt_psc
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀) (j : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ (F x).psc (G x) m n j) x₀ := by
  simp_rw [← Polynomial.subresultantCoeff_self]
  exact analyticAt_subresultantCoeff hF hG j j

/-- A fixed-bound principal subresultant coefficient is analytic on `s` when the input polynomial
coefficients up to `m` and `n` are analytic on `s`. -/
theorem analyticOn_psc
    (hF : ∀ i ≤ m, AnalyticOn 𝕜 (fun x ↦ (F x).coeff i) s)
    (hG : ∀ i ≤ n, AnalyticOn 𝕜 (fun x ↦ (G x).coeff i) s) (j : ℕ) :
    AnalyticOn 𝕜 (fun x ↦ (F x).psc (G x) m n j) s :=
  fun x hx ↦ analyticWithinAt_psc (fun i hi ↦ hF i hi x hx) (fun i hi ↦ hG i hi x hx) j

/-- A fixed-bound principal subresultant coefficient is neighborhood-analytic on `s` when the input
polynomial coefficients up to `m` and `n` are neighborhood-analytic on `s`. -/
theorem analyticOnNhd_psc
    (hF : ∀ i ≤ m, AnalyticOnNhd 𝕜 (fun x ↦ (F x).coeff i) s)
    (hG : ∀ i ≤ n, AnalyticOnNhd 𝕜 (fun x ↦ (G x).coeff i) s) (j : ℕ) :
    AnalyticOnNhd 𝕜 (fun x ↦ (F x).psc (G x) m n j) s :=
  fun x hx ↦ analyticAt_psc (fun i hi ↦ hF i hi x hx) (fun i hi ↦ hG i hi x hx) j

/-- A fixed-bound resultant depends analytically within `s` at `x₀` on the input polynomial
coefficients up to `m` and `n`. -/
theorem analyticWithinAt_resultant
    (hF : ∀ i ≤ m, AnalyticWithinAt 𝕜 (fun x ↦ (F x).coeff i) s x₀)
    (hG : ∀ i ≤ n, AnalyticWithinAt 𝕜 (fun x ↦ (G x).coeff i) s x₀) :
    AnalyticWithinAt 𝕜 (fun x ↦ (F x).resultant (G x) m n) s x₀ := by
  simp_rw [← Polynomial.psc_zero]
  exact analyticWithinAt_psc hF hG 0

/-- A fixed-bound resultant depends analytically at `x₀` on the input polynomial coefficients up
to `m` and `n`. -/
theorem analyticAt_resultant
    (hF : ∀ i ≤ m, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hG : ∀ i ≤ n, AnalyticAt 𝕜 (fun x ↦ (G x).coeff i) x₀) :
    AnalyticAt 𝕜 (fun x ↦ (F x).resultant (G x) m n) x₀ := by
  simp_rw [← Polynomial.psc_zero]
  exact analyticAt_psc hF hG 0

/-- A fixed-bound resultant is analytic on `s` when the input polynomial coefficients up to `m` and
`n` are analytic on `s`. -/
theorem analyticOn_resultant
    (hF : ∀ i ≤ m, AnalyticOn 𝕜 (fun x ↦ (F x).coeff i) s)
    (hG : ∀ i ≤ n, AnalyticOn 𝕜 (fun x ↦ (G x).coeff i) s) :
    AnalyticOn 𝕜 (fun x ↦ (F x).resultant (G x) m n) s :=
  fun x hx ↦ analyticWithinAt_resultant (fun i hi ↦ hF i hi x hx) (fun i hi ↦ hG i hi x hx)

/-- A fixed-bound resultant is neighborhood-analytic on `s` when the input polynomial coefficients
up to `m` and `n` are neighborhood-analytic on `s`. -/
theorem analyticOnNhd_resultant
    (hF : ∀ i ≤ m, AnalyticOnNhd 𝕜 (fun x ↦ (F x).coeff i) s)
    (hG : ∀ i ≤ n, AnalyticOnNhd 𝕜 (fun x ↦ (G x).coeff i) s) :
    AnalyticOnNhd 𝕜 (fun x ↦ (F x).resultant (G x) m n) s :=
  fun x hx ↦ analyticAt_resultant (fun i hi ↦ hF i hi x hx) (fun i hi ↦ hG i hi x hx)

end TauCeti

end
