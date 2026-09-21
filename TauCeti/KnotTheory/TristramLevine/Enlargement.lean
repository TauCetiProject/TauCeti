/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.TristramLevine.Basic

/-!
# Tristram--Levine signature under Seifert-matrix enlargement

The two elementary enlargements of a Seifert matrix preserve its Tristram--Levine signature.
Together with congruence invariance, these are the algebraic identities needed for invariance
under S-equivalence. The statements hold for every complex parameter, including `ω = 1`,
where the form vanishes; no condition on the Alexander polynomial is needed.

The input remains a real matrix: this does not construct a Seifert surface or assert
knot-concordance invariance at roots of the Alexander polynomial.

The calculation follows W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175,
Chapter 8, Theorem 8.9.

Formal source: `TauCeti.KnotTheory.signature_enlargeColumn` in
`TauCeti.KnotTheory.Signature`.
-/

public section

open Matrix
open scoped ComplexConjugate

namespace TauCeti.KnotTheory

variable {ι : Type*}

/-- The Tristram--Levine form of a column enlargement: the original form is bordered by
one weighted enlargement vector and a two-dimensional Hermitian zero-diagonal block. -/
@[simp]
theorem tristramLevineForm_enlargeColumn (V : Matrix ι ι ℝ) (ξ : ι → ℝ) (ω : ℂ) :
    tristramLevineForm (enlargeColumn V ξ) ω =
      fromBlocks (tristramLevineForm V ω)
        ((1 - ω) • (enlargeBlock ξ).map ((↑) : ℝ → ℂ))
        (((1 - ω) • (enlargeBlock ξ).map ((↑) : ℝ → ℂ))ᴴ)
        !![0, 1 - ω; 1 - conj ω, 0] := by
  ext (i | i) (j | j)
  · simp
  · fin_cases j <;> simp
  · fin_cases i <;> simp [Matrix.conjTranspose_apply]
  · fin_cases i <;> fin_cases j <;> simp

variable [Fintype ι]

/-- A column enlargement preserves the Tristram--Levine signature at every complex parameter. -/
@[simp]
theorem tristramLevineSignature_enlargeColumn (V : Matrix ι ι ℝ) (ξ : ι → ℝ) (ω : ℂ) :
    tristramLevineSignature (enlargeColumn V ξ) ω = tristramLevineSignature V ω := by
  classical
  by_cases hω : ω = 1
  · subst ω
    simp
  have hb : 1 - conj ω ≠ 0 := by
    intro h
    have h' : 1 - ω = 0 := by simpa using congrArg conj h
    exact hω (sub_eq_zero.mp h').symm
  let E : Matrix ι (Fin 2) ℂ := (1 - ω) • (enlargeBlock ξ).map ((↑) : ℝ → ℂ)
  let F : Matrix ι (Fin 2) ℂ := of fun i => ![0, -(1 - ω) * ξ i / (1 - conj ω)]
  let H : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1 - ω; 1 - conj ω, 0]
  have hH : H.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]
  have hFE : F * Eᴴ = 0 := by
    ext i j
    simp [F, E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  have hEF : E + F * H = 0 := by
    ext i j
    fin_cases j <;> simp [F, E, H, Matrix.mul_apply, Fin.sum_univ_two, hb]
    ring
  have hEH : Eᴴ + H * Fᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hEF
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hH.eq,
      Matrix.conjTranspose_zero] using h
  let P : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) ℂ := fromBlocks 1 F 0 1
  have hP : IsUnit P.det := by
    simp [P]
  have hcong : P * tristramLevineForm (enlargeColumn V ξ) ω * Pᴴ =
      fromBlocks (tristramLevineForm V ω) 0 0 H := by
    rw [tristramLevineForm_enlargeColumn]
    -- `rw` leaves the local block aliases folded inside `fromBlocks`; no rewrite lemma
    -- can match through those aliases, so `change` unfolds only their definitional equalities.
    change fromBlocks 1 F 0 1 * fromBlocks (tristramLevineForm V ω) E Eᴴ H *
      (fromBlocks 1 F 0 1)ᴴ = _
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero, hFE, hEF, zero_add, add_zero, hEH]
  have h : ((isHermitian_tristramLevineForm V ω).fromBlocks
      Matrix.conjTranspose_zero hH).signature =
      (isHermitian_tristramLevineForm (enlargeColumn V ξ) ω).signature := by
    convert (isHermitian_tristramLevineForm (enlargeColumn V ξ) ω).signature_congr hP using 2
    exact hcong.symm
  have hzero : hH.signature = 0 :=
    hH.signature_eq_zero_of_fin_two_diagonal_eq_zero (by simp [H]) (by simp [H])
  rw [(isHermitian_tristramLevineForm V ω).signature_fromBlocks_zero hH, hzero, add_zero] at h
  simpa only [tristramLevineSignature_def] using h.symm

/-- A row enlargement preserves the Tristram--Levine signature at every complex parameter. -/
@[simp]
theorem tristramLevineSignature_enlargeRow (V : Matrix ι ι ℝ) (η : ι → ℝ) (ω : ℂ) :
    tristramLevineSignature (enlargeRow V η) ω = tristramLevineSignature V ω := by
  have hrow : enlargeRow V η = (enlargeColumn Vᵀ η)ᵀ := by
    ext (i | i) (j | j)
    · simp [Matrix.transpose_apply]
    · fin_cases j <;> simp [Matrix.transpose_apply]
    · fin_cases i <;> simp [Matrix.transpose_apply]
    · fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  rw [hrow, tristramLevineSignature_transpose,
    tristramLevineSignature_enlargeColumn, tristramLevineSignature_transpose]

end TauCeti.KnotTheory
