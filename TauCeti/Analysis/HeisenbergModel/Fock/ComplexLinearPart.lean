/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.ComplementaryMinor
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The complex-linear part of a signed unitary matrix

For signs `ε`, the matrix `C(u) = P₊ u P₊ + P₋ conj(u) P₋` retains the positive block of `u`
and the conjugate of its negative block. Its inverse supplies the substitution on polynomials
in the harmonic matrix-coefficient formula for the Fock representation.

We compute `det C(u) = det(u) * Δ_∞(u)^2` for `u ∈ U(ε)` and prove that `C(u)` is invertible.
The determinant computation uses Jacobi's complementary-minor identity and the signed-unitary
inverse formula. Nonvanishing follows from the already established triviality of the Fock
cocycle. We also describe the blocks, addition, real scaling, conjugate transposition, and
inversion of `C(u)`.

## References

* M. Kashiwara, M. Vergne, *On the Segal–Shale–Weil representations and harmonic polynomials*,
  Invent. Math. 44 (1978), 1–48.
* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535–552.
-/

public noncomputable section

open Matrix Complex
open scoped ComplexConjugate

namespace TauCeti.Fock

variable {ι : Type*} (ε : ι → ℤˣ)

/-- `P₊ u P₊ + P₋ conj(u) P₋`, the complex-linear part used for the Fock polynomial
substitution. Here `P₊` and `P₋` project onto the coordinates of sign `1` and `-1`. -/
def complexLinearPart (u : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ if ε i = ε j then if ε i = 1 then u i j else conj (u i j) else 0

/-- The entries of the complex-linear part. -/
theorem complexLinearPart_apply (u : Matrix ι ι ℂ) (i j : ι) :
    complexLinearPart ε u i j =
      if ε i = ε j then if ε i = 1 then u i j else conj (u i j) else 0 := (rfl)

@[simp]
theorem complexLinearPart_apply_of_ne (u : Matrix ι ι ℂ) {i j : ι} (h : ε i ≠ ε j) :
    complexLinearPart ε u i j = 0 := by
  simp [complexLinearPart_apply, h]

@[simp]
theorem complexLinearPart_apply_of_pos (u : Matrix ι ι ℂ) {i j : ι}
    (hi : ε i = 1) (hj : ε j = 1) : complexLinearPart ε u i j = u i j := by
  simp [complexLinearPart_apply, hi, hj]

@[simp]
theorem complexLinearPart_apply_of_neg (u : Matrix ι ι ℂ) {i j : ι}
    (hi : ε i = -1) (hj : ε j = -1) : complexLinearPart ε u i j = conj (u i j) := by
  simp [complexLinearPart_apply, hi, hj]

@[simp]
theorem complexLinearPart_zero : complexLinearPart ε (0 : Matrix ι ι ℂ) = 0 := by
  ext i j
  simp [complexLinearPart_apply]

@[simp]
theorem complexLinearPart_add (u v : Matrix ι ι ℂ) :
    complexLinearPart ε (u + v) = complexLinearPart ε u + complexLinearPart ε v := by
  ext i j
  simp only [Matrix.add_apply, complexLinearPart_apply]
  split_ifs <;> simp

@[simp]
theorem complexLinearPart_smul (r : ℝ) (u : Matrix ι ι ℂ) :
    complexLinearPart ε (r • u) = r • complexLinearPart ε u := by
  ext i j
  simp only [Matrix.smul_apply, complexLinearPart_apply]
  split_ifs <;> simp

@[simp]
theorem complexLinearPart_neg (u : Matrix ι ι ℂ) :
    complexLinearPart ε (-u) = -complexLinearPart ε u := by
  simpa using complexLinearPart_smul ε (-1) u

@[simp]
theorem complexLinearPart_sub (u v : Matrix ι ι ℂ) :
    complexLinearPart ε (u - v) = complexLinearPart ε u - complexLinearPart ε v := by
  simp [sub_eq_add_neg]

@[simp]
theorem complexLinearPart_conjTranspose (u : Matrix ι ι ℂ) :
    complexLinearPart ε uᴴ = (complexLinearPart ε u)ᴴ := by
  ext i j
  simp only [complexLinearPart_apply, conjTranspose_apply, star_def]
  by_cases h : ε i = ε j
  · rw [h]
    simp only [ite_true]
    split_ifs <;> simp
  · simp [h, Ne.symm h]

variable [DecidableEq ι]

@[simp]
theorem complexLinearPart_one : complexLinearPart ε (1 : Matrix ι ι ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [complexLinearPart_apply]
  · simp [complexLinearPart_apply, h]

omit [DecidableEq ι] in
/-- Splitting the indices into negative and positive signs makes the complex-linear part block
diagonal, with blocks `conj(u₋₋)` and `u₊₊`. -/
theorem complexLinearPart_submatrix (u : Matrix ι ι ℂ) :
    (complexLinearPart ε u).submatrix (Equiv.sumCompl fun i ↦ ε i = -1)
        (Equiv.sumCompl fun i ↦ ε i = -1) =
      fromBlocks ((negBlock ε u).map conj) 0 0
        (u.submatrix (fun i : {i // ε i ≠ -1} ↦ i.val) Subtype.val) := by
  have hp (i : {i // ε i ≠ -1}) : ε i = 1 :=
    (Int.units_eq_one_or (ε i)).resolve_right i.property
  ext (i | i) (j | j)
  · simp [Equiv.sumCompl, i.property, j.property]
  · simp [Equiv.sumCompl, i.property, hp j]
  · simp [Equiv.sumCompl, hp i, j.property]
  · simp [Equiv.sumCompl, hp i, hp j]

variable [Fintype ι]

/-- The entrywise definition agrees with `P₊ u P₊ + P₋ conj(u) P₋`. -/
theorem complexLinearPart_eq (u : Matrix ι ι ℂ) :
    complexLinearPart ε u =
      diagonal (fun i ↦ if ε i = 1 then (1 : ℂ) else 0) * u *
        diagonal (fun i ↦ if ε i = 1 then (1 : ℂ) else 0) +
      diagonal (fun i ↦ if ε i = -1 then (1 : ℂ) else 0) * u.map conj *
        diagonal (fun i ↦ if ε i = -1 then (1 : ℂ) else 0) := by
  ext i j
  rcases Int.units_eq_one_or (ε i) with hi | hi <;>
    rcases Int.units_eq_one_or (ε j) with hj | hj <;>
    simp [diagonal_mul, mul_diagonal, hi, hj]

/-- The determinant of the complex-linear part is the product of its two signed blocks. -/
theorem det_complexLinearPart_eq (u : Matrix ι ι ℂ) :
    (complexLinearPart ε u).det = conj (negBlock ε u).det *
      (u.submatrix (fun i : {i // ε i ≠ -1} ↦ i.val) Subtype.val).det := by
  rw [← det_submatrix_equiv_self (Equiv.sumCompl fun i ↦ ε i = -1),
    complexLinearPart_submatrix, det_fromBlocks_zero₂₁]
  congr 1
  exact ((starRingEnd ℂ).map_det _).symm

/-- On the signed unitary group, `det C(u) = det(u) * Δ_∞(u)^2`. -/
theorem det_complexLinearPart (g : unitaryGroup ε) :
    (complexLinearPart ε ((g : GL ι ℂ) : Matrix ι ι ℂ)).det =
      ((g : GL ι ℂ) : Matrix ι ι ℂ).det * multiplier ε g ^ 2 := by
  have h := det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl
    ((g : GL ι ℂ) : Matrix ι ι ℂ) (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)
    (by simp) (Equiv.sumCompl fun i ↦ ε i = -1) (Equiv.refl ι) (Equiv.refl ι)
  -- The complementary minor is the negative block of the group inverse. Its explicit formula
  -- removes the coordinate-equivalence wrappers in Jacobi's identity.
  have hminor :
      (((g : GL ι ℂ) : Matrix ι ι ℂ).submatrix
        (fun i : {i // ε i ≠ -1} ↦ i.val) Subtype.val).det =
      ((g : GL ι ℂ) : Matrix ι ι ℂ).det *
        (negBlock ε (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ)).det := by
    have hnb : negBlock ε (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) =
        (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ).submatrix
          (fun i : {i // ε i = -1} ↦ i.val) Subtype.val := by
      ext i j
      exact negBlock_apply _ _ _
    rw [hnb]
    simpa [Function.comp_def] using h
  rw [det_complexLinearPart_eq, hminor, negBlock_inv, det_conjTranspose, Complex.star_def,
    ← multiplier_apply]
  ring

/-- The complex-linear part of every signed unitary matrix has nonzero determinant. -/
theorem det_complexLinearPart_ne_zero (g : unitaryGroup ε) :
    (complexLinearPart ε ((g : GL ι ℂ) : Matrix ι ι ℂ)).det ≠ 0 := by
  have hΔ : multiplier ε g ≠ 0 := by
    have h := cocycle_multiplier (ε := ε) g 1
    intro hzero
    simp [HeisenbergDatum.Multiplier.cocycle_def, hzero] at h
  rw [det_complexLinearPart]
  exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero (g : GL ι ℂ)) (pow_ne_zero _ hΔ)

/-- The complex-linear part is invertible, so the inverse polynomial substitution is defined. -/
theorem isUnit_complexLinearPart (g : unitaryGroup ε) :
    IsUnit (complexLinearPart ε ((g : GL ι ℂ) : Matrix ι ι ℂ)) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact det_complexLinearPart_ne_zero ε g

/-- When the complex-linear part is invertible, its inverse is block diagonal, with the inverses
of the conjugate negative block and of the positive block. -/
theorem inv_complexLinearPart_submatrix (u : Matrix ι ι ℂ)
    (hu : IsUnit (complexLinearPart ε u)) :
    (complexLinearPart ε u)⁻¹.submatrix
        (Equiv.sumCompl fun i ↦ ε i = -1) (Equiv.sumCompl fun i ↦ ε i = -1) =
      fromBlocks (((negBlock ε u).map conj)⁻¹) 0 0
        ((u.submatrix (fun i : {i // ε i ≠ -1} ↦ i.val) Subtype.val)⁻¹) := by
  have h := (isUnit_submatrix_equiv (Equiv.sumCompl fun i ↦ ε i = -1)
    (Equiv.sumCompl fun i ↦ ε i = -1)).2 hu
  rw [complexLinearPart_submatrix, isUnit_fromBlocks_zero₂₁] at h
  rw [← inv_submatrix_equiv, complexLinearPart_submatrix,
    inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true h.1 h.2)]
  simp

/-- The inverse substitution does not mix coordinates of opposite signs, even when the
complex-linear part is singular (when its nonsingular inverse is zero). -/
@[simp]
theorem inv_complexLinearPart_apply_of_ne (u : Matrix ι ι ℂ) {i j : ι} (h : ε i ≠ ε j) :
    (complexLinearPart ε u)⁻¹ i j = 0 := by
  by_cases hu : IsUnit (complexLinearPart ε u)
  · let e := Equiv.sumCompl fun i ↦ ε i = -1
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    have hblocks := inv_complexLinearPart_submatrix ε u hu
    have hp (i : {i // ε i ≠ -1}) : ε i = 1 :=
      (Int.units_eq_one_or (ε i)).resolve_right i.property
    cases i with
    | inl i =>
      cases j with
      | inl j => exact (h (i.property.trans j.property.symm)).elim
      | inr j =>
        simpa [e, submatrix_apply] using congrFun (congrFun hblocks (Sum.inl i)) (Sum.inr j)
    | inr i =>
      cases j with
      | inl j =>
        simpa [e, submatrix_apply] using congrFun (congrFun hblocks (Sum.inr i)) (Sum.inl j)
      | inr j => exact (h ((hp i).trans (hp j).symm)).elim
  · rw [nonsing_inv_apply_not_isUnit _ ((isUnit_iff_isUnit_det _).not.mp hu)]
    rfl

/-- Taking the inverse in the signed unitary group conjugate-transposes its complex-linear part.
This is a statement about the group inverse of `g`, rather than the matrix inverse of `C(g)`. -/
theorem complexLinearPart_inv (g : unitaryGroup ε) :
    complexLinearPart ε (((g⁻¹ : unitaryGroup ε) : GL ι ℂ) : Matrix ι ι ℂ) =
      (complexLinearPart ε ((g : GL ι ℂ) : Matrix ι ι ℂ))ᴴ := by
  rw [← complexLinearPart_conjTranspose, Subgroup.coe_inv,
    val_inv_of_mem_unitaryGroupOf isUnit_signMatrix g.property, inv_signMatrix]
  ext i j
  by_cases h : ε i = ε j
  · rw [complexLinearPart_apply, complexLinearPart_apply]
    simp only [h, ↓reduceIte, signMatrix_eq_diagonal, diagonal_mul, mul_diagonal]
    rcases Int.units_eq_one_or (ε i) with hi | hi <;>
      simp [← h, hi]
  · simp [h]

end TauCeti.Fock
