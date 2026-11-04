/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Alexander
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Recognising elementary enlargements up to congruence

The row enlargement `TauCeti.KnotTheory.enlargeRow V η` adds two basis vectors `a = inr 0` and
`b = inr 1` to the basis of `V`: the column of `b` vanishes, and the row of `b` is the coordinate
vector of `a`. Adding a tube to a Seifert surface produces exactly this pattern, with `b` the
meridian of the tube and `a` a curve running once along it, but only after a change of basis: in a
basis adapted to the surface, the row of the meridian is in general a unit multiple of the
coordinate vector of the dual curve, and the other basis curves still link the dual curve.

This file shows that the pattern on the new basis vector `b` alone already forces the shape of an
enlargement up to unimodular congruence: subtracting multiples of `b` from the other basis vectors
clears their linking with `a`, and rescaling `a` normalises the unit. The transposed statement
gives the column enlargement `TauCeti.KnotTheory.enlargeColumn`.

## Main results

* `TauCeti.KnotTheory.exists_mul_mul_transpose_eq_enlargeRow`: a matrix in which the column of
  `inr 1` vanishes and its row is a unit multiple of the coordinate vector of `inr 0` is congruent,
  by a matrix with unit determinant, to the row enlargement of its upper left block.
* `TauCeti.KnotTheory.exists_mul_mul_transpose_eq_enlargeColumn`: the transposed statement.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8
  (S-equivalence of Seifert matrices).
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Recognising a row enlargement.** If the column of `inr 1` vanishes and the row of `inr 1` is
a unit `s` times the coordinate vector of `inr 0`, then `W` is congruent, by a matrix with unit
determinant, to the row enlargement of its upper left block. -/
theorem exists_mul_mul_transpose_eq_enlargeRow (W : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R) {s : Rˣ}
    (hrow : W (.inr 1) = Pi.single (.inr 0) (s : R)) (hcol : ∀ i, W i (.inr 1) = 0) :
    ∃ (P : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R) (η : ι → R), IsUnit P.det ∧
      P * W * Pᵀ = enlargeRow W.toBlocks₁₁ η := by
  -- rescale the vector `inr 0` by `s⁻¹`, so that the row of `inr 1` becomes its coordinate vector
  set d : ι ⊕ Fin 2 → R := Function.update 1 (.inr 0) ↑s⁻¹ with hd
  set W' := diagonal d * W * (diagonal d)ᵀ with hW'
  have hW'_apply : ∀ x y, W' x y = d x * W x y * d y := fun x y ↦ by
    simp [hW', diagonal_transpose, diagonal_mul, mul_diagonal]
  have hrow' : W' (.inr 1) = Pi.single (.inr 0) 1 := by
    ext y
    rw [hW'_apply, hrow]
    by_cases hy : y = .inr 0
    · subst hy
      simp [hd]
    · simp [hd, hy]
  have hcol' : W'.col (.inr 1) = 0 := by
    ext x
    simp [hW'_apply, hcol]
  -- then subtract from every other vector its linking with `inr 0` times the vector `inr 1`
  set u : ι ⊕ Fin 2 → R := Function.update (W'.col (.inr 0)) (.inr 1) 0 with hu
  set P₁ : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R := 1 - vecMulVec u (Pi.single (.inr 1) 1) with hP₁
  have hP₁det : P₁.det = 1 := by
    rw [hP₁, vecMulVec_eq Unit, det_one_sub_mul_comm, det_unique, Matrix.sub_apply,
      one_apply_eq, replicateRow_mul_replicateCol_apply, single_one_dotProduct]
    simp [hu]
  have hcongr : P₁ * W' * P₁ᵀ = W' - vecMulVec u (Pi.single (.inr 0) 1) := by
    have hright : W' * P₁ᵀ = W' := by
      rw [hP₁, transpose_sub, transpose_one, transpose_vecMulVec, Matrix.mul_sub, Matrix.mul_one,
        mul_vecMulVec, mulVec_single_one, hcol']
      simp
    have hleft : P₁ * W' = W' - vecMulVec u (Pi.single (.inr 0) 1) := by
      rw [hP₁, Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul, single_one_vecMul]
      simp [Matrix.row, hrow']
    rw [Matrix.mul_assoc, hright, hleft]
  refine ⟨P₁ * diagonal d, fun j ↦ ↑s⁻¹ * W (.inr 0) (.inl j), ?_, ?_⟩
  · rw [det_mul, hP₁det, one_mul, det_diagonal, Fintype.prod_eq_single (.inr 0)
      (fun x hx ↦ by simp [hd, hx])]
    simp [hd]
  · have hP : P₁ * diagonal d * W * (P₁ * diagonal d)ᵀ = P₁ * W' * P₁ᵀ := by
      simp only [hW', transpose_mul, Matrix.mul_assoc]
    rw [hP, hcongr]
    ext (x | x) (y | y) <;> (try fin_cases x) <;> (try fin_cases y) <;>
      simp [hW'_apply, hd, hcol, hrow, vecMulVec, hu, toBlocks₁₁]

/-- **Recognising a column enlargement.** If the row of `inr 1` vanishes and the column of `inr 1`
is a unit `s` times the coordinate vector of `inr 0`, then `W` is congruent, by a matrix with unit
determinant, to the column enlargement of its upper left block. -/
theorem exists_mul_mul_transpose_eq_enlargeColumn (W : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R)
    {s : Rˣ} (hcol : W.col (.inr 1) = Pi.single (.inr 0) (s : R))
    (hrow : ∀ j, W (.inr 1) j = 0) :
    ∃ (P : Matrix (ι ⊕ Fin 2) (ι ⊕ Fin 2) R) (ξ : ι → R), IsUnit P.det ∧
      P * W * Pᵀ = enlargeColumn W.toBlocks₁₁ ξ := by
  obtain ⟨P, ξ, hP, h⟩ := exists_mul_mul_transpose_eq_enlargeRow Wᵀ hcol hrow
  have hblock : Wᵀ.toBlocks₁₁ = W.toBlocks₁₁ᵀ := by ext; simp [toBlocks₁₁]
  refine ⟨P, ξ, hP, ?_⟩
  rw [← transpose_transpose (enlargeColumn _ _), ← transpose_transpose W.toBlocks₁₁,
    ← enlargeRow_def, ← hblock, ← h]
  simp [transpose_mul, Matrix.mul_assoc]

end TauCeti.KnotTheory
