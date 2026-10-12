/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

/-!
# Two-sided unimodular equivalence of matrices

Matrices related by `L * A * R` with `L` and `R` in `SL`. Nothing here assumes a Smith normal
form or a divisibility chain along a diagonal, so these facts sit below that theory rather
than inside it, and hold over an arbitrary finite index type. The corresponding statement for
merely invertible factors is `Matrix.GeneralLinearGroup.inv_mul_mul_inv_of_mul_mul_eq`, in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence`.

## Main results

* `Matrix.prod_eq_det_of_mul_mul_eq_diagonal`: the product of a diagonalisation's diagonal
  entries is the determinant.
* `Matrix.exists_SL_mul_mul_eq_of_mul_mul_eq`: two matrices carried to a common value by
  `SL`-transformations are themselves `SL`-equivalent.
* `Matrix.exists_eq_diagonal_mul_iff`: a matrix `A` with `det A = ∏ i, d i` a non-zero-divisor
  lies in `diagonal d * SL` exactly when `d i` divides every entry of the `i`-th row of `A`.
-/

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

public section

/-- **The product of a diagonalisation's diagonal entries is the determinant.** Both `SL`
factors have determinant `1`, so taking determinants through `L * A * R = diagonal d` leaves
the product of the diagonal.

No divisibility chain is assumed, so `d` need not be the invariant factors. -/
theorem prod_eq_det_of_mul_mul_eq_diagonal {S : Type*} [CommRing S]
    {A : Matrix ι ι S} {L R : SpecialLinearGroup ι S} {d : ι → S}
    (h : (L : Matrix ι ι S) * A * (R : Matrix ι ι S) = Matrix.diagonal d) :
    ∏ i, d i = A.det := by
  have hdet := congrArg Matrix.det h
  simp only [Matrix.det_mul, L.2, R.2, one_mul, mul_one, Matrix.det_diagonal] at hdet
  exact hdet.symm

/-- **Matrices sharing an `SL`-transform are `SL`-equivalent.** If `L_A A R_A = L_B B R_B`
then `L_B⁻¹ L_A` and `R_A R_B⁻¹` carry `A` to `B`.

Pure group algebra: nothing is assumed about the common value, which need not be diagonal.
Callers holding two diagonalisations with equal diagonals compose them into this single
hypothesis. -/
theorem exists_SL_mul_mul_eq_of_mul_mul_eq {S : Type*} [CommRing S]
    {A B : Matrix ι κ S} {LA LB : SpecialLinearGroup ι S} {RA RB : SpecialLinearGroup κ S}
    (h : (LA : Matrix ι ι S) * A * (RA : Matrix κ κ S) =
      (LB : Matrix ι ι S) * B * (RB : Matrix κ κ S)) :
    ∃ (P : SpecialLinearGroup ι S) (Q : SpecialLinearGroup κ S),
      (P : Matrix ι ι S) * A * (Q : Matrix κ κ S) = B := by
  refine ⟨LB⁻¹ * LA, RA * RB⁻¹, ?_⟩
  -- `toGL` is a monoid hom, so `map_inv` moves the inverse to the `SL` side and
  -- `coe_GL_coe_matrix` drops back to matrices; both inverses then normalise the same way
  simpa [SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← map_inv,
    SpecialLinearGroup.coe_GL_coe_matrix] using
    LB.toGL.inv_mul_mul_inv_of_mul_mul_eq RB.toGL h.symm

/-- **Right `SL`-cosets of a diagonal matrix.** If `det A = ∏ i, d i` is a left non-zero-divisor,
then `A = diagonal d * g` for some `g ∈ SL` exactly when `d i` divides every entry of the `i`-th
row of `A`. -/
theorem exists_eq_diagonal_mul_iff {S : Type*} [CommRing S] {d : ι → S} {A : Matrix ι ι S}
    (hA : A.det = ∏ i, d i) (hA₀ : IsLeftRegular A.det) :
    (∃ g : SpecialLinearGroup ι S, A = diagonal d * g) ↔ ∀ i j, d i ∣ A i j := by
  refine ⟨fun ⟨g, hg⟩ i j ↦ by simp [hg, diagonal_mul], fun h ↦ ?_⟩
  choose B hB using h
  have hAB : A = diagonal d * of B := by ext i j; simp [diagonal_mul, hB]
  -- `det A · det B = det A`, and `det A` is cancellable
  refine ⟨⟨of B, hA₀ ?_⟩, hAB⟩
  calc A.det * (of B).det = (diagonal d * of B).det := by rw [det_mul, det_diagonal, hA]
    _ = A.det * 1 := by rw [← hAB, mul_one]

end

end Matrix
