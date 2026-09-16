/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# The even and odd parts of the Leibniz expansion

The Leibniz formula writes the determinant of a square matrix as a signed sum over permutations.
Grouping its terms by the sign of the permutation gives two sums, `P` over the even and `N` over
the odd permutations, with `det M = P - N` and `permanent M = P + N`. A permutation of the rows or
of the columns of `M` either fixes both sums or exchanges them, according to its sign, so the
symmetric functions `P + N` and `P * N` are invariant under such permutations while `det M` is
only invariant up to sign. Together with `(P - N) ^ 2 = (P + N) ^ 2 - 4 * (P * N)` this is the
engine of Stickelberger's congruence for discriminants of number fields.

## Main definitions

* `Matrix.leibnizPart`: the sum of the Leibniz terms of the permutations of a given sign.

## Main results

* `Matrix.leibnizPart_one_sub_leibnizPart_neg_one`,
  `Matrix.leibnizPart_one_add_leibnizPart_neg_one`: the two parts recover the determinant and the
  permanent.
* `Matrix.leibnizPart_submatrix_left`, `Matrix.leibnizPart_submatrix_right`: permuting the rows or
  the columns by `ρ` shifts the sign by `Equiv.Perm.sign ρ`.
* `Matrix.leibnizPart_transpose`, `Matrix.leibnizPart_map`: invariance under transposition and
  naturality under ring homomorphisms.
* `Matrix.leibnizPart_one_mul_leibnizPart_neg_one_submatrix_left`,
  `Matrix.leibnizPart_one_mul_leibnizPart_neg_one_submatrix_right`: the product of the two parts
  is invariant under permutations of the rows and of the columns.
* `Matrix.det_sq_eq_permanent_sq_sub_four_mul`: `det M ^ 2 = permanent M ^ 2 - 4 * (P * N)`.

## References

* L. Stickelberger, *Über eine neue Eigenschaft der Diskriminanten algebraischer Zahlkörper*
  (1897).
* W. Narkiewicz, *Elementary and Analytic Theory of Algebraic Numbers*, Chapter 4.
-/

public section

namespace Matrix

open Equiv Equiv.Perm Finset

variable {n : Type*} [DecidableEq n] [Fintype n] {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The part of the Leibniz expansion of `M` indexed by the permutations of sign `s`: the sum of
`∏ i, M (σ i) i` over the permutations `σ` with `Equiv.Perm.sign σ = s`. -/
def leibnizPart (M : Matrix n n R) (s : ℤˣ) : R :=
  ∑ σ : Perm n with sign σ = s, ∏ i, M (σ i) i

/-- The defining sum of a Leibniz part. -/
theorem leibnizPart_def (M : Matrix n n R) (s : ℤˣ) :
    M.leibnizPart s = ∑ σ : Perm n with sign σ = s, ∏ i, M (σ i) i := by
  rw [leibnizPart]

/-- The Leibniz part as a sum over all permutations, the terms of the wrong sign being zero. -/
theorem leibnizPart_eq_sum_ite (M : Matrix n n R) (s : ℤˣ) :
    M.leibnizPart s = ∑ σ : Perm n, if sign σ = s then ∏ i, M (σ i) i else 0 := by
  rw [leibnizPart_def, sum_filter]

/-- The even part plus the odd part of the Leibniz expansion is the permanent. -/
theorem leibnizPart_one_add_leibnizPart_neg_one (M : Matrix n n R) :
    M.leibnizPart 1 + M.leibnizPart (-1) = M.permanent := by
  rw [leibnizPart_eq_sum_ite, leibnizPart_eq_sum_ite, ← sum_add_distrib, permanent]
  refine sum_congr rfl fun σ _ ↦ ?_
  rcases Int.units_eq_one_or (sign σ) with h | h <;> simp [h]

/-- Permuting the rows by `ρ` multiplies the sign index of a Leibniz part by `sign ρ`. -/
@[simp]
theorem leibnizPart_submatrix_left (M : Matrix n n R) (ρ : Perm n) (s : ℤˣ) :
    (M.submatrix ρ id).leibnizPart s = M.leibnizPart (sign ρ * s) := by
  rw [leibnizPart_eq_sum_ite, leibnizPart_eq_sum_ite, ← Equiv.sum_comp (Equiv.mulLeft ρ⁻¹)]
  refine sum_congr rfl fun σ _ ↦ ?_
  have hsign : sign ρ * sign σ = s ↔ sign σ = sign ρ * s := by
    rcases Int.units_eq_one_or (sign ρ) with h | h <;> simp [h, neg_eq_iff_eq_neg]
  simp [hsign]

/-- A Leibniz part is unchanged by transposition. -/
@[simp]
theorem leibnizPart_transpose (M : Matrix n n R) (s : ℤˣ) :
    Mᵀ.leibnizPart s = M.leibnizPart s := by
  rw [leibnizPart_eq_sum_ite, leibnizPart_eq_sum_ite, ← Equiv.sum_comp (Equiv.inv (Perm n))]
  refine sum_congr rfl fun σ _ ↦ ?_
  rw [Equiv.inv_apply, sign_inv, ← Equiv.prod_comp σ]
  simp

/-- Permuting the columns by `ρ` multiplies the sign index of a Leibniz part by `sign ρ`. -/
@[simp]
theorem leibnizPart_submatrix_right (M : Matrix n n R) (ρ : Perm n) (s : ℤˣ) :
    (M.submatrix id ρ).leibnizPart s = M.leibnizPart (sign ρ * s) := by
  rw [← leibnizPart_transpose, transpose_submatrix, leibnizPart_submatrix_left,
    leibnizPart_transpose]

/-- The product of the even and the odd Leibniz parts is invariant under permutations of the
rows. -/
theorem leibnizPart_one_mul_leibnizPart_neg_one_submatrix_left (M : Matrix n n R) (ρ : Perm n) :
    (M.submatrix ρ id).leibnizPart 1 * (M.submatrix ρ id).leibnizPart (-1) =
      M.leibnizPart 1 * M.leibnizPart (-1) := by
  rw [leibnizPart_submatrix_left, leibnizPart_submatrix_left]
  rcases Int.units_eq_one_or (sign ρ) with h | h <;> simp [h, mul_comm]

/-- The product of the even and the odd Leibniz parts is invariant under permutations of the
columns. -/
theorem leibnizPart_one_mul_leibnizPart_neg_one_submatrix_right (M : Matrix n n R) (ρ : Perm n) :
    (M.submatrix id ρ).leibnizPart 1 * (M.submatrix id ρ).leibnizPart (-1) =
      M.leibnizPart 1 * M.leibnizPart (-1) := by
  rw [leibnizPart_submatrix_right, leibnizPart_submatrix_right]
  rcases Int.units_eq_one_or (sign ρ) with h | h <;> simp [h, mul_comm]

/-- A ring homomorphism carries a Leibniz part of `M` to the Leibniz part of the mapped matrix. -/
@[simp]
theorem leibnizPart_map {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)
    (M : Matrix n n R) (s : ℤˣ) :
    (M.map f).leibnizPart s = f (M.leibnizPart s) := by
  simp [leibnizPart_def, map_sum, map_prod]

section CommRing

variable {R : Type*} [CommRing R]

/-- The even part minus the odd part of the Leibniz expansion is the determinant. -/
theorem leibnizPart_one_sub_leibnizPart_neg_one (M : Matrix n n R) :
    M.leibnizPart 1 - M.leibnizPart (-1) = M.det := by
  rw [leibnizPart_eq_sum_ite, leibnizPart_eq_sum_ite, ← sum_sub_distrib, det_apply]
  refine sum_congr rfl fun σ _ ↦ ?_
  rcases Int.units_eq_one_or (sign σ) with h | h <;> simp [h]

/-- The discriminant identity `(P - N) ^ 2 = (P + N) ^ 2 - 4 * (P * N)` for the two parts of the
Leibniz expansion. -/
theorem det_sq_eq_permanent_sq_sub_four_mul (M : Matrix n n R) :
    M.det ^ 2 = M.permanent ^ 2 - 4 * (M.leibnizPart 1 * M.leibnizPart (-1)) := by
  rw [← leibnizPart_one_sub_leibnizPart_neg_one, ← leibnizPart_one_add_leibnizPart_neg_one]
  ring

end CommRing

end Matrix

end
