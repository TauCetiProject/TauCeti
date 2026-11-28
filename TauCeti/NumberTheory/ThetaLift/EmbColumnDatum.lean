/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.StandardColumns
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.EmbRowStabilizer

/-!
# The column datum of an embedding

Let `φ : R →+* S` be a ring homomorphism, `e : r ↪ n` an embedding of finite index types and `w`
a matrix over `S` with columns indexed by `n`. For a function `χ : R → C`, typically a
multiplicative character, the column datum `embColumnDatum χ φ w e` is the function of an
`n × r` matrix `σ` over `R` equal to `χ (σ.submatrix e id).det` if `w * σ.map φ` is the matrix
of the columns `e` of `w`, and `0` otherwise. The columns `e` of `w` are `w` times the inclusion
matrix of `e`.

The main result says that the column datum at the columns `e` of a matrix `z ∈ GL n R` with
standard columns off `e` records exactly whether `z` lies in the row stabiliser
`embRowStabilizer φ w e`, together with `χ (det z)`: if `F` is invariant under left
multiplication by the row stabiliser, then `χ (det z) * F (z⁻¹ * y)`, cut off to `z` in the row
stabiliser, is the column datum at the columns `e` of `z` times `F y`.

The column datum is unrelated to the standard row and column data
`Subring.standardRowDatum` and `Subring.standardColDatum`.

## Main definitions

* `TauCeti.embColumnDatum χ φ w e`: the column datum.

## Main results

* `TauCeti.embColumnDatum_mul_eq_ite_mem_embRowStabilizer`: the column datum identity.

## References

The statements follow the formal proof in the folder `grh` of
https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`New/OneLift/ComparisonOperator/OneExchange.lean` (`New.Rows.columnDatum`,
`New.Rows.columnDatum_mul_ite_eq_ite_mem_rowStabilizer`).
-/

public section

open Matrix

namespace TauCeti

variable {n r m R S C : Type*} [Fintype n] [Fintype r] [DecidableEq r]
  [CommRing R] [Semiring S]

open Classical in
/-- The column datum of `χ` for `(φ, w, e)`: at an `n × r` matrix `σ` over `R`, it is
`χ` of the determinant of the rows `e` of `σ` if `w * σ.map φ` is the matrix of the columns `e`
of `w` (that is, `w` times the inclusion matrix of `e`), and `0` otherwise. -/
noncomputable def embColumnDatum [Zero C] (χ : R → C) (φ : R →+* S) (w : Matrix m n S)
    (e : r ↪ n) (σ : Matrix n r R) : C :=
  if w * σ.map φ = w.submatrix id e then χ (σ.submatrix e id).det else 0

variable {χ : R → C} {φ : R →+* S} {w : Matrix m n S} {e : r ↪ n} {σ : Matrix n r R}

/-- The column datum as a conditional, for any decidability instance of its condition. -/
theorem embColumnDatum_def [Zero C] [Decidable (w * σ.map φ = w.submatrix id e)] :
    embColumnDatum χ φ w e σ =
      if w * σ.map φ = w.submatrix id e then χ (σ.submatrix e id).det else 0 := by
  unfold embColumnDatum
  congr

/-- Where `w * σ.map φ` is the matrix of the columns `e` of `w`, the column datum is `χ` of the
determinant of the rows `e` of `σ`. -/
@[simp]
theorem embColumnDatum_of_mul_map_eq [Zero C] (h : w * σ.map φ = w.submatrix id e) :
    embColumnDatum χ φ w e σ = χ (σ.submatrix e id).det := by
  simp [embColumnDatum, h]

/-- Where `w * σ.map φ` is not the matrix of the columns `e` of `w`, the column datum vanishes. -/
@[simp]
theorem embColumnDatum_of_mul_map_ne [Zero C] (h : w * σ.map φ ≠ w.submatrix id e) :
    embColumnDatum χ φ w e σ = 0 := by
  simp [embColumnDatum, h]

/-- **The column datum identity.** Let `F` be a function of `n × c` matrices over `R` that is
invariant under left multiplication by the row stabiliser `H(φ, w, e)`, and let `z ∈ GL n R`
have the columns of the identity matrix off the image of `e`. Then the column datum at the
columns `e` of `z` times `F y` equals `χ (det z) * F (z⁻¹ * y)` if `z ∈ H(φ, w, e)`, and `0`
otherwise. -/
theorem embColumnDatum_mul_eq_ite_mem_embRowStabilizer [DecidableEq n] [MulZeroClass C]
    [DecidablePred (· ∈ embRowStabilizer φ w e)] {c : Type*}
    {F : Matrix n c R → C}
    (hF : ∀ A ∈ embRowStabilizer φ w e, ∀ y, F ((A : Matrix n n R) * y) = F y) {z : GL n R}
    (hz : z ∈ columnRowFixingSubgroup R (Set.range e)ᶜ ∅) (y : Matrix n c R) :
    embColumnDatum χ φ w e ((z : Matrix n n R).submatrix id e) * F y =
      if z ∈ embRowStabilizer φ w e then
        χ (z : Matrix n n R).det * F ((↑z⁻¹ : Matrix n n R) * y)
      else 0 := by
  have hmem := mem_embRowStabilizer_iff_of_mem_columnRowFixingSubgroup (φ := φ) (w := w) hz
  split_ifs with hzH
  · rw [embColumnDatum_of_mul_map_eq (hmem.mp hzH), submatrix_submatrix, Function.id_comp,
      Function.comp_id, det_eq_det_submatrix_of_col_eq_one e
        (mem_columnRowFixingSubgroup_iff.mp hz).1, hF _ (inv_mem hzH)]
  · rw [embColumnDatum_of_mul_map_ne (mt hmem.mpr hzH), zero_mul]

end TauCeti
