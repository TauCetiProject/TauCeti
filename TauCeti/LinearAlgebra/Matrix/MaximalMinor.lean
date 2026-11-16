/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Maximal minors and their gcd

A *maximal minor* of a matrix `A` with rows indexed by `m` and columns indexed by `n` is the
determinant `det (A.submatrix id e)` of the square submatrix on all the rows and on the columns
picked out by an embedding `e : m ↪ n`. Over an integral domain the rows of `A` are linearly
independent exactly when some maximal minor is nonzero, by the criterion in
`TauCeti.LinearAlgebra.Matrix.Rank`. That module also proves invariance of row independence under
scalar extension between domains.

Over a GCD domain, `Matrix.minorGcd A` is the normalized gcd of the maximal minors. Left
multiplication by a square matrix `B` multiplies every maximal minor by `det B`, so it multiplies
the minor gcd by `normalize (det B)` and leaves it unchanged for `B` invertible. For an integer
matrix `A` with linearly independent rows, the quotient `√det (A * Aᵀ) / minorGcd A` is the
covolume of the lattice of integer solutions of `A *ᵥ x = 0`, which enters the sharp form of
Siegel's lemma due to Bombieri and Vaaler; that quotient and its invariance under `A ↦ B * A`
are treated in `TauCeti.NumberTheory.Height.Arakelov.IntMatrix`. The examples at the end of the
file compute the minor gcd and Gram determinant of the row `[2, 2]` and of a matrix after a
unimodular shear; the matrix before the shear is treated in
`TauCeti.Examples.NumberTheory.Height.Arakelov.BombieriVaaler`.

The Gram determinant `det (A * Aᵀ)` is mostly treated elsewhere: its behaviour under
`A ↦ B * A` and its independence criterion are in `TauCeti.LinearAlgebra.Matrix.Gram`, and its
positivity, a consequence of the Cauchy–Binet formula, is in
`TauCeti.LinearAlgebra.ExteriorPower.Plucker`. Only its integer case under independence over `ℚ`,
`Matrix.det_mul_transpose_pos`, is stated here, next to the matching `Matrix.one_le_minorGcd`.

## Main definitions

* `Matrix.minorGcd`: the normalized gcd of the maximal minors.

## Main results

* `Matrix.det_submatrix_mul_left_of_det_eq_one`,
  `Matrix.IsUpperUnitriangular.det_submatrix_mul_left` and
  `Matrix.det_submatrix_mul_left_of_isUpperUnitriangular_transpose`: a row change of
  determinant one, in particular an upper or lower unitriangular one, preserves every maximal
  minor; `Matrix.det_submatrix_list_prod_mul_left` does the same for a composite of such changes,
  and the `mul_right` forms treat column changes.
* `Matrix.minorGcd_ne_zero_iff`: the minor gcd is nonzero exactly when the rows are linearly
  independent.
* `Matrix.minorGcd_mul_left` and `Matrix.minorGcd_unit_mul`: left multiplication by `B`
  multiplies the minor gcd by `normalize (det B)`, and leaves it unchanged for `B` invertible.
* `Matrix.minorGcd_eq_gcd_plucker`: the minor gcd is the gcd of the Plücker coordinates
  `TauCeti.plucker A.row` of the rows.
* `Matrix.one_le_minorGcd` and `Matrix.det_mul_transpose_pos`: the minor gcd of an integer
  matrix is at least `1` and its Gram determinant is positive when its rows are linearly
  independent over `ℚ`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* I. Aliev and M. Henk, *Minkowski's successive minima in convex and discrete geometry*,
  Commun. Math. **31** (2023), no. 2, 35–59, §6.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m]

/-- A minor of `B * A` on all the rows is `det B` times the corresponding minor of `A`. -/
theorem det_submatrix_mul_left [CommRing R] (B : Matrix m m R) (A : Matrix m n R) (e : m → n) :
    ((B * A).submatrix id e).det = B.det * (A.submatrix id e).det := by
  rw [submatrix_mul B A id id e Function.bijective_id, submatrix_id_id, det_mul]

/-! ### Row and column changes of determinant one -/

section DetEqOne

variable [CommRing R] {U : Matrix m m R}

/-- A row change of determinant one preserves every full-row minor. This is all that the
unitriangular forms below use. -/
theorem det_submatrix_mul_left_of_det_eq_one (hU : U.det = 1) (A : Matrix m n R) (c : m → n) :
    ((U * A).submatrix id c).det = (A.submatrix id c).det := by
  rw [det_submatrix_mul_left, hU, one_mul]

/-- An upper-unitriangular row change preserves every full-row minor. -/
theorem IsUpperUnitriangular.det_submatrix_mul_left [LinearOrder m]
    (hU : U.IsUpperUnitriangular) (A : Matrix m n R) (c : m → n) :
    ((U * A).submatrix id c).det = (A.submatrix id c).det :=
  det_submatrix_mul_left_of_det_eq_one hU.det_eq_one A c

/-- A lower-unitriangular row change, that is one whose transpose is upper unitriangular, preserves
every full-row minor. -/
theorem det_submatrix_mul_left_of_isUpperUnitriangular_transpose [LinearOrder m]
    (hU : Uᵀ.IsUpperUnitriangular) (A : Matrix m n R) (c : m → n) :
    ((U * A).submatrix id c).det = (A.submatrix id c).det :=
  det_submatrix_mul_left_of_det_eq_one (by rw [← det_transpose, hU.det_eq_one]) A c

/-- A composite of unitriangular row changes, each upper or lower unitriangular, preserves every
full-row minor. The shapes may be mixed, in which case the product need not be triangular: only
`det = 1` is preserved. -/
theorem det_submatrix_list_prod_mul_left [LinearOrder m] (L : List (Matrix m m R))
    (hL : ∀ U ∈ L, U.IsUpperUnitriangular ∨ Uᵀ.IsUpperUnitriangular) (A : Matrix m n R)
    (c : m → n) : ((L.prod * A).submatrix id c).det = (A.submatrix id c).det := by
  refine det_submatrix_mul_left_of_det_eq_one ?_ A c
  rw [← coe_detMonoidHom, map_list_prod]
  refine List.prod_eq_one fun x hx ↦ ?_
  obtain ⟨U, hU, rfl⟩ := List.mem_map.1 hx
  rcases hL U hU with h | h
  · exact h.det_eq_one
  · rw [coe_detMonoidHom, ← det_transpose, h.det_eq_one]

/-- A column change of determinant one preserves every full-column minor. For square `A` and
`r = id` this is `det (A * U) = det A`. -/
theorem det_submatrix_mul_right_of_det_eq_one (hU : U.det = 1) (A : Matrix n m R) (r : m → n) :
    ((A * U).submatrix r id).det = (A.submatrix r id).det := by
  rw [← det_transpose, transpose_submatrix, transpose_mul,
    det_submatrix_mul_left_of_det_eq_one (by rwa [det_transpose]), ← transpose_submatrix,
    det_transpose]

/-- An upper-unitriangular column change preserves every full-column minor. -/
theorem IsUpperUnitriangular.det_submatrix_mul_right [LinearOrder m]
    (hU : U.IsUpperUnitriangular) (A : Matrix n m R) (r : m → n) :
    ((A * U).submatrix r id).det = (A.submatrix r id).det :=
  det_submatrix_mul_right_of_det_eq_one hU.det_eq_one A r

/-- A lower-unitriangular column change preserves every full-column minor. -/
theorem det_submatrix_mul_right_of_isUpperUnitriangular_transpose [LinearOrder m]
    (hU : Uᵀ.IsUpperUnitriangular) (A : Matrix n m R) (r : m → n) :
    ((A * U).submatrix r id).det = (A.submatrix r id).det :=
  det_submatrix_mul_right_of_det_eq_one (by rw [← det_transpose, hU.det_eq_one]) A r

end DetEqOne

variable [Fintype n]

section Gcd

section NormalizedGCDMonoid

variable [CommRing R] [NormalizedGCDMonoid R]

/-- The gcd of the maximal minors of `A`: the normalized gcd of the determinants
`det (A.submatrix id e)` over all embeddings `e : m ↪ n`. It is `0` exactly when every maximal
minor vanishes, in particular when `n` has fewer elements than `m`. -/
noncomputable def minorGcd (A : Matrix m n R) : R :=
  Finset.univ.gcd fun e : m ↪ n ↦ (A.submatrix id e).det

theorem minorGcd_def (A : Matrix m n R) :
    A.minorGcd = Finset.univ.gcd fun e : m ↪ n ↦ (A.submatrix id e).det :=
  (rfl)

theorem minorGcd_dvd (A : Matrix m n R) (e : m ↪ n) : A.minorGcd ∣ (A.submatrix id e).det :=
  Finset.gcd_dvd (Finset.mem_univ e)

theorem dvd_minorGcd_iff {A : Matrix m n R} {a : R} :
    a ∣ A.minorGcd ↔ ∀ e : m ↪ n, a ∣ (A.submatrix id e).det := by
  simp [minorGcd_def, Finset.dvd_gcd_iff]

@[simp]
theorem normalize_minorGcd (A : Matrix m n R) : normalize A.minorGcd = A.minorGcd :=
  Finset.normalize_gcd

theorem minorGcd_eq_zero_iff {A : Matrix m n R} :
    A.minorGcd = 0 ↔ ∀ e : m ↪ n, (A.submatrix id e).det = 0 := by
  simp [minorGcd_def, Finset.gcd_eq_zero_iff]

/-- The minor gcd is nonzero exactly when the rows are linearly independent. -/
theorem minorGcd_ne_zero_iff [Nontrivial R] {A : Matrix m n R} :
    A.minorGcd ≠ 0 ↔ LinearIndependent R A.row := by
  have : IsDomain R := {}
  simp [minorGcd_eq_zero_iff, linearIndependent_row_iff_exists_det_submatrix_ne_zero]

/-- Left multiplication by an invertible matrix does not change the minor gcd. -/
@[simp]
theorem minorGcd_unit_mul (U : GL m R) (A : Matrix m n R) :
    minorGcd ((U : Matrix m m R) * A) = A.minorGcd := by
  simp only [minorGcd_def, det_submatrix_mul_left]
  refine Associated.eq_of_normalized ?_ Finset.normalize_gcd Finset.normalize_gcd
  exact (Finset.gcd_mul_left' _ _ _).trans
    ((associated_isUnit_mul_left_iff (isUnits_det_units U)).2 (.refl _))

end NormalizedGCDMonoid

/-- Left multiplication by `B` multiplies the minor gcd by `normalize (det B)`. -/
theorem minorGcd_mul_left [CommRing R] [StrongNormalizedGCDMonoid R] (B : Matrix m m R)
    (A : Matrix m n R) : minorGcd (B * A) = normalize B.det * A.minorGcd := by
  simp only [minorGcd_def, det_submatrix_mul_left, Finset.gcd_mul_left]

/-- For a matrix with rows indexed by `Fin p` and linearly ordered columns, the minor gcd is the
gcd of the Plücker coordinates of the rows: these are the maximal minors on columns taken in
increasing order, and every maximal minor is one of them up to sign. -/
theorem minorGcd_eq_gcd_plucker {ι : Type*} [Fintype ι] [LinearOrder ι] {p : ℕ} [CommRing R]
    [NormalizedGCDMonoid R] (A : Matrix (Fin p) ι R) :
    A.minorGcd = Finset.univ.gcd (TauCeti.plucker A.row) := by
  -- The Plücker coordinate at `s` is the maximal minor on the increasing enumeration of `s`.
  have hp (s) : (A.submatrix id (Set.powersetCard.ofFinEmbEquiv.symm s)).det =
      TauCeti.plucker A.row s :=
    (TauCeti.plucker_apply A.row s).symm
  refine dvd_antisymm_of_normalize_eq (normalize_minorGcd A) Finset.normalize_gcd
    (Finset.dvd_gcd fun s _ ↦ hp s ▸ minorGcd_dvd A _) (dvd_minorGcd_iff.2 fun e ↦ ?_)
  obtain ⟨σ, hσ⟩ := A.exists_det_submatrix_eq_sign_mul_plucker e
  rw [hσ]
  exact (Finset.gcd_dvd (Finset.mem_univ _)).mul_left _

end Gcd

section Int

theorem minorGcd_nonneg (A : Matrix m n ℤ) : 0 ≤ A.minorGcd :=
  Int.nonneg_of_normalize_eq_self (normalize_minorGcd A)

/-- The minor gcd of an integer matrix is positive exactly when its rows are linearly
independent. -/
theorem minorGcd_pos_iff {A : Matrix m n ℤ} : 0 < A.minorGcd ↔ LinearIndependent ℤ A.row := by
  rw [← minorGcd_ne_zero_iff, (minorGcd_nonneg A).lt_iff_ne', ne_eq]

/-- The minor gcd of an integer matrix whose rows are linearly independent over `ℚ` is at
least `1`. -/
theorem one_le_minorGcd {A : Matrix m n ℤ} (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    1 ≤ A.minorGcd :=
  minorGcd_pos_iff.2 (linearIndependent_rat_row_iff.1 hA)

/-- The Gram determinant of an integer matrix whose rows are linearly independent over `ℚ` is
positive. -/
theorem det_mul_transpose_pos {A : Matrix m n ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 0 < (A * A.transpose).det :=
  det_mul_transpose_pos_iff.2 (linearIndependent_rat_row_iff.1 hA)

end Int

/-! ### Examples -/

-- The row `[2, 2]` has independent rows, Gram determinant `8` and minor gcd `2`, so the quotient
-- `√8 / 2 = √2` is that of the row `[1, 1]`.
example : minorGcd !![(2 : ℤ), 2] = 2 := by
  have h (e : Fin 1 ↪ Fin 2) : (!![(2 : ℤ), 2].submatrix id e).det = 2 := by
    rw [det_unique, submatrix_apply]
    generalize e default = j
    fin_cases j <;> rfl
  refine dvd_antisymm_of_normalize_eq (normalize_minorGcd _) (by decide)
    (h ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩ ▸ minorGcd_dvd _ _) ?_
  exact dvd_minorGcd_iff.2 fun e ↦ (h e).symm ▸ dvd_rfl

example : (!![(2 : ℤ), 2] * !![(2 : ℤ), 2]ᵀ).det = 8 := by
  simp [det_unique, Function.swap, Matrix.vecHead, Matrix.vecTail]

-- The shear `!![1, 1; 0, 1]` moves `!![1, 0, -1; 0, 1, -1]` to `!![1, 1, -2; 0, 1, -1]`. Both
-- have minor gcd `1` and Gram determinant `3`, while the largest entry grows from `1` to `2`. The
-- matrix before the shear is treated in
-- `TauCeti.Examples.NumberTheory.Height.Arakelov.BombieriVaaler`.
example : minorGcd !![(1 : ℤ), 1, -2; 0, 1, -1] = 1 := by
  exact Int.eq_one_of_dvd_one (minorGcd_nonneg _)
    (by simpa [det_fin_two] using minorGcd_dvd !![(1 : ℤ), 1, -2; 0, 1, -1] ⟨![0, 1], by decide⟩)

example : (!![(1 : ℤ), 1, -2; 0, 1, -1] * !![(1 : ℤ), 1, -2; 0, 1, -1]ᵀ).det = 3 := by
  simp [det_fin_two, Function.swap, Matrix.vecHead, Matrix.vecTail]

end Matrix
