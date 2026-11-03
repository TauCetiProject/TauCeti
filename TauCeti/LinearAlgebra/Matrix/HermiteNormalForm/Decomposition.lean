/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Hermite decompositions of integer matrices

For an `m × n` integer matrix `A`, a *Hermite decomposition* consists of `k ≤ n`, an `m × k`
matrix `H` in (column-style, upper) Hermite normal form, and integer `n × n` matrices `U`, `U'`
with `U * U' = U' * U = 1` such that `A * U = [H | 0]`: the first `k` columns of `A * U` are the
columns of `H` and the remaining `n - k` columns vanish. This is the shape in which a Hermite
normal form algorithm returns its result, with the unimodular transformation and its inverse
recorded explicitly, so that both the lattice equality and the reconstruction `A = [H | 0] * U'`
can be checked.

From such a decomposition we read off the invariants of `A` that do not depend on the choice of
`U`: the column lattice of `A` (the range of `A.mulVecLin`) is the column lattice of `H`, and `k`
is the rank of `A`, over `ℤ` and over every domain of characteristic zero, such as `ℚ`.

## Main definitions

* `Matrix.hermitePad H n`: the matrix `[H | 0]`, an `m × k` matrix padded with zero columns to
  `m × n`.
* `Matrix.IsHermiteDecomposition A H U U'`: `A * U = [H | 0]` with `H` in Hermite normal form,
  `k ≤ n`, and `U'` a two-sided inverse of `U`.

## Main results

* `Matrix.range_mulVecLin_hermitePad`, `Matrix.rank_hermitePad`: padding with zero columns
  changes neither the column lattice nor the rank.
* `Matrix.IsHermiteDecomposition.eq_hermitePad_mul`: the reconstruction `A = [H | 0] * U'`.
* `Matrix.IsHermiteDecomposition.range_mulVecLin_eq`: the column lattice of `A` is that of `H`.
* `Matrix.IsHermiteDecomposition.rank_map_eq`, `Matrix.IsHermiteDecomposition.rank_eq`: `k` is
  the rank of `A` over any domain of characteristic zero, and over `ℤ`.
* `Matrix.IsHermiteDecomposition.isUnit_det`,
  `Matrix.IsHermiteDecomposition.det_eq_one_or_neg_one`: `U` is unimodular, with determinant `±1`.

## References

* Daniele Micciancio, *CSE 206A: Lattice Algorithms and Applications*, lecture 4 (Basic
  algorithms), Section 1: the Hermite normal form `H` of a basis `B` with `L(H) = L(B)`, here
  recorded together with the unimodular transformation realising it.
-/

public section

namespace Matrix

section Pad

variable {ι α : Type*} {k n : ℕ}

section Zero

variable [Zero α]

/-- The matrix `[H | 0]`: a matrix `H` with `k` columns, padded on the right with zero columns to
a matrix with `n` columns. Column `j` of `hermitePad H n` is column `j` of `H` for `j < k` and
zero for `k ≤ j`. -/
def hermitePad (H : Matrix ι (Fin k) α) (n : ℕ) : Matrix ι (Fin n) α :=
  of fun i j ↦ if h : (j : ℕ) < k then H i ⟨j, h⟩ else 0

/-- The entries of `[H | 0]`: column `j` is column `j` of `H` when `j < k`, and zero otherwise. -/
theorem hermitePad_apply (H : Matrix ι (Fin k) α) (n : ℕ) (i : ι) (j : Fin n) :
    hermitePad H n i j = if h : (j : ℕ) < k then H i ⟨j, h⟩ else 0 :=
  (rfl)

/-- The first `k` columns of `[H | 0]` are the columns of `H`. -/
@[simp]
theorem hermitePad_apply_castLE (H : Matrix ι (Fin k) α) (hk : k ≤ n) (i : ι) (j : Fin k) :
    hermitePad H n i (Fin.castLE hk j) = H i j := by
  simp [hermitePad_apply]

/-- The columns of `[H | 0]` beyond the first `k` vanish. -/
theorem hermitePad_apply_of_le (H : Matrix ι (Fin k) α) (i : ι) {j : Fin n} (hj : k ≤ j) :
    hermitePad H n i j = 0 := by
  simp [hermitePad_apply, not_lt.mpr hj]

/-- Padding a matrix with `k` columns to `k` columns does nothing. -/
@[simp]
theorem hermitePad_self (H : Matrix ι (Fin k) α) : hermitePad H k = H := by
  ext i j
  simp [hermitePad_apply]

/-- Deleting the zero columns of `[H | 0]` recovers `H`. -/
@[simp]
theorem submatrix_hermitePad (H : Matrix ι (Fin k) α) (hk : k ≤ n) :
    (hermitePad H n).submatrix id (Fin.castLE hk) = H := by
  ext i j
  simp

/-- Applying a zero-preserving map entrywise commutes with padding by zero columns. -/
theorem hermitePad_map {β : Type*} [Zero β] (H : Matrix ι (Fin k) α) (n : ℕ) {f : α → β}
    (hf : f 0 = 0) : (hermitePad H n).map f = hermitePad (H.map f) n := by
  ext i j
  by_cases h : (j : ℕ) < k <;> simp [hermitePad_apply, h, hf]

end Zero

/-- Multiplying `[H | 0]` by a vector multiplies `H` by its first `k` coordinates. -/
theorem hermitePad_mulVec [NonUnitalNonAssocSemiring α] (H : Matrix ι (Fin k) α) (hk : k ≤ n)
    (v : Fin n → α) : hermitePad H n *ᵥ v = H *ᵥ (v ∘ Fin.castLE hk) := by
  ext i
  refine (Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _
    (fun j hj ↦ ?_) fun j ↦ ?_).symm
  · simp [hermitePad_apply_of_le _ _ (not_lt.mp fun h ↦ hj ⟨⟨j, h⟩, rfl⟩)]
  · simp

variable [CommSemiring α]

/-- Padding with zero columns does not change the column lattice: for `k ≤ n` the range of
`[H | 0]` acting on `α ^ n` is the range of `H` acting on `α ^ k`. -/
theorem range_mulVecLin_hermitePad (H : Matrix ι (Fin k) α) (hk : k ≤ n) :
    LinearMap.range (hermitePad H n).mulVecLin = LinearMap.range H.mulVecLin := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, rfl⟩
    exact ⟨v ∘ Fin.castLE hk, by rw [mulVecLin_apply, mulVecLin_apply, hermitePad_mulVec H hk]⟩
  · rintro x ⟨w, rfl⟩
    refine ⟨fun j ↦ if h : (j : ℕ) < k then w ⟨j, h⟩ else 0, ?_⟩
    rw [mulVecLin_apply, mulVecLin_apply, hermitePad_mulVec H hk]
    congr 1
    ext j
    simp

/-- Padding with zero columns does not change the rank. -/
theorem rank_hermitePad (H : Matrix ι (Fin k) α) (hk : k ≤ n) :
    (hermitePad H n).rank = H.rank := by
  rw [rank, rank, range_mulVecLin_hermitePad H hk]

end Pad

variable {m n k : ℕ}

/-- A *Hermite decomposition* of the integer matrix `A`: `k ≤ n`, the `m × k` matrix `H` is in
Hermite normal form, `U'` is a two-sided inverse of `U`, and `A * U = [H | 0]`, so that the first
`k` columns of `A * U` are those of `H` and the remaining ones vanish. -/
structure IsHermiteDecomposition (A : Matrix (Fin m) (Fin n) ℤ) (H : Matrix (Fin m) (Fin k) ℤ)
    (U U' : Matrix (Fin n) (Fin n) ℤ) : Prop where
  /-- The Hermite matrix has at most as many columns as `A`. -/
  le : k ≤ n
  /-- The Hermite matrix is in Hermite normal form. -/
  isHermiteNormalForm : H.IsHermiteNormalForm
  /-- `U'` is a right inverse of `U`. -/
  mul_inv : U * U' = 1
  /-- `U'` is a left inverse of `U`. -/
  inv_mul : U' * U = 1
  /-- The transformation `U` brings `A` to the form `[H | 0]`. -/
  mul_eq_hermitePad : A * U = hermitePad H n

namespace IsHermiteDecomposition

variable {A : Matrix (Fin m) (Fin n) ℤ} {H : Matrix (Fin m) (Fin k) ℤ}
  {U U' : Matrix (Fin n) (Fin n) ℤ}

/-- Reconstruction: a matrix is recovered from a Hermite decomposition as `A = [H | 0] * U'`. -/
theorem eq_hermitePad_mul (h : IsHermiteDecomposition A H U U') : A = hermitePad H n * U' := by
  rw [← h.mul_eq_hermitePad, Matrix.mul_assoc, h.mul_inv, Matrix.mul_one]

/-- The transformation matrix of a Hermite decomposition is unimodular. -/
theorem isUnit_det (h : IsHermiteDecomposition A H U U') : IsUnit U.det :=
  isUnit_det_of_right_inverse h.mul_inv

/-- The transformation matrix of a Hermite decomposition has determinant `1` or `-1`. -/
theorem det_eq_one_or_neg_one (h : IsHermiteDecomposition A H U U') :
    U.det = 1 ∨ U.det = -1 :=
  Int.isUnit_iff.mp h.isUnit_det

/-- The column lattice of `A` is the column lattice of its Hermite matrix `H`. -/
theorem range_mulVecLin_eq (h : IsHermiteDecomposition A H U U') :
    LinearMap.range A.mulVecLin = LinearMap.range H.mulVecLin := by
  have hU : LinearMap.range U.mulVecLin = ⊤ := LinearMap.range_eq_top.mpr fun v ↦
    ⟨U' *ᵥ v, by rw [mulVecLin_apply, mulVec_mulVec, h.mul_inv, one_mulVec]⟩
  rw [← range_mulVecLin_hermitePad H h.le, ← h.mul_eq_hermitePad, mulVecLin_mul,
    LinearMap.range_comp_of_range_eq_top _ hU]

/-- The number `k` of columns of the Hermite matrix is the rank of `A` over any domain of
characteristic zero, such as `ℚ`. -/
theorem rank_map_eq {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (h : IsHermiteDecomposition A H U U') : (A.map (Int.cast : ℤ → R)).rank = k := by
  have hU : IsUnit (U.map (Int.cast : ℤ → R)).det :=
    Int.cast_det (R := R) U ▸ h.isUnit_det.map (Int.castRingHom R)
  have hmul : A.map (Int.cast : ℤ → R) * U.map Int.cast = (hermitePad H n).map Int.cast := by
    rw [← h.mul_eq_hermitePad]
    exact (Matrix.map_mul (f := Int.castRingHom R)).symm
  have hcol : (H.map (Int.cast : ℤ → R)).col = fun j ↦ algebraMap ℤ R ∘ H.col j := by
    ext j i
    simp
  rw [← rank_mul_eq_left_of_isUnit_det _ _ hU, hmul, hermitePad_map _ _ Int.cast_zero,
    rank_hermitePad _ h.le, rank_eq_finrank_span_cols, hcol,
    finrank_span_eq_card (linearIndependent_algebraMap_comp_iff.mpr
      h.isHermiteNormalForm.linearIndependent_cols), Fintype.card_fin]

/-- The number `k` of columns of the Hermite matrix is the rank of `A`. -/
theorem rank_eq (h : IsHermiteDecomposition A H U U') : A.rank = k := by
  have hA : A.map (Int.cast : ℤ → ℤ) = A := by
    ext
    exact Int.cast_id
  rw [← hA]
  exact h.rank_map_eq

/-- The Hermite matrix of a Hermite decomposition has at most as many columns as rows. -/
theorem le_height (h : IsHermiteDecomposition A H U U') : k ≤ m :=
  h.rank_eq ▸ A.rank_le_height

end IsHermiteDecomposition

/-! ### Examples -/

/-- The identity matrix has the identity as its Hermite matrix, with `k = n`. -/
example :
    IsHermiteDecomposition (1 : Matrix (Fin n) (Fin n) ℤ) (1 : Matrix (Fin n) (Fin n) ℤ) 1 1 :=
  ⟨le_rfl, IsHermiteNormalForm.one, Matrix.mul_one 1, Matrix.mul_one 1, by simp⟩

/-- The zero matrix has the empty Hermite matrix, with `k = 0`. -/
example : IsHermiteDecomposition (0 : Matrix (Fin m) (Fin n) ℤ) (0 : Matrix (Fin m) (Fin 0) ℤ)
    1 1 :=
  ⟨Nat.zero_le _, isHermiteNormalForm_of_fin_zero _, Matrix.mul_one 1, Matrix.mul_one 1, by
    ext i j
    simp [hermitePad_apply]⟩

/-- `diag(2, 1)` has Hermite matrix `diag(2, 1)`: unlike its rational column space, which is all
of `ℚ²`, the column lattice of `diag(2, 1)` remembers the `2`. -/
example : IsHermiteDecomposition !![(2 : ℤ), 0; 0, 1] !![2, 0; 0, 1] 1 1 :=
  ⟨le_rfl, IsHermitePivotedBy.isHermiteNormalForm (p := id)
    ⟨strictMono_id, by decide, by decide, by decide, by decide⟩, Matrix.mul_one 1,
    Matrix.mul_one 1, by simp⟩

/-- Every Hermite decomposition of the `2 × 2` identity matrix has `k = 2`. -/
example {H : Matrix (Fin 2) (Fin k) ℤ} {U U' : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsHermiteDecomposition 1 H U U') : k = 2 := by
  simpa using h.rank_eq.symm

/-- Every Hermite decomposition of the zero `2 × 3` matrix has `k = 0`. -/
example {H : Matrix (Fin 2) (Fin k) ℤ} {U U' : Matrix (Fin 3) (Fin 3) ℤ}
    (h : IsHermiteDecomposition 0 H U U') : k = 0 := by
  simpa using h.rank_eq.symm

/-- Every Hermite decomposition of the `2 × 2` identity matrix with `k = 2` has `H = 1`. -/
example {H U U' : Matrix (Fin 2) (Fin 2) ℤ} (h : IsHermiteDecomposition 1 H U U') : H = 1 := by
  have hH := h.isHermiteNormalForm
  have hdet : H.det = 1 := by
    have hHU : H = U := by simpa using h.mul_eq_hermitePad.symm
    subst hHU
    have := hH.det_pos
    rcases h.det_eq_one_or_neg_one with h1 | h1 <;> omega
  rw [hH.det_eq_prod_diag, Fin.prod_univ_two] at hdet
  have h0 := Int.eq_one_of_mul_eq_one_right (hH.diag_pos 0).le hdet
  have h1 := Int.eq_one_of_mul_eq_one_left (hH.diag_pos 1).le hdet
  have h01 : H 0 1 = 0 := by
    have hnonneg := hH.isHermitePivotedBy_id.nonneg_of_lt (j := 0) (j' := 1) (by decide)
    have hlt := hH.isHermitePivotedBy_id.lt_pivot_of_lt (j := 0) (j' := 1) (by decide)
    simp only [id_eq] at hnonneg hlt
    omega
  have h10 : H 1 0 = 0 := hH.isUpperTriangular (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h01, h10]

/-- Every Hermite decomposition of `diag(2, 1)` has `k = 2`. -/
example {H : Matrix (Fin 2) (Fin k) ℤ} {U U' : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsHermiteDecomposition !![(2 : ℤ), 0; 0, 1] H U U') : k = 2 := by
  rw [← h.rank_eq, rank_of_det_ne_zero (by simp), Fintype.card_fin]

/-- Every Hermite decomposition of `diag(2, 1)` has first pivot `2`, although over `ℚ` the
column space of `diag(2, 1)` is everything. -/
example {H U U' : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsHermiteDecomposition !![(2 : ℤ), 0; 0, 1] H U U') : H 0 0 = 2 := by
  have hH := h.isHermiteNormalForm
  -- The first column of `H` lies in the lattice of `diag(2, 1)`, so `2 ∣ H 0 0`.
  obtain ⟨v, hv⟩ : H *ᵥ Pi.single 0 1 ∈ LinearMap.range (!![(2 : ℤ), 0; 0, 1]).mulVecLin :=
    h.range_mulVecLin_eq ▸ ⟨_, rfl⟩
  -- The vector `(2, 0)` lies in the lattice of the upper triangular `H`, so `H 0 0 ∣ 2`.
  obtain ⟨w, hw⟩ : !![(2 : ℤ), 0; 0, 1] *ᵥ Pi.single 0 1 ∈ LinearMap.range H.mulVecLin :=
    h.range_mulVecLin_eq.symm ▸ ⟨_, rfl⟩
  have h10 : H 1 0 = 0 := hH.isUpperTriangular (by decide)
  have hv0 : 2 * v 0 = H 0 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
  have hw0 : H 0 0 * w 0 + H 0 1 * w 1 = 2 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 0
  have hw1 : w 1 = 0 := by
    have : H 1 1 * w 1 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_two, h10] using congrFun hw 1
    exact (mul_eq_zero.mp this).resolve_left (hH.diag_pos 1).ne'
  rw [hw1, mul_zero, add_zero] at hw0
  exact Int.dvd_antisymm (hH.diag_pos 0).le zero_le_two ⟨w 0, hw0.symm⟩ ⟨v 0, hv0.symm⟩

end Matrix
