/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Algebra.Ring.Idempotent.Basic

/-!
# Basic determinant formulas

Additions to Mathlib's `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`.

Mathlib computes the determinant of a matrix indexed by a singleton type (`Matrix.det_unique`)
and of a `Fin 2`-indexed matrix (`Matrix.det_fin_two`). A two-by-two matrix also arises indexed
by `m ⊕ n` with `m` and `n` singletons, for instance as `fromBlocks` of four `1 × 1` blocks or on
the `l ⊕ l` index of the standard symplectic form `Matrix.J l R`. `Matrix.det_sum_unique` gives
its determinant in coordinates, so that such a matrix need not be reindexed along `Fin 2` by hand.

If every row of a matrix `B` with `n + 2` rows and `n + 1` columns sums to `1`, then deleting the
rows of `B` one at a time gives `n + 2` square matrices, and the alternating sum of their
determinants vanishes. Indeed, it is the expansion along the first column of the square matrix
obtained from `B` by adjoining a first column of ones, and that column is the sum of the others.

A first column of ones also lets a square matrix drop one size: subtracting each row from its
successor (`Matrix.det_eq_of_forall_row_eq_smul_add_pred`) leaves a single `1` in that column, and
expanding along it (`Matrix.det_succ_column_zero`) leaves the matrix of consecutive row
differences of the remaining columns.

## Main results

* `Matrix.det_updateRow_updateRow_swap`: exchanging the vectors in two prescribed rows reverses
  the determinant.
* `Matrix.det_sum_unique`: the determinant of a matrix on `m ⊕ n`, for singletons `m` and `n`.
* `Matrix.sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero`: the alternating sum of the maximal
  minors of a matrix with `n + 2` rows and `n + 1` columns whose rows sum to `1` vanishes.
* `Matrix.det_eq_det_of_col_zero_eq_one`: a square matrix whose first column is constant `1` has
  the determinant of its consecutive row differences on the remaining columns.
* `Matrix.det_of_sum_rows`: the determinant of a matrix whose rows are sums over finite sets is the
  sum, over the choices of one summand in each row, of the determinants of the resulting matrices.
* `Matrix.det_submatrix_ne_zero_of_map`: a minor whose image under a ring homomorphism is nonzero
  is nonzero, and `Matrix.det_submatrix_map_ne_zero_iff` is the converse for an injective one.
* `Matrix.exists_isUnit_det_row_eq`: any row with a unit entry extends to a matrix with unit
  determinant.
* `Matrix.isUnit_det_mul_add_one_sub`: for an idempotent `P` commuting with an invertible `g`,
  the matrix `P * g + 1 - P` has invertible determinant.
* `Matrix.isUnit_det_map_intCast`: an integer matrix with nonzero determinant has unit
  determinant over every field of characteristic zero.
* `RingHom.det_map_ne_zero_of_isUnit_det`: the image of a matrix with unit determinant under a ring
  homomorphism to a nontrivial commutative ring has nonzero determinant.
* `Matrix.isUnit_det_one_add_smul`: a matrix congruent to `1` modulo an element of the Jacobson
  radical has unit determinant.
-/

public section

namespace Matrix

variable {m n R : Type*} [Unique m] [Unique n] [DecidableEq m] [DecidableEq n] [Fintype m]
  [Fintype n] [CommRing R]

/-- The determinant of a matrix indexed by `m ⊕ n`, for singleton types `m` and `n`, is the
two-by-two determinant of its entries. -/
theorem det_sum_unique (A : Matrix (m ⊕ n) (m ⊕ n) R) :
    A.det = A (Sum.inl default) (Sum.inl default) * A (Sum.inr default) (Sum.inr default)
      - A (Sum.inl default) (Sum.inr default) * A (Sum.inr default) (Sum.inl default) := by
  -- Reindex along `Fin 2 ≃ m ⊕ n`. It sends `0` to `Sum.inl default` and `1` to `Sum.inr default`
  -- by definition, so `det_fin_two` is the claim up to `rfl`; `simp` cannot see through the
  -- numerals `0, 1 : Fin 2` to evaluate `finSumFinEquiv.symm` on them.
  rw [← det_submatrix_equiv_self (finSumFinEquiv.symm.trans <|
    (Equiv.ofUnique (Fin 1) m).sumCongr (Equiv.ofUnique (Fin 1) n)) A, det_fin_two]
  rfl

end Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The alternating sum of the maximal minors of a matrix whose rows sum to one vanishes.** If
every row of a matrix `B` with `n + 2` rows and `n + 1` columns sums to `1`, then deleting the row
`p` of `B` for each `p` gives square matrices whose determinants have vanishing alternating sum. -/
theorem sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero
    (B : Matrix (Fin (n + 2)) (Fin (n + 1)) R) (hB : ∀ j, ∑ i, B j i = 1) :
    ∑ p : Fin (n + 2), (-1 : R) ^ (p : ℕ) * (B.submatrix p.succAbove id).det = 0 := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) R := of fun j ↦ Fin.cons 1 (B j)
  -- the first column of `A` is the sum of the others
  have hcol : A.updateCol 0 (fun k ↦ ∑ i, (Fin.cons 0 fun _ ↦ 1 : Fin (n + 2) → R) i • A k i) =
      A := by
    refine (congrArg (A.updateCol 0) (funext fun k ↦ ?_)).trans (updateCol_eq_self A 0)
    simp [A, Fin.sum_univ_succ, hB]
  have hsub (p : Fin (n + 2)) : A.submatrix p.succAbove Fin.succ = B.submatrix p.succAbove id := by
    ext j i
    simp [A]
  have hA := det_updateCol_sum A 0 (Fin.cons 0 fun _ ↦ 1)
  rw [hcol, Fin.cons_zero, zero_smul, det_succ_column_zero] at hA
  simpa [A, hsub] using hA

/-- **Expanding along a constant column `1`.** If the first column of a square matrix `N` is
constant equal to `1`, then `det N` is the determinant of the matrix of consecutive row
differences `N (i + 1) (j + 1) - N i (j + 1)` of the remaining columns.

Subtracting each row from its successor leaves `1` as the only nonzero entry of the first column,
in the first row, and the minor of that entry is the matrix of differences. -/
theorem det_eq_det_of_col_zero_eq_one (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hN : ∀ i, N i 0 = 1) :
    N.det = (of fun i j : Fin n => N i.succ j.succ - N i.castSucc j.succ).det := by
  rw [det_eq_of_forall_row_eq_smul_add_pred (A := N)
    (B := of (Fin.cons (N 0) fun i => N i.succ - N i.castSucc)) (fun _ => 1) (fun _ => rfl)
    (fun _ _ => by simp), det_succ_column_zero, Fin.sum_univ_succ]
  simp [hN, submatrix]

end Matrix

namespace Matrix

/-- Interchanging the rows occupied by two prescribed vectors reverses the determinant. -/
theorem det_updateRow_updateRow_swap {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) (j k : ι)
    (a b : ι → R) (h : j ≠ k) :
    ((A.updateRow j a).updateRow k b).det =
      -((A.updateRow k a).updateRow j b).det := by
  let M := (A.updateRow k a).updateRow j b
  have hkj : k ≠ j := Ne.symm h
  have he :
      M.submatrix (Equiv.swap j k) id =
        (A.updateRow j a).updateRow k b := by
    ext r l
    by_cases hrj : r = j
    · subst r
      simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, h, hkj]
    · by_cases hrk : r = k
      · subst r
        simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply]
      · simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, hrj, hrk,
          Equiv.swap_apply_of_ne_of_ne hrj hrk]
  rw [← he, Matrix.det_permute]
  simp [M, Equiv.Perm.sign_swap h]

/-- **A nonzero minor lifts along a ring homomorphism.** If the minor of `A.map f` on rows `r` and
columns `c` is nonzero, so is the minor of `A` on the same rows and columns. No injectivity of `f`
is needed: the image of the minor of `A` is the minor of `A.map f` (`RingHom.map_det_submatrix`). -/
theorem det_submatrix_ne_zero_of_map {m n R S l : Type*} [Fintype l] [DecidableEq l] [CommRing R]
    [CommRing S] (f : R →+* S) {A : Matrix m n R} {r : l → m} {c : l → n}
    (h : ((A.map f).submatrix r c).det ≠ 0) : (A.submatrix r c).det ≠ 0 := by
  rw [← f.map_det_submatrix] at h
  exact ne_of_apply_ne f (by rwa [map_zero])

/-- Along an injective ring homomorphism `f`, a minor of `A.map f` is nonzero exactly when the
minor of `A` on the same rows and columns is nonzero. -/
theorem det_submatrix_map_ne_zero_iff {m n R S l : Type*} [Fintype l] [DecidableEq l] [CommRing R]
    [CommRing S] {f : R →+* S} (hf : Function.Injective f) {A : Matrix m n R} {r : l → m}
    {c : l → n} : ((A.map f).submatrix r c).det ≠ 0 ↔ (A.submatrix r c).det ≠ 0 := by
  rw [← f.map_det_submatrix, map_ne_zero_iff f hf]

/-- An integer matrix with nonzero determinant has unit determinant over every field of
characteristic zero. -/
theorem isUnit_det_map_intCast {n K : Type*} [Fintype n] [DecidableEq n] [Field K] [CharZero K]
    {A : Matrix n n ℤ} (hA : A.det ≠ 0) : IsUnit (A.map ((↑) : ℤ → K)).det := by
  rw [← Int.cast_det]
  exact (Int.cast_ne_zero.2 hA).isUnit

/-- **Multilinearity of the determinant in all rows at once.** The determinant of a matrix whose
`i`-th row is a sum over a finite set `A i` is the sum, over the choices of one summand in each
row, of the determinants of the resulting matrices. -/
theorem det_of_sum_rows {ι R : Type*} {κ : ι → Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : ∀ i, Finset (κ i)) (g : ∀ i, κ i → ι → R) :
    (Matrix.of fun i j => ∑ t ∈ A i, g i t j).det
      = ∑ y ∈ Fintype.piFinset A, (Matrix.of fun i j => g i (y i) j).det := by
  have key := (detRowAlternating (R := R) (n := ι)).toMultilinearMap.map_sum_finset
    (A := A) (g := g)
  have hrow : (fun i => ∑ t ∈ A i, g i t) = fun i j => ∑ t ∈ A i, g i t j := by
    funext i j
    exact Finset.sum_apply j _ _
  rw [hrow] at key
  exact key

/-- **Completing a row with a unit entry to a matrix with unit determinant.** If `f j₀` is a unit
in `R`, then `f` is row `i₀` of a square matrix over `R` with unit determinant. -/
theorem exists_isUnit_det_row_eq {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (i₀ : ι) {f : ι → R} {j₀ : ι} (hj₀ : IsUnit (f j₀)) :
    ∃ A : Matrix ι ι R, IsUnit A.det ∧ A i₀ = f := by
  let M : Matrix ι ι R := (1 : Matrix ι ι R).updateRow j₀ f
  have hsum : (∑ k, f k • (1 : Matrix ι ι R) k) = f := by ext m; simp [Matrix.one_apply]
  have hMdet : M.det = f j₀ := by
    simpa [M, hsum] using det_updateRow_sum (1 : Matrix ι ι R) j₀ f
  refine ⟨M.submatrix (Equiv.swap i₀ j₀) id, ?_, by ext m; simp [M]⟩
  rw [det_permute, hMdet]
  exact ((Int.castRingHom R).isUnit_map (Units.isUnit _)).mul hj₀

/-- For an idempotent matrix `P` commuting with an invertible matrix `g`, the matrix
`P * g + 1 - P`, which acts as `g` on the range of `P` and as the identity on that of `1 - P`, has
invertible determinant. -/
theorem isUnit_det_mul_add_one_sub {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {P g : Matrix n n R} (hP : IsIdempotentElem P) (hg : IsUnit g) (hPg : Commute P g) :
    IsUnit (P * g + 1 - P).det :=
  (isUnit_iff_isUnit_det _).1 (hP.isUnit_mul_add_one_sub hg hPg)

/-- A matrix congruent to `1` modulo an element of the Jacobson radical is invertible. -/
theorem isUnit_det_one_add_smul {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] {r : R}
    (hr : r ∈ Ring.jacobson R) (D : Matrix n n R) : IsUnit (1 + r • D).det := by
  refine Ideal.isUnit_of_sub_one_mem_jacobson _ ?_
  rw [det_one_add_smul, add_assoc, add_sub_cancel_left]
  exact (Ring.jacobson R).add_mem (Ideal.mul_mem_left _ _ hr)
    (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hr 2 two_pos))

end Matrix

namespace RingHom

/-- The image of a matrix with unit determinant under a ring homomorphism to a nontrivial
commutative ring has nonzero determinant. -/
theorem det_map_ne_zero_of_isUnit_det {ι R K : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [CommRing K] [Nontrivial K] (f : R →+* K) {A : Matrix ι ι R} (hdet : IsUnit A.det) :
    (A.map f).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hdet.map _).ne_zero

end RingHom
