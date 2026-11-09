/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Matrix-vector multiplication

Multiplying a vector by a matrix twice is multiplying it by the square of the matrix, so a
square-zero matrix annihilates every vector in two steps. This is the form in which the nilpotence
of a root operator reaches the vector it acts on.

Over an ordered semiring, multiplication by an entrywise nonnegative matrix is monotone and
preserves nonnegativity, and an entrywise strictly positive matrix sends a nonzero nonnegative
vector to a strictly positive one.

When row `i` of a matrix vanishes off the diagonal, coordinate `i` of a product with a vector only
sees coordinate `i` of that vector. In particular such a matrix maps the coordinate hyperplane
`{v | v i = 0}` into itself.

Subtracting a matrix from a constant diagonal matrix turns its eigenvector equation into a
homogeneous linear system, with no multiplicative identity needed. An eigenvector of a matrix is an
eigenvector of each of its powers.

The `σ`-sesquilinear form `(σ ∘ x) ⬝ᵥ (Q *ᵥ y)` of a matrix `Q` scales by `σ c * c` along a
line.

## Main results

* `TauCeti.mulVec_mulVec_eq_zero_of_pow_two_eq_zero`: a square-zero matrix annihilates every
  vector in two multiplications.
* `Matrix.mulVec_apply_eq_mul_of_forall_ne_eq_zero`: if row `i` of `A` vanishes off the diagonal,
  then `(A *ᵥ v) i = A i i * v i`.
* `Matrix.diagonal_const_sub_mulVec_eq_zero_iff`: `(a - A) v = 0` for a constant diagonal `a`
  is the eigenvector equation `A v = a • v`.
* `Matrix.pow_mulVec_eq_pow_smul`: if `A v = μ • v`, then `A ^ k v = μ ^ k • v`.
* `Matrix.mulVec_mono` and `Matrix.mulVec_nonneg`: multiplication by an entrywise nonnegative
  matrix is monotone and preserves nonnegativity.
* `Matrix.mulVec_pos`: a strictly positive matrix sends a nonzero nonnegative vector to a strictly
  positive one.
* `Matrix.submatrix_id_castSucc_mulVec_eq_of_mulVec_eq_zero`: a right null vector with unit last
  coordinate lets the submatrix omitting the last column reproduce `A *ᵥ x`.
* `Matrix.comp_smul_dotProduct_mulVec_smul`: `h(c v, c v) = σ c * c * h(v, v)`.
-/

public section

open scoped Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square-zero matrix annihilates every vector in two multiplications. -/
theorem mulVec_mulVec_eq_zero_of_pow_two_eq_zero {R : Type*} [Semiring R] {M : Matrix n n R}
    (hM : M ^ 2 = 0) (v : n → R) : M *ᵥ M *ᵥ v = 0 := by
  rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]

end TauCeti

namespace Matrix

variable {m n : Type*} [Fintype n]

section NonUnitalNonAssocSemiring

variable {R : Type*} [NonUnitalNonAssocSemiring R]

/-- If row `i` of `A` vanishes off the diagonal, then coordinate `i` of `A *ᵥ v` is
`A i i * v i`. -/
theorem mulVec_apply_eq_mul_of_forall_ne_eq_zero {A : Matrix n n R} {i : n}
    (h : ∀ j ≠ i, A i j = 0) (v : n → R) : (A *ᵥ v) i = A i i * v i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj ↦ by rw [h j hj, zero_mul]) (by simp)

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- The homogeneous system `(a - A) v = 0` for a constant diagonal `a` is the eigenvector
equation `A v = a • v`. Unlike `Matrix.diagonal_const_mulVec`, no multiplicative identity is
needed. -/
theorem diagonal_const_sub_mulVec_eq_zero_iff [DecidableEq n] (A : Matrix n n R) (a : R)
    (v : n → R) : (diagonal (fun _ => a) - A) *ᵥ v = 0 ↔ A *ᵥ v = a • v := by
  have h : (diagonal fun _ => a) *ᵥ v = a • v := by
    ext
    simp [mulVec_diagonal]
  rw [sub_mulVec, h, sub_eq_zero, eq_comm]

end NonUnitalNonAssocRing

section CommSemiring

variable {R : Type*} [CommSemiring R] [DecidableEq n]

/-- An eigenvector of a square matrix is an eigenvector of each of its powers, for the
corresponding power of the eigenvalue. -/
theorem pow_mulVec_eq_pow_smul {A : Matrix n n R} {v : n → R} {μ : R} (h : A *ᵥ v = μ • v)
    (k : ℕ) : (A ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, ← pow_succ']

end CommSemiring

/-- Along a line the `σ`-sesquilinear form `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` scales by `σ c * c`:
`h(c v, c v) = σ c * c * h(v, v)`. -/
theorem comp_smul_dotProduct_mulVec_smul {R : Type*} [CommSemiring R] (Q : Matrix n n R)
    (σ : R →+* R) (c : R) (v : n → R) :
    (σ ∘ (c • v)) ⬝ᵥ (Q *ᵥ (c • v)) = σ c * c * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) := by
  rw [TauCeti.map_comp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, mul_assoc]

section OrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] {A : Matrix m n R}
  {x y : n → R}

/-- Multiplication by an entrywise nonnegative matrix is monotone. -/
theorem mulVec_mono (hA : ∀ i j, 0 ≤ A i j) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := fun i =>
  dotProduct_le_dotProduct_of_nonneg_left hxy (hA i)

/-- An entrywise nonnegative matrix sends nonnegative vectors to nonnegative vectors. -/
theorem mulVec_nonneg (hA : ∀ i j, 0 ≤ A i j) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := fun i =>
  dotProduct_nonneg_of_nonneg (hA i) hx

end OrderedSemiring

section StrictOrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {A : Matrix m n R}
  {y : n → R}

/-- A strictly positive matrix sends a nonzero nonnegative vector to a vector all of whose entries
are strictly positive. -/
theorem mulVec_pos (hA : ∀ i j, 0 < A i j) (hy : 0 ≤ y) (hy0 : y ≠ 0) (i : m) :
    0 < (A *ᵥ y) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA i k).le (hy k))
    ⟨j, Finset.mem_univ j, mul_pos (hA i j) ((hy j).lt_of_ne' hj)⟩

end StrictOrderedSemiring

section Ring

variable {n : ℕ} {R : Type*} [Ring R]

/-- If `A *ᵥ u = 0` and `u (Fin.last n)` is a unit, then the submatrix of `A` omitting its last
column sends `fun i => x i.castSucc - u i.castSucc * (u (last))⁻¹ * x (last)` to `A *ᵥ x`. -/
theorem submatrix_id_castSucc_mulVec_eq_of_mulVec_eq_zero {m : Type*}
    (A : Matrix m (Fin (n + 1)) R) {u : Fin (n + 1) → R} (hu : A *ᵥ u = 0)
    (huunit : IsUnit (u (Fin.last n))) (x : Fin (n + 1) → R) :
    (A.submatrix id Fin.castSucc) *ᵥ (fun i => x i.castSucc -
      u i.castSucc * ((huunit.unit⁻¹ : Rˣ) : R) * x (Fin.last n)) = A *ᵥ x := by
  have hcol (i : m) : A i (Fin.last n) =
      -(∑ j : Fin n, A i j.castSucc * u j.castSucc) * ((huunit.unit⁻¹ : Rˣ) : R) := by
    have h := congrFun hu i
    simp only [mulVec, dotProduct, Pi.zero_apply, Fin.sum_univ_castSucc] at h
    calc A i (Fin.last n) = A i (Fin.last n) * u (Fin.last n) * ((huunit.unit⁻¹ : Rˣ) : R) := by
          rw [mul_assoc, huunit.mul_val_inv, mul_one]
      _ = _ := by rw [eq_neg_of_add_eq_zero_right h]
  ext i
  simp only [mulVec, dotProduct, submatrix_apply, id_eq, Fin.sum_univ_castSucc, hcol, mul_sub,
    Finset.sum_sub_distrib, neg_mul, ← sub_eq_add_neg]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by simp only [mul_assoc]

end Ring

end Matrix
