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

/-!
# Matrix-vector multiplication

Multiplying a vector by a matrix twice is multiplying it by the square of the matrix, so a
square-zero matrix annihilates every vector in two steps. This is the form in which the nilpotence
of a root operator reaches the vector it acts on.

Over an ordered semiring, multiplication by an entrywise nonnegative matrix is monotone and
preserves nonnegativity, a dot product with a vector of entries at least `1` bounds each
coordinate of a nonnegative vector, and a matrix whose row `i` is strictly positive sends a nonzero
nonnegative vector to one whose coordinate `i` is strictly positive.

When row `i` of a matrix vanishes off the diagonal, coordinate `i` of a product with a vector only
sees coordinate `i` of that vector. In particular such a matrix maps the coordinate hyperplane
`{v | v i = 0}` into itself.

Subtracting a matrix from a constant diagonal matrix turns its eigenvector equation into a
homogeneous linear system, with no multiplicative identity needed. An eigenvector of a matrix is an
eigenvector of each of its powers, with the eigenvalue in any monoid of scalars whose action
commutes with multiplication of the entries.

For a matrix `Q` and a multiplicative map `σ`, the pairing `(σ ∘ x) ⬝ᵥ (Q *ᵥ y)` scales by
`σ c * c` along a line. When `σ` is also additive, such as a ring endomorphism, this pairing is
the `σ`-sesquilinear form of `Q`.

Casting the entries of an integer matrix and of an integer vector into a ring commutes with both
matrix-vector and vector-matrix multiplication.

A matrix invariant under row and column reindexing sends vectors invariant under the column
permutation to vectors invariant under the row map.

A right null vector whose last coordinate is a unit lets the submatrix omitting the last column
reproduce every product `A *ᵥ x`.

## Main results

* `Matrix.mulVec_mulVec_eq_zero_of_sq_eq_zero`: a square-zero matrix annihilates every
  vector in two multiplications.
* `Matrix.mulVec_apply_eq_mul_of_forall_ne_eq_zero`: if row `i` of `A` vanishes off the diagonal,
  then `(A *ᵥ v) i = A i i * v i`.
* `Matrix.mulVec_comp_of_submatrix_eq`: multiplying an `e₂`-invariant vector by an
  `(e₁, e₂)`-invariant matrix yields an `e₁`-invariant vector.
* `Matrix.diagonal_const_sub_mulVec_eq_zero_iff`: `(a - A) v = 0` for a constant diagonal `a`
  is the eigenvector equation `A v = a • v`.
* `Matrix.pow_mulVec_eq_pow_smul`: if `A v = μ • v`, then `A ^ k v = μ ^ k • v`.
* `Matrix.mulVec_mono` and `Matrix.mulVec_nonneg`: multiplication by an entrywise nonnegative
  matrix is monotone and preserves nonnegativity.
* `Matrix.le_dotProduct_of_one_le`: a coordinate of a nonnegative vector is at most its dot
  product with a vector whose entries are at least `1`.
* `Matrix.mulVec_pos`: if row `i` of `A` is strictly positive, then `A` sends a nonzero
  nonnegative vector to one whose coordinate `i` is strictly positive.
* `Matrix.submatrix_id_castSucc_mulVec_eq_of_mulVec_eq_zero`: a right null vector with unit last
  coordinate lets the submatrix omitting the last column reproduce `A *ᵥ x`.
* `Matrix.comp_smul_dotProduct_mulVec_smul`: `h(c v, c v) = σ c * c * h(v, v)`.
* `Matrix.vecMul_ne_zero_of_isUnit`: for a unit matrix `Q` over a semiring and `w ≠ 0`,
  `w ᵥ* Q ≠ 0`.
* `Matrix.exists_eq_smul_of_vecMulVec_eq`: equality of `vecMulVec u₁ w₁` and `vecMulVec u₂ w₂`
  with `u₂, w₂ ≠ 0` implies `u₁ = c • u₂` for some `c ≠ 0`.
* `Matrix.map_intCast_mulVec` and `Matrix.map_intCast_vecMul`: casting integer entries commutes
  with matrix-vector and vector-matrix multiplication.
-/

public section

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype n]

/-- A square-zero matrix annihilates every vector in two multiplications. -/
theorem mulVec_mulVec_eq_zero_of_sq_eq_zero [DecidableEq n] {R : Type*} [Semiring R]
    {M : Matrix n n R} (hM : M ^ 2 = 0) (v : n → R) : M *ᵥ M *ᵥ v = 0 := by
  rw [mulVec_mulVec, ← sq, hM, zero_mulVec]

section NonUnitalNonAssocSemiring

variable {R : Type*} [NonUnitalNonAssocSemiring R]

/-- If row `i` of `A` vanishes off the diagonal, then coordinate `i` of `A *ᵥ v` is
`A i i * v i`. -/
theorem mulVec_apply_eq_mul_of_forall_ne_eq_zero {A : Matrix n n R} {i : n}
    (h : ∀ j ≠ i, A i j = 0) (v : n → R) : (A *ᵥ v) i = A i i * v i := by
  simp only [mulVec, dotProduct]
  exact Fintype.sum_eq_single i fun j hj ↦ by rw [h j hj, zero_mul]

/-- Multiplying an `e₂`-invariant vector by an `(e₁, e₂)`-invariant matrix yields an `e₁`-invariant
vector. -/
theorem mulVec_comp_of_submatrix_eq {M : Matrix m n R} {e₁ : m → m} {e₂ : n ≃ n}
    (hM : M.submatrix e₁ e₂ = M) {v : n → R} (hv : v ∘ e₂ = v) :
    (M *ᵥ v) ∘ e₁ = M *ᵥ v := by
  conv_rhs => rw [← hM, ← hv]
  rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]

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

/-- An eigenvector of a square matrix is an eigenvector of each of its powers, for the
corresponding power of the eigenvalue. The eigenvalue may lie in any monoid `S` whose action
commutes with multiplication in `R`, so `R` need not be commutative. -/
theorem pow_mulVec_eq_pow_smul [DecidableEq n] {R S : Type*} [Semiring R] [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] {A : Matrix n n R} {v : n → R} {μ : S}
    (h : A *ᵥ v = μ • v) (k : ℕ) : (A ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, ← pow_succ']

/-- For a multiplicative map `σ`, the pairing `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` scales by `σ c * c`
along a line: `h(c v, c v) = σ c * c * h(v, v)`. When `σ` is also additive, such as a ring
endomorphism, `h` is the `σ`-sesquilinear form of `Q`. The left multiplications of `R` must
commute (`SMulCommClass R R R`), but `R` need not be commutative or unital. -/
theorem comp_smul_dotProduct_mulVec_smul {R F : Type*} [NonUnitalSemiring R]
    [SMulCommClass R R R] [FunLike F R R] [MulHomClass F R R] (Q : Matrix n n R) (σ : F) (c : R)
    (v : n → R) : (σ ∘ (c • v)) ⬝ᵥ (Q *ᵥ (c • v)) = σ c * c * ((σ ∘ v) ⬝ᵥ (Q *ᵥ v)) := by
  rw [TauCeti.map_comp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, mul_assoc]

section IntCast

variable {R : Type*} [NonAssocRing R]

/-- Casting an integer matrix and an integer vector entrywise commutes with matrix-vector
multiplication. -/
theorem map_intCast_mulVec (A : Matrix m n ℤ) (v : n → ℤ) :
    A.map (Int.cast : ℤ → R) *ᵥ (fun j => (v j : R)) = fun i => ((A *ᵥ v) i : R) :=
  -- `RingHom.map_mulVec` for `Int.castRingHom R`, whose coercion is `Int.cast`.
  funext fun i => ((Int.castRingHom R).map_mulVec A v i).symm

omit [Fintype n] in
/-- Casting an integer vector and an integer matrix entrywise commutes with vector-matrix
multiplication. -/
theorem map_intCast_vecMul [Fintype m] (v : m → ℤ) (A : Matrix m n ℤ) :
    (fun i => (v i : R)) ᵥ* A.map (Int.cast : ℤ → R) = fun j => ((v ᵥ* A) j : R) :=
  -- `RingHom.map_vecMul` for `Int.castRingHom R`, whose coercion is `Int.cast`.
  funext fun j => ((Int.castRingHom R).map_vecMul A v j).symm

end IntCast

section OrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] {A : Matrix m n R}
  {x y : n → R}

/-- Multiplication by an entrywise nonnegative matrix is monotone. -/
theorem mulVec_mono (hA : ∀ i j, 0 ≤ A i j) (hxy : x ≤ y) : A *ᵥ x ≤ A *ᵥ y := fun i =>
  dotProduct_le_dotProduct_of_nonneg_left hxy (hA i)

/-- An entrywise nonnegative matrix sends nonnegative vectors to nonnegative vectors. -/
theorem mulVec_nonneg (hA : ∀ i j, 0 ≤ A i j) (hx : 0 ≤ x) : 0 ≤ A *ᵥ x := fun i =>
  dotProduct_nonneg_of_nonneg (hA i) hx

/-- A coordinate of a nonnegative vector `x` is at most its dot product with a vector `w` whose
entries are at least `1`. -/
theorem le_dotProduct_of_one_le {w : n → R} (hw : ∀ k, 1 ≤ w k) (hx : 0 ≤ x) (j : n) :
    x j ≤ w ⬝ᵥ x :=
  (le_mul_of_one_le_left (hx j) (hw j)).trans <|
    Finset.single_le_sum (f := fun k => w k * x k)
      (fun k _ => mul_nonneg (zero_le_one.trans (hw k)) (hx k)) (Finset.mem_univ j)

end OrderedSemiring

section StrictOrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {A : Matrix m n R}
  {y : n → R}

/-- If row `i` of `A` is strictly positive, then for a nonzero nonnegative vector `y` the
coordinate `i` of `A *ᵥ y` is strictly positive. -/
theorem mulVec_pos {i : m} (hA : ∀ j, 0 < A i j) (hy : 0 ≤ y) (hy0 : y ≠ 0) :
    0 < (A *ᵥ y) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA k).le (hy k))
    ⟨j, Finset.mem_univ j, mul_pos (hA j) ((hy j).lt_of_ne' hj)⟩

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

section Semiring

variable [DecidableEq n] {R : Type*} [Semiring R]

/-- If `Q` is a unit matrix over a semiring and `w ≠ 0`, then `w ᵥ* Q ≠ 0`. -/
theorem vecMul_ne_zero_of_isUnit {Q : Matrix n n R} (hQ : IsUnit Q) {w : n → R} (hw : w ≠ 0) :
    w ᵥ* Q ≠ 0 := by
  obtain ⟨U, rfl⟩ := hQ
  intro h0
  apply hw
  calc w = w ᵥ* ((U : Matrix n n R) * ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)) := by simp
    _ = (w ᵥ* (U : Matrix n n R)) ᵥ* ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) :=
      (vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [h0, zero_vecMul]

end Semiring

section Field

variable {K : Type*} [Field K]

omit [Fintype n] in
/-- If two outer products `vecMulVec u₁ w₁` and `vecMulVec u₂ w₂` over a field agree and
`u₂`, `w₂` are nonzero, then `u₁ = c • u₂` for some nonzero scalar `c`. -/
theorem exists_eq_smul_of_vecMulVec_eq {u₁ u₂ : m → K} {w₁ w₂ : n → K}
    (hu₂ : u₂ ≠ 0) (hw₂ : w₂ ≠ 0) (h : vecMulVec u₁ w₁ = vecMulVec u₂ w₂) :
    ∃ c ≠ (0 : K), u₁ = c • u₂ := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw₂
  have hcol : ∀ i, u₁ i * w₁ j = u₂ i * w₂ j := fun i ↦ congrFun (congrFun h i) j
  have hw₁j : w₁ j ≠ 0 := fun h0 ↦ hu₂ <| funext fun i ↦ by
    have hi := hcol i
    rw [h0, mul_zero] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_right hj
  refine ⟨w₂ j * (w₁ j)⁻¹, mul_ne_zero hj (inv_ne_zero hw₁j), funext fun i ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  calc u₁ i = u₁ i * w₁ j * (w₁ j)⁻¹ := (mul_inv_cancel_right₀ hw₁j _).symm
    _ = u₂ i * w₂ j * (w₁ j)⁻¹ := by rw [hcol i]
    _ = w₂ j * (w₁ j)⁻¹ * u₂ i := by rw [mul_assoc, mul_comm (u₂ i)]

end Field

end Matrix
