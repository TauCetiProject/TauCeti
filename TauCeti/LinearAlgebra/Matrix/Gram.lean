/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.IsSymm` and `Matrix.IsLowerTriangular` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring

/-!
# Gram forms, matrix reflection, Gram determinants and Gram entry monomials

This file records the basic symmetry and quadratic-form preservation identities for the bilinear
and quadratic forms attached to a symmetric matrix, the basic facts about the Gram determinant
`det (A * Aᵀ)` of the rows of a matrix `A`, and the multinomial expansion of entry monomials of
`A * Aᵀ` into monomials in the entries of `A`.

## Main results

* `TauCeti.vecMul_dotProduct_comm`: the bilinear form `(v, w) ↦ (v ᵥ* M) ⬝ᵥ w` of a symmetric matrix
  `M` is symmetric.
* `TauCeti.reflect_vecMul_dotProduct_self`: reflection in a vector of norm two preserves the value
  `(v ᵥ* M) ⬝ᵥ v` of the form at every vector.
* `Matrix.det_mul_transpose_mul_left`: the Gram determinant of `B * A` is `det B ^ 2` times that
  of `A`.
* `Matrix.det_mul_transpose_ne_zero_iff`: over a linearly ordered commutative ring, the Gram
  determinant `det (A * Aᵀ)` is nonzero exactly when the rows of `A` are linearly independent.
* `Matrix.prod_pow_mul_transpose_apply`: every monomial in the entries of `A * Aᵀ` expands as a
  multinomial sum of monomials in the entries of `A`.
* `Matrix.IsLowerTriangular.mul_transpose_apply_eq_sum_Iic` and
  `Matrix.IsLowerTriangular.prod_pow_mul_transpose_apply`: for a lower-triangular matrix `A`, the
  Gram entries and Gram entry monomials sum only over columns at most `min i j`.
-/

public section

namespace TauCeti

open _root_.Matrix

variable {n : Type*} [Fintype n]

/-- The bilinear form carried by a symmetric matrix is symmetric. -/
theorem vecMul_dotProduct_comm {R : Type*} [NonUnitalCommSemiring R] {M : Matrix n n R}
    (hM : M.IsSymm) (v w : n → R) :
    (v ᵥ* M) ⬝ᵥ w = (w ᵥ* M) ⬝ᵥ v := by
  rw [← dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hM.eq]

variable {R : Type*} [CommRing R] {M : Matrix n n R}

/-- **Reflection in a vector of norm two preserves the value of the quadratic form.** For a
symmetric matrix `M` and a vector `u` with `(u ᵥ* M) ⬝ᵥ u = 2`, reflection in `u` preserves the
value `(v ᵥ* M) ⬝ᵥ v` of the form at every vector `v`. This is what makes a family of norm-two
vectors stable under its own reflections once the family exhausts the norm-two vectors. -/
theorem reflect_vecMul_dotProduct_self (hM : M.IsSymm) {u : n → R} (hu : (u ᵥ* M) ⬝ᵥ u = 2)
    (v : n → R) :
    ((v - ((v ᵥ* M) ⬝ᵥ u) • u) ᵥ* M) ⬝ᵥ (v - ((v ᵥ* M) ⬝ᵥ u) • u) = (v ᵥ* M) ⬝ᵥ v := by
  simp only [sub_vecMul, smul_vecMul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hu, vecMul_dotProduct_comm hM u v]
  ring

end TauCeti

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- The Gram determinant of the rows of `B * A` is `det B ^ 2` times that of `A`. -/
theorem det_mul_transpose_mul_left [CommRing R] (B : Matrix m m R) (A : Matrix m n R) :
    (B * A * (B * A)ᵀ).det = B.det ^ 2 * (A * Aᵀ).det := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A, det_mul, det_mul, det_transpose]
  ring

/-- Over a linearly ordered commutative ring, the Gram determinant `det (A * Aᵀ)` of the rows of
`A` is nonzero exactly when the rows are linearly independent. -/
theorem det_mul_transpose_ne_zero_iff [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {A : Matrix m n R} : (A * Aᵀ).det ≠ 0 ↔ LinearIndependent R A.row := by
  have key (v : m → R) : v ᵥ* (A * Aᵀ) = 0 ↔ v ᵥ* A = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [← vecMul_vecMul, h, zero_vecMul]⟩
    have := congr($h ⬝ᵥ v)
    rw [← vecMul_vecMul, ← dotProduct_mulVec, mulVec_transpose] at this
    simpa using this
  rw [← vecMul_injective_iff, Ne, ← exists_vecMul_eq_zero_iff, ← coe_vecMulLinear,
    injective_iff_map_eq_zero]
  simp only [key, vecMulLinear_apply]
  grind

section Monomial

omit [DecidableEq m] in
private theorem prod_pow_mul_eq_prod_pow_add [CommSemiring R] (A : Matrix m n R)
    (K : m × m → n → ℕ) :
    (∏ ij : m × m, ∏ k : n, (A ij.1 k * A ij.2 k) ^ K ij k) =
      ∏ q : m × n, A q.1 q.2 ^ ∑ j : m, (K (q.1, j) q.2 + K (j, q.1) q.2) := by
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  have hleft :
      (∏ ij : m × m, ∏ k : n, A ij.1 k ^ K ij k) =
        ∏ q : m × n, A q.1 q.2 ^ ∑ j : m, K (q.1, j) q.2 := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun k _ ↦
      Finset.prod_pow_eq_pow_sum Finset.univ (fun j ↦ K (i, j) k) (A i k)
  have hright :
      (∏ ij : m × m, ∏ k : n, A ij.2 k ^ K ij k) =
        ∏ q : m × n, A q.1 q.2 ^ ∑ j : m, K (j, q.1) q.2 := by
    rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun k _ ↦
      Finset.prod_pow_eq_pow_sum Finset.univ (fun j ↦ K (j, i) k) (A i k)
  rw [hleft, hright, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  rw [← pow_add, Finset.sum_add_distrib]

private theorem prod_pow_sum_mul_eq_sum_piFinset [CommSemiring R] [DecidableEq n]
    (A : Matrix m n R) (s : m × m → Finset n) (d : m × m → ℕ)
    (hs : ∀ ij : m × m, (A * Aᵀ) ij.1 ij.2 = ∑ k ∈ s ij, A ij.1 k * A ij.2 k) :
    (∏ ij, (A * Aᵀ) ij.1 ij.2 ^ d ij) =
      ∑ K ∈ Fintype.piFinset (fun ij : m × m ↦ Finset.piAntidiag (s ij) (d ij)),
        (∏ ij, (Nat.multinomial Finset.univ (K ij) : R)) *
          ∏ q : m × n, A q.1 q.2 ^ ∑ j, (K (q.1, j) q.2 + K (j, q.1) q.2) := by
  simp_rw [hs, Finset.sum_pow_eq_sum_piAntidiag]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun K hK ↦ ?_
  have hsup (ij : m × m) {k : n} (hk : K ij k ≠ 0) : k ∈ s ij :=
    (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hK ij)).2 k hk
  have hmult (ij : m × m) :
      Nat.multinomial (s ij) (K ij) = Nat.multinomial Finset.univ (K ij) :=
    Nat.multinomial_congr_of_sdiff (Finset.subset_univ _)
      (fun k hk ↦ by_contra fun hne ↦ (Finset.mem_sdiff.mp hk).2 (hsup ij hne))
      (fun _ _ ↦ rfl)
  have hprod (ij : m × m) :
      (∏ k ∈ s ij, (A ij.1 k * A ij.2 k) ^ K ij k) =
        ∏ k : n, (A ij.1 k * A ij.2 k) ^ K ij k :=
    Finset.prod_subset (Finset.subset_univ _) fun k _ hk ↦ by
      rw [not_imp_comm.mp (hsup ij) hk, pow_zero]
  simp_rw [hmult, hprod]
  rw [Finset.prod_mul_distrib, prod_pow_mul_eq_prod_pow_add]

/-- Every natural monomial in the entries of a Gram matrix `A * Aᵀ` expands as a multinomial sum
of monomials in the entries of `A`. Each summand chooses a column-split exponent vector `K ij` of
sum `d ij` for every entry pair `ij`, and `A i k` collects its occurrences as both left and right
factor in column `k`. -/
theorem prod_pow_mul_transpose_apply [CommSemiring R] [DecidableEq n]
    (A : Matrix m n R) (d : m × m → ℕ) :
    (∏ ij, (A * Aᵀ) ij.1 ij.2 ^ d ij) =
      ∑ K ∈ Fintype.piFinset (fun ij : m × m ↦ Finset.piAntidiag Finset.univ (d ij)),
        (∏ ij, (Nat.multinomial Finset.univ (K ij) : R)) *
          ∏ q : m × n, A q.1 q.2 ^ ∑ j, (K (q.1, j) q.2 + K (j, q.1) q.2) :=
  prod_pow_sum_mul_eq_sum_piFinset A (fun _ ↦ Finset.univ) d fun ij ↦ by
    simp [Matrix.mul_apply]

omit [DecidableEq m] [Fintype n] in
/-- For a lower-triangular matrix `A`, the `(i, j)` entry of `A * Aᵀ` sums only over columns at
most `min i j`. -/
theorem IsLowerTriangular.mul_transpose_apply_eq_sum_Iic [NonUnitalNonAssocSemiring R]
    [LinearOrder m] [LocallyFiniteOrderBot m] {A : Matrix m m R} (hA : A.IsLowerTriangular)
    (i j : m) :
    (A * Aᵀ) i j = ∑ k ∈ Finset.Iic (min i j), A i k * A j k := by
  rw [Matrix.mul_apply]
  simp only [transpose_apply]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ ?_
  rw [Finset.mem_Iic, le_min_iff, not_and_or, not_le, not_le] at hk
  rcases hk with hik | hjk
  · rw [hA hik, zero_mul]
  · rw [hA hjk, mul_zero]

omit [Fintype n] in
/-- For a lower-triangular matrix `A`, every natural monomial in the entries of `A * Aᵀ` expands
over column-split exponent vectors supported on `Finset.Iic (min ij.1 ij.2)`. Consequently every
surviving factor power in `A` is supported on or below the diagonal. -/
theorem IsLowerTriangular.prod_pow_mul_transpose_apply [CommSemiring R]
    [LinearOrder m] [LocallyFiniteOrderBot m] {A : Matrix m m R} (hA : A.IsLowerTriangular)
    (d : m × m → ℕ) :
    (∏ ij, (A * Aᵀ) ij.1 ij.2 ^ d ij) =
      ∑ K ∈ Fintype.piFinset
          (fun ij : m × m ↦ Finset.piAntidiag (Finset.Iic (min ij.1 ij.2)) (d ij)),
        (∏ ij, (Nat.multinomial Finset.univ (K ij) : R)) *
          ∏ q : m × m, A q.1 q.2 ^ ∑ j, (K (q.1, j) q.2 + K (j, q.1) q.2) :=
  prod_pow_sum_mul_eq_sum_piFinset A (fun ij ↦ Finset.Iic (min ij.1 ij.2)) d fun ij ↦
    hA.mul_transpose_apply_eq_sum_Iic ij.1 ij.2

end Monomial

end Matrix
