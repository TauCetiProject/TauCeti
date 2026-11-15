/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.IsSymm` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Order.Interval.Finset.Defs
import TauCeti.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Ring

/-!
# Gram forms, matrix reflection, Gram determinants, and Gram monomials

This file records the basic symmetry and quadratic-form preservation identities for the bilinear
and quadratic forms attached to a symmetric matrix, the basic facts about the Gram determinant
`det (A * Aᵀ)` of the rows of a matrix `A`, and the multinomial expansion of entrywise monomials
`∏ q, (A * Aᵀ) q.1 q.2 ^ d q` in terms of monomials in the entries of `A`.

## Main definitions

* `TauCeti.gramMonomialExponent`: the exponent of `A p.1 p.2` collected from a family of column
  compositions `c : m × m → n → ℕ` when expanding a monomial in the entries of `A * Aᵀ`.

## Main results

* `TauCeti.vecMul_dotProduct_comm`: the bilinear form `(v, w) ↦ (v ᵥ* M) ⬝ᵥ w` of a symmetric matrix
  `M` is symmetric.
* `TauCeti.reflect_vecMul_dotProduct_self`: reflection in a vector of norm two preserves the value
  `(v ᵥ* M) ⬝ᵥ v` of the form at every vector.
* `Matrix.det_mul_transpose_mul_left`: the Gram determinant of `B * A` is `det B ^ 2` times that
  of `A`.
* `Matrix.det_mul_transpose_ne_zero_iff`: over a linearly ordered commutative ring, the Gram
  determinant `det (A * Aᵀ)` is nonzero exactly when the rows of `A` are linearly independent.
* `Matrix.prod_mul_pow_eq_prod_pow_gramMonomialExponent`,
  `Matrix.prod_pow_mul_transpose_apply_of_support`, and `Matrix.prod_pow_mul_transpose_apply`:
  regrouping column-pair products by `TauCeti.gramMonomialExponent` and expanding an entrywise
  monomial in `A * Aᵀ` into monomials in `A`.
* `Matrix.IsLowerTriangular.mul_transpose_apply_eq_sum_Iic` and
  `Matrix.IsLowerTriangular.prod_pow_mul_transpose_apply`: for a lower-triangular matrix `A`, each
  entry `(A * Aᵀ) i j` sums over `Finset.Iic (min i j)` and every resulting factor monomial is
  supported on or below the diagonal (`TauCeti.le_of_gramMonomialExponent_ne_zero`).
-/

public section

open scoped BigOperators

namespace TauCeti

open _root_.Matrix

section BilinearForm

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

end BilinearForm

section GramMonomialExponent

variable {m k : Type*} [Fintype m]

/-- The combined exponent of `A p.1 p.2` arising from a family of column compositions
`c : m × m → k → ℕ` in the multinomial expansion of a monomial in the entries of `A * Aᵀ`. Each
summand `A i r * A j r` contributes `c (i, j) r` to the left factor `A i r` and `c (i, j) r` to the
right factor `A j r`. -/
def gramMonomialExponent (c : m × m → k → ℕ) (p : m × k) : ℕ :=
  (∑ j, c (p.1, j) p.2) + ∑ i, c (i, p.1) p.2

/-- The defining formula for `TauCeti.gramMonomialExponent`. -/
theorem gramMonomialExponent_def (c : m × m → k → ℕ) (p : m × k) :
    gramMonomialExponent c p = (∑ j, c (p.1, j) p.2) + ∑ i, c (i, p.1) p.2 :=
  (rfl)

/-- The defining formula for `TauCeti.gramMonomialExponent` on an explicit pair `(i, r)`. -/
theorem gramMonomialExponent_mk (c : m × m → k → ℕ) (i : m) (r : k) :
    gramMonomialExponent c (i, r) = (∑ j, c (i, j) r) + ∑ j, c (j, i) r :=
  (rfl)

/-- The zero composition family yields zero factor exponents. -/
@[simp]
theorem gramMonomialExponent_zero :
    gramMonomialExponent (0 : m × m → k → ℕ) = 0 := by
  ext p
  simp [gramMonomialExponent_def]

/-- Factor exponents in a Gram monomial expansion are additive in the composition family. -/
@[simp]
theorem gramMonomialExponent_add (c₁ c₂ : m × m → k → ℕ) :
    gramMonomialExponent (c₁ + c₂) =
      gramMonomialExponent c₁ + gramMonomialExponent c₂ := by
  ext p
  simp only [gramMonomialExponent_def, Pi.add_apply, Finset.sum_add_distrib]
  omega

/-- Factor exponents in a Gram monomial expansion commute with natural scalar multiplication. -/
theorem gramMonomialExponent_nsmul (n : ℕ) (c : m × m → k → ℕ) :
    gramMonomialExponent (n • c) = n • gramMonomialExponent c := by
  ext p
  simp [gramMonomialExponent_def, Finset.mul_sum, mul_add]

/-- Factor exponents in a Gram monomial expansion commute with multiplication by a cast natural
number (the `simp` normal form of `n • c`). -/
@[simp]
theorem gramMonomialExponent_natCast_mul (n : ℕ) (c : m × m → k → ℕ) :
    gramMonomialExponent ((n : m × m → k → ℕ) * c) =
      (n : m × k → ℕ) * gramMonomialExponent c := by
  simpa only [nsmul_eq_mul] using gramMonomialExponent_nsmul n c

/-- Factor exponents commute with finite sums of composition families. -/
@[simp]
theorem gramMonomialExponent_sum {ι : Type*} (s : Finset ι) (c : ι → m × m → k → ℕ) :
    gramMonomialExponent (∑ x ∈ s, c x) = ∑ x ∈ s, gramMonomialExponent (c x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih => simp [hxs, ih]

/-- Pointwise evaluation of `TauCeti.gramMonomialExponent` on a finite sum of composition
families. -/
theorem gramMonomialExponent_sum_apply {ι : Type*} (s : Finset ι) (c : ι → m × m → k → ℕ)
    (p : m × k) :
    gramMonomialExponent (∑ x ∈ s, c x) p = ∑ x ∈ s, gramMonomialExponent (c x) p := by
  rw [gramMonomialExponent_sum, Finset.sum_apply]

/-- The factor exponents contributed by a composition supported at a single matrix position `q`. -/
@[simp]
theorem gramMonomialExponent_single [DecidableEq m] (q : m × m) (f : k → ℕ) (p : m × k) :
    gramMonomialExponent (Pi.single q f) p =
      (if p.1 = q.1 then f p.2 else 0) + (if p.1 = q.2 then f p.2 else 0) := by
  simp [gramMonomialExponent_def, Pi.single_apply, ite_apply, Prod.ext_iff, ite_and]

/-- Swapping the two row indices of a composition family preserves the resulting factor
exponents. -/
@[simp]
theorem gramMonomialExponent_swap (c : m × m → k → ℕ) :
    gramMonomialExponent (fun q ↦ c q.swap) = gramMonomialExponent c := by
  ext p
  simp only [gramMonomialExponent_def, Prod.swap_prod_mk]
  exact Nat.add_comm _ _

/-- The factor exponent `gramMonomialExponent c p` vanishes if and only if every composition entry
in column `p.2` involving row `p.1` vanishes. -/
@[simp]
theorem gramMonomialExponent_apply_eq_zero_iff (c : m × m → k → ℕ) (p : m × k) :
    gramMonomialExponent c p = 0 ↔ (∀ j, c (p.1, j) p.2 = 0) ∧ ∀ i, c (i, p.1) p.2 = 0 := by
  simp [gramMonomialExponent_def]

/-- The factor exponent family `gramMonomialExponent c` vanishes if and only if `c = 0`. -/
@[simp]
theorem gramMonomialExponent_eq_zero_iff (c : m × m → k → ℕ) :
    gramMonomialExponent c = 0 ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext q r
  exact ((gramMonomialExponent_apply_eq_zero_iff c (q.1, r)).1 (congrFun h (q.1, r))).1 q.2

/-- Summing `gramMonomialExponent c` over all factor entries yields twice the total weight of `c`,
reflecting that every entry of `A * Aᵀ` is quadratic in `A`. -/
theorem sum_gramMonomialExponent [Fintype k] (c : m × m → k → ℕ) :
    (∑ p : m × k, gramMonomialExponent c p) = 2 * ∑ q : m × m, ∑ r : k, c q r := by
  simp only [gramMonomialExponent_def, Finset.sum_add_distrib, two_mul]
  have h1 : (∑ x : m × k, ∑ j : m, c (x.1, j) x.2) = ∑ q : m × m, ∑ r : k, c q r := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    exact Finset.sum_comm
  have h2 : (∑ x : m × k, ∑ i : m, c (i, x.1) x.2) = ∑ q : m × m, ∑ r : k, c q r := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    dsimp only
    refine (Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm).trans Finset.sum_comm
  rw [h1, h2]

/-- When each composition `c q` is supported on `Finset.Iic (min q.1 q.2)`, every nonzero exponent
in `gramMonomialExponent c` lies on or below the diagonal. -/
theorem le_of_gramMonomialExponent_ne_zero [LinearOrder m] [LocallyFiniteOrderBot m]
    {d : m × m → ℕ} {c : m × m → m → ℕ}
    (hc : c ∈ Fintype.piFinset fun q : m × m ↦ (Finset.Iic (min q.1 q.2)).piAntidiag (d q))
    {p : m × m} (hp : gramMonomialExponent c p ≠ 0) : p.2 ≤ p.1 := by
  rw [gramMonomialExponent_def, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hp
  rcases hp with hp | hp
  · obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    have hmem := (Finset.mem_piAntidiag.1 (Fintype.mem_piFinset.1 hc (p.1, j))).2 p.2 hj
    exact (Finset.mem_Iic.1 hmem).trans (min_le_left _ _)
  · obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    have hmem := (Finset.mem_piAntidiag.1 (Fintype.mem_piFinset.1 hc (i, p.1))).2 p.2 hi
    exact (Finset.mem_Iic.1 hmem).trans (min_le_right _ _)

end GramMonomialExponent

end TauCeti

namespace Matrix

/-- Regrouping a product of powers of column-pair products `(A q.1 r * A q.2 r) ^ c q r` collects
the exponent `TauCeti.gramMonomialExponent c p` on each matrix entry `A p.1 p.2`. -/
theorem prod_mul_pow_eq_prod_pow_gramMonomialExponent {m k R : Type*}
    [Fintype m] [Fintype k] [CommMonoid R] (A : Matrix m k R) (c : m × m → k → ℕ) :
    (∏ q : m × m, ∏ r : k, (A q.1 r * A q.2 r) ^ c q r) =
      ∏ p : m × k, A p.1 p.2 ^ TauCeti.gramMonomialExponent c p := by
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  have hleft :
      (∏ q : m × m, ∏ r : k, A q.1 r ^ c q r) =
        ∏ p : m × k, A p.1 p.2 ^ (∑ j : m, c (p.1, j) p.2) := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    dsimp only
    exact Finset.prod_pow_eq_pow_sum _ _ _
  have hright :
      (∏ q : m × m, ∏ r : k, A q.2 r ^ c q r) =
        ∏ p : m × k, A p.1 p.2 ^ (∑ i : m, c (i, p.1) p.2) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun r _ ↦ ?_
    dsimp only
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hleft, hright, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ ↦ (pow_add (A p.1 p.2) _ _).symm

section Rectangular

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

/-- **Multinomial expansion of a Gram entry monomial with restricted column supports.** If for
every pair `q = (i, j)`, the column products `A i r * A j r` vanish outside `s q`, then
`∏ q, (A * Aᵀ) q.1 q.2 ^ d q` expands into a sum over composition families in `(s q).piAntidiag`
of multinomial weights times monomials in the entries of `A`. -/
theorem prod_pow_mul_transpose_apply_of_support [DecidableEq n] [CommSemiring R]
    (A : Matrix m n R) (d : m × m → ℕ) (s : m × m → Finset n)
    (hs : ∀ q : m × m, ∀ r ∉ s q, A q.1 r * A q.2 r = 0) :
    (∏ q : m × m, (A * Aᵀ) q.1 q.2 ^ d q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ (s q).piAntidiag (d q)),
        (∏ q, (Nat.multinomial (s q) (c q) : R)) *
          ∏ p : m × n, A p.1 p.2 ^ TauCeti.gramMonomialExponent c p := by
  have hentry (q : m × m) :
      (A * Aᵀ) q.1 q.2 ^ d q =
        ∑ f ∈ (s q).piAntidiag (d q),
          (Nat.multinomial (s q) f : R) * ∏ r : n, (A q.1 r * A q.2 r) ^ f r := by
    have hsum : (A * Aᵀ) q.1 q.2 = ∑ r ∈ s q, A q.1 r * A q.2 r := by
      rw [Matrix.mul_apply]
      simp only [transpose_apply]
      exact (Finset.sum_subset (Finset.subset_univ (s q)) fun r _ hr ↦ hs q r hr).symm
    rw [hsum, Finset.sum_pow_eq_sum_piAntidiag]
    refine Finset.sum_congr rfl fun f hf ↦ congrArg ((Nat.multinomial (s q) f : R) * ·) ?_
    refine Finset.prod_subset (Finset.subset_univ (s q)) fun r _ hr ↦ ?_
    rw [Finset.eq_zero_of_notMem_of_mem_piAntidiag hr hf, pow_zero]
  simp_rw [hentry]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.prod_mul_distrib, prod_mul_pow_eq_prod_pow_gramMonomialExponent]

/-- **Multinomial expansion of a Gram entry monomial.** Every natural monomial in the entries of
`A * Aᵀ` expands into a weighted sum of natural monomials in the entries of `A`. -/
theorem prod_pow_mul_transpose_apply [DecidableEq n] [CommSemiring R]
    (A : Matrix m n R) (d : m × m → ℕ) :
    (∏ q : m × m, (A * Aᵀ) q.1 q.2 ^ d q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.univ.piAntidiag (d q)),
        (∏ q, (Nat.multinomial Finset.univ (c q) : R)) *
          ∏ p : m × n, A p.1 p.2 ^ TauCeti.gramMonomialExponent c p :=
  A.prod_pow_mul_transpose_apply_of_support d (fun _ ↦ Finset.univ) fun _ _ hr ↦
    (hr (Finset.mem_univ _)).elim

end Rectangular

private theorem IsLowerTriangular.mul_apply_eq_zero_of_notMem_Iic {k R : Type*} [LinearOrder k]
    [LocallyFiniteOrderBot k] [MulZeroClass R] {A : Matrix k k R} (hA : A.IsLowerTriangular)
    {i j r : k} (hr : r ∉ Finset.Iic (min i j)) : A i r * A j r = 0 := by
  rw [Finset.mem_Iic, le_min_iff, not_and_or, not_le, not_le] at hr
  rcases hr with hr | hr
  · rw [hA hr, zero_mul]
  · rw [hA hr, mul_zero]

/-- For a lower-triangular matrix `A`, the `(i, j)` entry of `A * Aᵀ` sums only over columns up to
`min i j`. -/
theorem IsLowerTriangular.mul_transpose_apply_eq_sum_Iic {k R : Type*} [Fintype k] [LinearOrder k]
    [LocallyFiniteOrderBot k] [NonUnitalNonAssocSemiring R] {A : Matrix k k R}
    (hA : A.IsLowerTriangular) (i j : k) :
    (A * Aᵀ) i j = ∑ r ∈ Finset.Iic (min i j), A i r * A j r := by
  rw [Matrix.mul_apply]
  simp only [transpose_apply]
  exact (Finset.sum_subset (Finset.subset_univ _) fun _ _ ↦
    hA.mul_apply_eq_zero_of_notMem_Iic).symm

/-- **Multinomial expansion of a lower-triangular Gram monomial.** When `A` is lower triangular,
each entry `(A * Aᵀ) i j` uses only columns in `Finset.Iic (min i j)`, so every resulting monomial
in `A` is supported on or below the diagonal (`TauCeti.le_of_gramMonomialExponent_ne_zero`). -/
theorem IsLowerTriangular.prod_pow_mul_transpose_apply {k R : Type*} [Fintype k] [LinearOrder k]
    [LocallyFiniteOrderBot k] [CommSemiring R] {A : Matrix k k R}
    (hA : A.IsLowerTriangular) (d : k × k → ℕ) :
    (∏ q : k × k, (A * Aᵀ) q.1 q.2 ^ d q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ (Finset.Iic (min q.1 q.2)).piAntidiag (d q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : R)) *
          ∏ p : k × k, A p.1 p.2 ^ TauCeti.gramMonomialExponent c p :=
  A.prod_pow_mul_transpose_apply_of_support d (fun q ↦ Finset.Iic (min q.1 q.2)) fun _ _ ↦
    hA.mul_apply_eq_zero_of_notMem_Iic

end Matrix
