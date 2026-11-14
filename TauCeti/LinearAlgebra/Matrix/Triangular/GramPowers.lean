/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Defs
import TauCeti.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Mixed monomial expansions for Gram matrices

Every natural monomial `∏ q, (L * Lᵀ) q.1 q.2 ^ n q` in the entries of a Gram matrix `L * Lᵀ`
over a commutative semiring expands as a finite multinomial sum of monomials in the entries of
the factor `L`. Choosing for each matrix position `q = (i, j)` a composition `c q` of `n q` over
columns `k` collects on `L r k` the total exponent

`gramFactorMultiIndex c (r, k) = ∑ j, (c (r, j) k + c (j, r) k)`.

When `L` is square and lower triangular over a finite linearly ordered index type with locally
finite initial intervals, the `(i, j)` entry of `L * Lᵀ` sums only over columns
`k ∈ Finset.Iic (min i j)`. Restricting each composition `c q` to `Finset.Iic (min q.1 q.2)`
ensures that every induced factor multi-index `gramFactorMultiIndex c` is supported on the lower
triangle `{rk | rk.2 ≤ rk.1}`. We also record the diagonal-scaling law for entry monomials of
`s i * M i j * s j`.

## Main definitions and results

* `TauCeti.gramFactorMultiIndex`: the factor multi-index induced by column compositions of Gram
  entries, together with its additivity, row-degree conservation, total-degree, and
  lower-triangular support lemmas;
* `Matrix.prod_pow_mul_transpose_eq_sum`: mixed monomial expansion of `(L * Lᵀ)` for a general
  rectangular matrix `L`;
* `Matrix.IsLowerTriangular.mul_transpose_apply_eq_sum_Iic_min`: each entry `(L * Lᵀ) i j` of a
  lower-triangular Gram matrix sums up to `min i j`;
* `Matrix.IsLowerTriangular.prod_pow_mul_transpose_eq_sum`: mixed monomial expansion of `(L * Lᵀ)`
  for a lower-triangular matrix `L`, indexed by compositions supported on
  `Finset.Iic (min q.1 q.2)`;
* `Matrix.prod_pow_mul_apply_mul`: diagonal scaling `s i * M i j * s j` multiplies an entry
  monomial by `∏ i, s i ^ ∑ j, (n (i, j) + n (j, i))`.
-/

public section

open scoped BigOperators Matrix

namespace TauCeti

/-- The factor-entry exponent induced by a family `c` of column compositions of Gram entries.
When `(L * Lᵀ) i j ^ n (i, j)` chooses exponent `c (i, j) k` on the `k`-th column product
`L i k * L j k`, the entry `L r k` receives exponent `c (r, j) k` from row `r` and `c (j, r) k`
from column `r`. -/
def gramFactorMultiIndex {ι κ : Type*} [Fintype ι]
    (c : ι × ι → κ → ℕ) (rk : ι × κ) : ℕ :=
  ∑ j : ι, (c (rk.1, j) rk.2 + c (j, rk.1) rk.2)

/-- The defining sum for `gramFactorMultiIndex`. -/
theorem gramFactorMultiIndex_apply {ι κ : Type*} [Fintype ι]
    (c : ι × ι → κ → ℕ) (rk : ι × κ) :
    gramFactorMultiIndex c rk = ∑ j : ι, (c (rk.1, j) rk.2 + c (j, rk.1) rk.2) :=
  (rfl)

/-- The zero composition family induces the zero factor multi-index. -/
@[simp]
theorem gramFactorMultiIndex_zero {ι κ : Type*} [Fintype ι] :
    gramFactorMultiIndex (0 : ι × ι → κ → ℕ) = 0 := by
  ext rk
  simp [gramFactorMultiIndex_apply]

/-- `gramFactorMultiIndex` is additive in the composition family. -/
@[simp]
theorem gramFactorMultiIndex_add {ι κ : Type*} [Fintype ι]
    (c d : ι × ι → κ → ℕ) :
    gramFactorMultiIndex (c + d) = gramFactorMultiIndex c + gramFactorMultiIndex d := by
  ext rk
  simp only [gramFactorMultiIndex_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  omega

/-- `gramFactorMultiIndex` commutes with finite sums of composition families. -/
@[simp]
theorem gramFactorMultiIndex_sum {s ι κ : Type*} [Fintype ι]
    (t : Finset s) (c : s → ι × ι → κ → ℕ) :
    gramFactorMultiIndex (∑ x ∈ t, c x) = ∑ x ∈ t, gramFactorMultiIndex (c x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert x t hxt ih => simp [hxt, ih]

/-- Transposing the Gram-entry index pair leaves `gramFactorMultiIndex` unchanged. -/
@[simp]
theorem gramFactorMultiIndex_comp_swap {ι κ : Type*} [Fintype ι]
    (c : ι × ι → κ → ℕ) :
    gramFactorMultiIndex (fun q ↦ c q.swap) = gramFactorMultiIndex c := by
  ext rk
  simp only [gramFactorMultiIndex_apply, Prod.swap_prod_mk]
  exact Finset.sum_congr rfl fun _ _ ↦ add_comm _ _

/-- Summing `gramFactorMultiIndex c (i, k)` across columns `k` recovers the row-and-column
total of `c` at `i`. -/
theorem sum_snd_gramFactorMultiIndex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι × ι → κ → ℕ) (i : ι) :
    ∑ k : κ, gramFactorMultiIndex c (i, k) =
      ∑ j : ι, ((∑ k : κ, c (i, j) k) + ∑ k : κ, c (j, i) k) := by
  simp_rw [gramFactorMultiIndex_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_add_distrib

/-- For compositions `c q ∈ Finset.piAntidiag (s q) (n q)`, the row sum of `gramFactorMultiIndex c`
at `i` equals the symmetric vertex degree `∑ j, (n (i, j) + n (j, i))`. -/
theorem sum_snd_gramFactorMultiIndex_of_mem_piFinset {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {s : ι × ι → Finset κ} {n : ι × ι → ℕ}
    {c : ι × ι → κ → ℕ}
    (hc : c ∈ Fintype.piFinset fun q ↦ Finset.piAntidiag (s q) (n q)) (i : ι) :
    ∑ k : κ, gramFactorMultiIndex c (i, k) = ∑ j : ι, (n (i, j) + n (j, i)) := by
  have hsum (q : ι × ι) : ∑ k : κ, c q k = n q := by
    have hcq := Fintype.mem_piFinset.mp hc q
    rw [← Finset.sum_subset (Finset.subset_univ (s q))
      fun k _ hk ↦ Finset.eq_zero_of_notMem_of_mem_piAntidiag hk hcq]
    exact (Finset.mem_piAntidiag.mp hcq).1
  rw [sum_snd_gramFactorMultiIndex]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hsum (i, j), hsum (j, i)]

/-- The total degree of `gramFactorMultiIndex c` is twice the sum of all entries of `c`. -/
theorem sum_gramFactorMultiIndex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι × ι → κ → ℕ) :
    ∑ rk : ι × κ, gramFactorMultiIndex c rk = 2 * ∑ q : ι × ι, ∑ k : κ, c q k := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_snd_gramFactorMultiIndex, Finset.sum_add_distrib]
  have hswap : (∑ x : ι, ∑ j : ι, ∑ k : κ, c (j, x) k) =
      ∑ x : ι, ∑ j : ι, ∑ k : κ, c (x, j) k := Finset.sum_comm
  rw [hswap, ← two_mul, Fintype.sum_prod_type]

/-- For compositions `c q ∈ Finset.piAntidiag (s q) (n q)`, the total degree of
`gramFactorMultiIndex c` is twice the total degree of `n`. -/
theorem sum_gramFactorMultiIndex_of_mem_piFinset {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {s : ι × ι → Finset κ} {n : ι × ι → ℕ}
    {c : ι × ι → κ → ℕ}
    (hc : c ∈ Fintype.piFinset fun q ↦ Finset.piAntidiag (s q) (n q)) :
    ∑ rk : ι × κ, gramFactorMultiIndex c rk = 2 * ∑ q : ι × ι, n q := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_snd_gramFactorMultiIndex_of_mem_piFinset hc, Finset.sum_add_distrib]
  have hswap : (∑ x : ι, ∑ j : ι, n (j, x)) = ∑ x : ι, ∑ j : ι, n (x, j) := Finset.sum_comm
  rw [hswap, ← two_mul, Fintype.sum_prod_type]

/-- When every composition `c q` is supported on `Finset.Iic (min q.1 q.2)`, the induced factor
multi-index `gramFactorMultiIndex c` is supported on the lower triangle `{rk | rk.2 ≤ rk.1}`. -/
theorem le_of_gramFactorMultiIndex_ne_zero {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] {n : ι × ι → ℕ} {c : ι × ι → ι → ℕ}
    (hc : c ∈ Fintype.piFinset
      fun q : ι × ι ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q))
    {rk : ι × ι} (hrk : gramFactorMultiIndex c rk ≠ 0) :
    rk.2 ≤ rk.1 := by
  by_contra hlt
  rw [not_le] at hlt
  apply hrk
  rw [gramFactorMultiIndex_apply]
  apply Finset.sum_eq_zero
  intro j _
  have h1 : rk.2 ∉ Finset.Iic (min rk.1 j) := by
    simp [not_le.mpr ((min_le_left rk.1 j).trans_lt hlt)]
  have h2 : rk.2 ∉ Finset.Iic (min j rk.1) := by
    simp [not_le.mpr ((min_le_right j rk.1).trans_lt hlt)]
  rw [Finset.eq_zero_of_notMem_of_mem_piAntidiag h1 (Fintype.mem_piFinset.mp hc (rk.1, j)),
    Finset.eq_zero_of_notMem_of_mem_piAntidiag h2 (Fintype.mem_piFinset.mp hc (j, rk.1)),
    add_zero]

end TauCeti

namespace Matrix

/-- Collecting column-product powers `(L q.1 k ^ c q k * L q.2 k ^ c q k)` across all pairs `q`
and columns `k` yields the factor monomial with exponent `TauCeti.gramFactorMultiIndex c`. -/
theorem prod_prod_pow_mul_pow_eq_prod_pow_gramFactorMultiIndex
    {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    (L : Matrix ι κ R) (c : ι × ι → κ → ℕ) :
    (∏ q : ι × ι, ∏ k : κ, (L q.1 k ^ c q k * L q.2 k ^ c q k)) =
      ∏ rk : ι × κ, L rk.1 rk.2 ^ TauCeti.gramFactorMultiIndex c rk := by
  simp_rw [Finset.prod_mul_distrib]
  have hleft : (∏ q : ι × ι, ∏ k : κ, L q.1 k ^ c q k) =
      ∏ rk : ι × κ, L rk.1 rk.2 ^ ∑ j : ι, c (rk.1, j) rk.2 := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun k _ ↦ by simp [Finset.prod_pow_eq_pow_sum]
  have hright : (∏ q : ι × ι, ∏ k : κ, L q.2 k ^ c q k) =
      ∏ rk : ι × κ, L rk.1 rk.2 ^ ∑ j : ι, c (j, rk.1) rk.2 := by
    rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun k _ ↦ by simp [Finset.prod_pow_eq_pow_sum]
  rw [hleft, hright, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun rk _ ↦ ?_
  rw [← pow_add, ← Finset.sum_add_distrib, ← TauCeti.gramFactorMultiIndex_apply]

/-- Every mixed natural monomial in the entries of `L * Lᵀ` expands as a multinomial sum of
monomials in the entries of `L`. -/
theorem prod_pow_mul_transpose_eq_sum {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [CommSemiring R]
    (L : Matrix ι κ R) (n : ι × ι → ℕ) :
    (∏ q : ι × ι, (L * Lᵀ) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset (fun q : ι × ι ↦ Finset.piAntidiag Finset.univ (n q)),
        (∏ q : ι × ι, (Nat.multinomial Finset.univ (c q) : R)) *
          ∏ rk : ι × κ, L rk.1 rk.2 ^ TauCeti.gramFactorMultiIndex c rk := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_pow_eq_sum_piAntidiag]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [mul_pow]
  exact prod_prod_pow_mul_pow_eq_prod_pow_gramFactorMultiIndex L c

/-- Each entry `(L * Lᵀ) i j` of a lower-triangular Gram matrix sums only over columns up to
`min i j`, since columns strictly above `i` or `j` vanish in `L`. -/
theorem IsLowerTriangular.mul_transpose_apply_eq_sum_Iic_min
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [NonUnitalNonAssocSemiring R] {L : Matrix ι ι R} (hL : L.IsLowerTriangular) (i j : ι) :
    (L * Lᵀ) i j = ∑ k ∈ Finset.Iic (min i j), L i k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ ?_
  simp only [Finset.mem_Iic, le_min_iff, not_and_or, not_le] at hk
  rcases hk with hik | hjk
  · rw [hL hik, zero_mul]
  · rw [hL hjk, mul_zero]

/-- For a lower-triangular matrix `L`, every mixed natural monomial in the entries of `L * Lᵀ`
expands as a multinomial sum over column compositions supported on `Finset.Iic (min q.1 q.2)`,
so each resulting factor multi-index is supported on the lower triangle. -/
theorem IsLowerTriangular.prod_pow_mul_transpose_eq_sum
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] [CommSemiring R]
    {L : Matrix ι ι R} (hL : L.IsLowerTriangular) (n : ι × ι → ℕ) :
    (∏ q : ι × ι, (L * Lᵀ) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset
          (fun q : ι × ι ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q : ι × ι, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : R)) *
          ∏ rk : ι × ι, L rk.1 rk.2 ^ TauCeti.gramFactorMultiIndex c rk := by
  simp_rw [hL.mul_transpose_apply_eq_sum_Iic_min, Finset.sum_pow_eq_sum_piAntidiag]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  have hext (q : ι × ι) :
      (∏ k ∈ Finset.Iic (min q.1 q.2), (L q.1 k * L q.2 k) ^ c q k) =
        ∏ k : ι, (L q.1 k ^ c q k * L q.2 k ^ c q k) := by
    simp_rw [← mul_pow]
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk ↦ ?_
    rw [Finset.eq_zero_of_notMem_of_mem_piAntidiag hk (Fintype.mem_piFinset.mp hc q), pow_zero]
  simp_rw [hext]
  exact prod_prod_pow_mul_pow_eq_prod_pow_gramFactorMultiIndex L c

/-- Scaling rows and columns of `M` by `s` multiplies an entry monomial `∏ q, M q.1 q.2 ^ n q` by
`∏ i, s i ^ ∑ j, (n (i, j) + n (j, i))`. -/
theorem prod_pow_mul_apply_mul {ι R : Type*} [Fintype ι] [CommSemiring R]
    (M : Matrix ι ι R) (s : ι → R) (n : ι × ι → ℕ) :
    (∏ q : ι × ι, (s q.1 * M q.1 q.2 * s q.2) ^ n q) =
      (∏ i : ι, s i ^ ∑ j : ι, (n (i, j) + n (j, i))) *
        ∏ q : ι × ι, M q.1 q.2 ^ n q := by
  have hterm (q : ι × ι) :
      (s q.1 * M q.1 q.2 * s q.2) ^ n q =
        (s q.1 ^ n q * s q.2 ^ n q) * M q.1 q.2 ^ n q := by
    rw [mul_right_comm, mul_pow, mul_pow]
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  have hleft : (∏ q : ι × ι, s q.1 ^ n q) = ∏ i : ι, s i ^ ∑ j : ι, n (i, j) := by
    rw [Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [Finset.prod_pow_eq_pow_sum]
  have hright : (∏ q : ι × ι, s q.2 ^ n q) = ∏ i : ι, s i ^ ∑ j : ι, n (j, i) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [Finset.prod_pow_eq_pow_sum]
  rw [hleft, hright, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← pow_add, ← Finset.sum_add_distrib]

end Matrix
