/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Fintype.Pi
import TauCeti.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Mixed monomial expansions for Gram matrices

Every natural monomial `∏ q, (L * Lᵀ) q.1 q.2 ^ n q` in the entries of a Gram matrix `L * Lᵀ`
of a rectangular matrix `L` over a commutative semiring expands as a finite multinomial sum of
monomials in the entries of the factor `L`. Choosing for each matrix position `q = (i, j)` a
composition `c q` of `n q` over columns `k` collects on `L r k` the total exponent

`gramFactorMultiIndex c (r, k) = ∑ j, (c (r, j) k + c (j, r) k)`.

For a square lower-triangular `L`, the finer expansion over column choices `k ≤ min i j` is
`Matrix.IsLowerTriangular.prod_mul_transpose_apply_pow_eq_sum`.

## Main definitions and results

* `TauCeti.gramFactorMultiIndex`: the factor multi-index induced by column compositions of Gram
  entries, together with its additivity, singleton (`Pi.single`), row-degree conservation and
  total-degree lemmas;
* `Matrix.prod_prod_pow_mul_pow_eq_prod_pow_gramFactorMultiIndex`: over a commutative monoid,
  collecting column-product powers `(L q.1 k ^ c q k * L q.2 k ^ c q k)` yields the factor
  monomial with exponent `TauCeti.gramFactorMultiIndex c`;
* `Matrix.prod_pow_mul_transpose_eq_sum`: mixed monomial expansion of `(L * Lᵀ)` for a general
  rectangular matrix `L`.
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

/-- Evaluating `gramFactorMultiIndex` on a composition family supported at a single matrix
position `q` adds the row and column contributions of `f` at `rk.2`. -/
theorem gramFactorMultiIndex_single_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι × ι) (f : κ → ℕ) (rk : ι × κ) :
    gramFactorMultiIndex (Pi.single q f) rk =
      (if rk.1 = q.1 then f rk.2 else 0) + (if rk.1 = q.2 then f rk.2 else 0) := by
  rcases q with ⟨i, j⟩
  rcases rk with ⟨r, k⟩
  rw [gramFactorMultiIndex_apply, Finset.sum_add_distrib]
  congr 1
  · by_cases h1 : r = i <;> simp [h1, Pi.single_apply, apply_ite (fun g : κ → ℕ ↦ g k)]
  · by_cases h2 : r = j <;> simp [h2, Pi.single_apply, apply_ite (fun g : κ → ℕ ↦ g k)]

/-- A single unit of column exponent `m` at Gram position `q` and column `k` induces the sum of
singleton factor exponents at `(q.1, k)` and `(q.2, k)`. -/
@[simp]
theorem gramFactorMultiIndex_single_single {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (q : ι × ι) (k : κ) (m : ℕ) :
    gramFactorMultiIndex (Pi.single q (Pi.single k m)) =
      Pi.single (q.1, k) m + Pi.single (q.2, k) m := by
  ext ⟨r, l⟩
  rw [gramFactorMultiIndex_single_apply, Pi.add_apply]
  by_cases hr1 : r = q.1 <;> by_cases hr2 : r = q.2 <;> by_cases hl : l = k <;>
    simp [hr1, hr2, hl, Pi.single_apply, Prod.ext_iff]

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
theorem sum_gramFactorMultiIndex_prodMk {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι × ι → κ → ℕ) (i : ι) :
    ∑ k : κ, gramFactorMultiIndex c (i, k) =
      ∑ j : ι, ((∑ k : κ, c (i, j) k) + ∑ k : κ, c (j, i) k) := by
  simp_rw [gramFactorMultiIndex_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_add_distrib

/-- For compositions `c q ∈ Finset.piAntidiag (s q) (n q)`, the row sum of `gramFactorMultiIndex c`
at `i` equals the symmetric vertex degree `∑ j, (n (i, j) + n (j, i))`. -/
theorem sum_gramFactorMultiIndex_prodMk_of_mem_piFinset {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {s : ι × ι → Finset κ} {n : ι × ι → ℕ}
    {c : ι × ι → κ → ℕ}
    (hc : c ∈ Fintype.piFinset fun q ↦ Finset.piAntidiag (s q) (n q)) (i : ι) :
    ∑ k : κ, gramFactorMultiIndex c (i, k) = ∑ j : ι, (n (i, j) + n (j, i)) := by
  have hsum (q : ι × ι) : ∑ k : κ, c q k = n q := by
    have hcq := Fintype.mem_piFinset.mp hc q
    rw [← Finset.sum_subset (Finset.subset_univ (s q))
      fun k _ hk ↦ Finset.eq_zero_of_notMem_of_mem_piAntidiag hk hcq]
    exact (Finset.mem_piAntidiag.mp hcq).1
  rw [sum_gramFactorMultiIndex_prodMk]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hsum (i, j), hsum (j, i)]

/-- The total degree of `gramFactorMultiIndex c` is twice the sum of all entries of `c`. -/
theorem sum_gramFactorMultiIndex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι × ι → κ → ℕ) :
    ∑ rk : ι × κ, gramFactorMultiIndex c rk = 2 * ∑ q : ι × ι, ∑ k : κ, c q k := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_gramFactorMultiIndex_prodMk, Finset.sum_add_distrib]
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
  simp_rw [sum_gramFactorMultiIndex_prodMk_of_mem_piFinset hc, Finset.sum_add_distrib]
  have hswap : (∑ x : ι, ∑ j : ι, n (j, x)) = ∑ x : ι, ∑ j : ι, n (x, j) := Finset.sum_comm
  rw [hswap, ← two_mul, Fintype.sum_prod_type]

end TauCeti

namespace Matrix

/-- Collecting column-product powers `(L q.1 k ^ c q k * L q.2 k ^ c q k)` across all pairs `q`
and columns `k` yields the factor monomial with exponent `TauCeti.gramFactorMultiIndex c`. -/
theorem prod_prod_pow_mul_pow_eq_prod_pow_gramFactorMultiIndex
    {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommMonoid R]
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

end Matrix
