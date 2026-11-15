/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Entry monomials of matrix products and Gram matrices

Over a commutative semiring, a finite product of natural powers of entries of a matrix product
`A * B` expands as a finite multinomial sum of entry monomials in `A` and `B`. When `B = Aᵀ`, the
factors from `A` and `Aᵀ` combine into a single entry monomial in `A` whose exponents are given by
`TauCeti.gramMonomialExponent`. When `A` is lower triangular on a linearly ordered finite index
type, the column decompositions may be restricted to `Finset.Iic (min i j)`, and every resulting
factor monomial is supported on or below the diagonal.

This file also records the symmetry and diagonal-sign transformations of matrix entry monomials:
for a unit-diagonal symmetric matrix, an entry monomial collapses to the strict lower triangle, and
conjugation by a single-axis sign flip multiplies an entry monomial by `(-1)` raised to that axis's
total incident degree.

## Main definitions and results

* `TauCeti.gramMonomialExponent`: aggregates a columnwise decomposition `c : ι × ι → κ → ℕ` of Gram
  entry powers into the resulting entry exponents on the factor `L` in `L * Lᵀ`.
* `Matrix.prod_pow_mul_apply_of_support` and `Matrix.prod_pow_mul_apply`: multinomial expansion of
  `∏ q, (A * B) q.1 q.2 ^ n q`.
* `Matrix.prod_pow_mul_transpose_apply_of_support`, `Matrix.prod_pow_mul_transpose_apply`, and
  `Matrix.IsLowerTriangular.prod_pow_mul_transpose_apply`: multinomial expansion of Gram entry
  monomials `∏ q, (L * Lᵀ) q.1 q.2 ^ n q`.
* `Matrix.prod_pow_single_apply`: reduction of a singleton-supported entry monomial to a single
  entry power.
* `Matrix.IsSymm.prod_pow_apply_of_diag_eq_one`: reduction of an entry monomial of a unit-diagonal
  symmetric matrix to the strict lower triangle.
* `Matrix.prod_pow_signFlip_mul_apply`: transformation of an entry monomial under a single-axis
  diagonal sign flip.
-/

public section

open scoped BigOperators Matrix

namespace TauCeti

section GramMonomialExponent

variable {ι κ : Type*} [Fintype ι]

/-- Aggregates a columnwise decomposition `c : ι × ι → κ → ℕ` of Gram entry powers into the
resulting entry exponents on the factor `L` in `L * Lᵀ`. Entry `(i, k)` receives `c (i, j) k` from
the left factor of `(L * Lᵀ) i j` and `c (j, i) k` from the right factor of `(L * Lᵀ) j i`. -/
def gramMonomialExponent (c : ι × ι → κ → ℕ) : ι × κ → ℕ :=
  fun r ↦ ∑ j : ι, (c (r.1, j) r.2 + c (j, r.1) r.2)

/-- Defining formula for `TauCeti.gramMonomialExponent`. -/
theorem gramMonomialExponent_def (c : ι × ι → κ → ℕ) :
    gramMonomialExponent c = fun r ↦ ∑ j : ι, (c (r.1, j) r.2 + c (j, r.1) r.2) := (rfl)

/-- Pointwise evaluation of `TauCeti.gramMonomialExponent`. -/
@[grind =]
theorem gramMonomialExponent_apply (c : ι × ι → κ → ℕ) (r : ι × κ) :
    gramMonomialExponent c r = ∑ j : ι, (c (r.1, j) r.2 + c (j, r.1) r.2) := (rfl)

/-- The zero decomposition produces the zero factor exponent. -/
@[simp]
theorem gramMonomialExponent_zero :
    gramMonomialExponent (0 : ι × ι → κ → ℕ) = 0 := by
  ext r
  simp [gramMonomialExponent_apply]

/-- Factor exponents are additive in the columnwise decomposition. -/
@[simp]
theorem gramMonomialExponent_add (c d : ι × ι → κ → ℕ) :
    gramMonomialExponent (c + d) = gramMonomialExponent c + gramMonomialExponent d := by
  ext r
  simp only [gramMonomialExponent_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by omega

/-- Factor exponents commute with finite sums of columnwise decompositions. -/
@[simp]
theorem gramMonomialExponent_sum {α : Type*} (s : Finset α) (c : α → ι × ι → κ → ℕ) :
    gramMonomialExponent (∑ a ∈ s, c a) = ∑ a ∈ s, gramMonomialExponent (c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih => simp [has, ih]

/-- Factor exponent of a decomposition supported at a single Gram entry `q`. -/
@[simp]
theorem gramMonomialExponent_single [DecidableEq ι] (q : ι × ι) (d : κ → ℕ) (r : ι × κ) :
    gramMonomialExponent (Pi.single q d) r =
      (if r.1 = q.1 then d r.2 else 0) + (if r.1 = q.2 then d r.2 else 0) := by
  rw [gramMonomialExponent_apply, Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_eq_single q.2]
    · by_cases h : r.1 = q.1
      · rw [ite_eq_left h, h, Prod.mk.eta, Pi.single_eq_same]
      · rw [ite_eq_right h, Pi.single_eq_of_ne (fun hq ↦ h (congrArg Prod.fst hq)), Pi.zero_apply]
    · intro j hj
      rw [Pi.single_eq_of_ne (fun hq ↦ hj (congrArg Prod.snd hq)), Pi.zero_apply]
  · rw [Fintype.sum_eq_single q.1]
    · by_cases h : r.1 = q.2
      · rw [ite_eq_left h, h, Prod.mk.eta, Pi.single_eq_same]
      · rw [ite_eq_right h, Pi.single_eq_of_ne (fun hq ↦ h (congrArg Prod.snd hq)), Pi.zero_apply]
    · intro j hj
      rw [Pi.single_eq_of_ne (fun hq ↦ hj (congrArg Prod.fst hq)), Pi.zero_apply]

/-- Swapping the two Gram indices leaves the aggregated factor exponent unchanged. -/
@[simp]
theorem gramMonomialExponent_comp_swap (c : ι × ι → κ → ℕ) :
    gramMonomialExponent (c ∘ Prod.swap) = gramMonomialExponent c := by
  ext r
  simp only [gramMonomialExponent_apply, Function.comp_apply, Prod.swap_prod_mk]
  exact Finset.sum_congr rfl fun _ _ ↦ add_comm _ _

/-- An aggregated factor exponent vanishes at `r` precisely when every Gram pair involving `r.1`
assigns exponent zero to column `r.2`. -/
@[simp]
theorem gramMonomialExponent_apply_eq_zero_iff {c : ι × ι → κ → ℕ} {r : ι × κ} :
    gramMonomialExponent c r = 0 ↔ ∀ j : ι, c (r.1, j) r.2 = 0 ∧ c (j, r.1) r.2 = 0 := by
  simp [gramMonomialExponent_apply]

/-- Summing the factor exponents along row `i` recovers the total degree incident to `i`. -/
theorem sum_gramMonomialExponent_row [Fintype κ] (c : ι × ι → κ → ℕ) (i : ι) :
    (∑ k : κ, gramMonomialExponent c (i, k)) =
      ∑ j : ι, ((∑ k : κ, c (i, j) k) + ∑ k : κ, c (j, i) k) := by
  simp only [gramMonomialExponent_apply, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k j ↦ c (i, j) k),
    Finset.sum_comm (f := fun k j ↦ c (j, i) k)]

/-- The total degree of the aggregated factor monomial is twice the total Gram degree. -/
theorem sum_gramMonomialExponent [Fintype κ] (c : ι × ι → κ → ℕ) :
    (∑ r : ι × κ, gramMonomialExponent c r) = 2 * ∑ q : ι × ι, ∑ k : κ, c q k := by
  rw [Fintype.sum_prod_type]
  simp only [sum_gramMonomialExponent_row, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j ↦ ∑ k : κ, c (j, i) k), ← two_mul, Fintype.sum_prod_type]

/-- Every decomposition supported on `Finset.Iic (min q.1 q.2)` aggregates to a lower-triangular
exponent multi-index. -/
theorem le_of_gramMonomialExponent_ne_zero_of_mem_piFinset_piAntidiag_Iic
    [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {n : ι × ι → ℕ} {c : ι × ι → ι → ℕ}
    (hc : c ∈ Fintype.piFinset fun q ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q))
    {r : ι × ι} (hr : gramMonomialExponent c r ≠ 0) :
    r.2 ≤ r.1 := by
  rw [Ne, gramMonomialExponent_apply_eq_zero_iff, not_forall] at hr
  obtain ⟨j, hj⟩ := hr
  rcases not_and_or.mp hj with hj | hj
  · have hmem := (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hc (r.1, j))).2 r.2 hj
    exact le_trans (Finset.mem_Iic.mp hmem) (min_le_left _ _)
  · have hmem := (Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hc (j, r.1))).2 r.2 hj
    exact le_trans (Finset.mem_Iic.mp hmem) (min_le_right _ _)

end GramMonomialExponent

end TauCeti

namespace Matrix

section MulMonomial

variable {ι κ ν R : Type*}

private theorem prod_pow_left_factor [Fintype ι] [Fintype κ] [Fintype ν] [CommSemiring R]
    (A : Matrix ι κ R) (c : ι × ν → κ → ℕ) :
    (∏ q : ι × ν, ∏ k : κ, A q.1 k ^ c q k) =
      ∏ r : ι × κ, A r.1 r.2 ^ ∑ j : ν, c (r.1, j) r.2 := by
  calc
    (∏ q : ι × ν, ∏ k : κ, A q.1 k ^ c q k) =
        ∏ i : ι, ∏ j : ν, ∏ k : κ, A i k ^ c (i, j) k :=
      Fintype.prod_prod_type _
    _ = ∏ i : ι, ∏ k : κ, ∏ j : ν, A i k ^ c (i, j) k :=
      Finset.prod_congr rfl fun _ _ ↦ Finset.prod_comm
    _ = ∏ i : ι, ∏ k : κ, A i k ^ ∑ j : ν, c (i, j) k := by
      simp_rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ r : ι × κ, A r.1 r.2 ^ ∑ j : ν, c (r.1, j) r.2 :=
      (Fintype.prod_prod_type fun r : ι × κ ↦ A r.1 r.2 ^ ∑ j : ν, c (r.1, j) r.2).symm

private theorem prod_pow_right_factor [Fintype ι] [Fintype κ] [Fintype ν] [CommSemiring R]
    (B : Matrix κ ν R) (c : ι × ν → κ → ℕ) :
    (∏ q : ι × ν, ∏ k : κ, B k q.2 ^ c q k) =
      ∏ r : κ × ν, B r.1 r.2 ^ ∑ i : ι, c (i, r.2) r.1 := by
  calc
    (∏ q : ι × ν, ∏ k : κ, B k q.2 ^ c q k) =
        ∏ i : ι, ∏ j : ν, ∏ k : κ, B k j ^ c (i, j) k :=
      Fintype.prod_prod_type _
    _ = ∏ j : ν, ∏ i : ι, ∏ k : κ, B k j ^ c (i, j) k := Finset.prod_comm
    _ = ∏ j : ν, ∏ k : κ, ∏ i : ι, B k j ^ c (i, j) k :=
      Finset.prod_congr rfl fun _ _ ↦ Finset.prod_comm
    _ = ∏ k : κ, ∏ j : ν, ∏ i : ι, B k j ^ c (i, j) k := Finset.prod_comm
    _ = ∏ k : κ, ∏ j : ν, B k j ^ ∑ i : ι, c (i, j) k := by
      simp_rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ r : κ × ν, B r.1 r.2 ^ ∑ i : ι, c (i, r.2) r.1 :=
      (Fintype.prod_prod_type fun r : κ × ν ↦ B r.1 r.2 ^ ∑ i : ι, c (i, r.2) r.1).symm

/-- **Multinomial expansion of an entry monomial of a matrix product**, restricted to per-entry
summation supports `s q` outside which the summands `A q.1 k * B k q.2` vanish. -/
theorem prod_pow_mul_apply_of_support [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] [CommSemiring R]
    (A : Matrix ι κ R) (B : Matrix κ ν R) (n : ι × ν → ℕ)
    (s : ι × ν → Finset κ) (hs : ∀ q k, k ∉ s q → A q.1 k * B k q.2 = 0) :
    (∏ q : ι × ν, (A * B) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (s q) (n q)),
        (∏ q, (Nat.multinomial (s q) (c q) : R)) *
          ((∏ r : ι × κ, A r.1 r.2 ^ ∑ j : ν, c (r.1, j) r.2) *
            ∏ r : κ × ν, B r.1 r.2 ^ ∑ i : ι, c (i, r.2) r.1) := by
  have hentry (q : ι × ν) : (A * B) q.1 q.2 = ∑ k ∈ s q, A q.1 k * B k q.2 := by
    rw [Matrix.mul_apply]
    exact (Finset.sum_subset (Finset.subset_univ (s q)) fun k _ hk ↦ hs q k hk).symm
  simp_rw [hentry, Finset.sum_pow_eq_sum_piAntidiag]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  have hfull (q : ι × ν) :
      (∏ k ∈ s q, (A q.1 k * B k q.2) ^ c q k) =
        ∏ k : κ, (A q.1 k * B k q.2) ^ c q k := by
    refine Finset.prod_subset (Finset.subset_univ (s q)) fun k _ hk ↦ ?_
    have hck : c q k = 0 := by
      by_contra hne
      exact hk ((Finset.mem_piAntidiag.mp (Fintype.mem_piFinset.mp hc q)).2 k hne)
    simp [hck]
  simp_rw [hfull, mul_pow, Finset.prod_mul_distrib]
  rw [prod_pow_left_factor, prod_pow_right_factor]

/-- **Multinomial expansion of an entry monomial of a matrix product.** -/
theorem prod_pow_mul_apply [Fintype ι] [Fintype κ] [Fintype ν]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] [CommSemiring R]
    (A : Matrix ι κ R) (B : Matrix κ ν R) (n : ι × ν → ℕ) :
    (∏ q : ι × ν, (A * B) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (Finset.univ : Finset κ) (n q)),
        (∏ q, (Nat.multinomial Finset.univ (c q) : R)) *
          ((∏ r : ι × κ, A r.1 r.2 ^ ∑ j : ν, c (r.1, j) r.2) *
            ∏ r : κ × ν, B r.1 r.2 ^ ∑ i : ι, c (i, r.2) r.1) :=
  prod_pow_mul_apply_of_support A B n (fun _ ↦ Finset.univ) fun _ _ hk ↦
    (hk (Finset.mem_univ _)).elim

/-- **Multinomial expansion of a Gram entry monomial `∏ q, (L * Lᵀ) q.1 q.2 ^ n q`**, restricted to
per-entry column supports `s q` outside which `L q.1 k * L q.2 k = 0`. -/
theorem prod_pow_mul_transpose_apply_of_support [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [CommSemiring R]
    (L : Matrix ι κ R) (n : ι × ι → ℕ)
    (s : ι × ι → Finset κ) (hs : ∀ q k, k ∉ s q → L q.1 k * L q.2 k = 0) :
    (∏ q : ι × ι, (L * Lᵀ) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (s q) (n q)),
        (∏ q, (Nat.multinomial (s q) (c q) : R)) *
          ∏ r : ι × κ, L r.1 r.2 ^ TauCeti.gramMonomialExponent c r := by
  rw [prod_pow_mul_apply_of_support L Lᵀ n s fun q k hk ↦ by simpa using hs q k hk]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 1
  have htr :
      (∏ r : κ × ι, Lᵀ r.1 r.2 ^ ∑ i : ι, c (i, r.2) r.1) =
        ∏ r : ι × κ, L r.1 r.2 ^ ∑ j : ι, c (j, r.1) r.2 :=
    Fintype.prod_equiv (Equiv.prodComm κ ι) _ _ fun r ↦ by simp
  rw [htr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ ↦ ?_
  rw [← pow_add, ← Finset.sum_add_distrib, ← TauCeti.gramMonomialExponent_apply]

/-- **Multinomial expansion of a Gram entry monomial `∏ q, (L * Lᵀ) q.1 q.2 ^ n q`.** -/
theorem prod_pow_mul_transpose_apply [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [CommSemiring R]
    (L : Matrix ι κ R) (n : ι × ι → ℕ) :
    (∏ q : ι × ι, (L * Lᵀ) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (Finset.univ : Finset κ) (n q)),
        (∏ q, (Nat.multinomial Finset.univ (c q) : R)) *
          ∏ r : ι × κ, L r.1 r.2 ^ TauCeti.gramMonomialExponent c r :=
  prod_pow_mul_transpose_apply_of_support L n (fun _ ↦ Finset.univ) fun _ _ hk ↦
    (hk (Finset.mem_univ _)).elim

/-- For a lower-triangular matrix `L`, a Gram entry monomial `∏ q, (L * Lᵀ) q.1 q.2 ^ n q` expands
over column decompositions supported on `Finset.Iic (min q.1 q.2)`. -/
theorem IsLowerTriangular.prod_pow_mul_transpose_apply
    [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] [CommSemiring R]
    {L : Matrix ι ι R} (hL : L.IsLowerTriangular) (n : ι × ι → ℕ) :
    (∏ q : ι × ι, (L * Lᵀ) q.1 q.2 ^ n q) =
      ∑ c ∈ Fintype.piFinset (fun q ↦ Finset.piAntidiag (Finset.Iic (min q.1 q.2)) (n q)),
        (∏ q, (Nat.multinomial (Finset.Iic (min q.1 q.2)) (c q) : R)) *
          ∏ r : ι × ι, L r.1 r.2 ^ TauCeti.gramMonomialExponent c r := by
  refine prod_pow_mul_transpose_apply_of_support L n (fun q ↦ Finset.Iic (min q.1 q.2))
    fun q k hk ↦ ?_
  rw [Finset.mem_Iic, le_min_iff, not_and_or, not_le, not_le] at hk
  rcases hk with hk | hk
  · rw [hL hk, zero_mul]
  · rw [hL hk, mul_zero]

end MulMonomial

section SymmetryAndSign

variable {ι κ R : Type*}

/-- An entry monomial supported at a single matrix position `(i, k)` reduces to the corresponding
entry power. -/
@[simp]
theorem prod_pow_single_apply [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [CommMonoid R] (M : Matrix ι κ R) (i : ι) (k : κ) (m : ℕ) :
    (∏ q : ι × κ, M q.1 q.2 ^ Pi.single (i, k) m q) = M i k ^ m := by
  rw [Fintype.prod_eq_single (i, k) (fun q hq ↦ by simp [Pi.single_eq_of_ne hq]),
    Pi.single_eq_same]

/-- For a symmetric matrix with unit diagonal, an entry monomial indexed by all ordered pairs
reduces to the strict lower triangle, summing symmetric exponents and dropping diagonal ones. -/
theorem IsSymm.prod_pow_apply_of_diag_eq_one [Fintype ι] [LinearOrder ι] [CommMonoid R]
    {M : Matrix ι ι R} (hM : M.IsSymm) (hdiag : ∀ i, M i i = 1) (n : ι × ι → ℕ) :
    (∏ q : ι × ι, M q.1 q.2 ^ n q) =
      ∏ ij : {q : ι × ι // q.2 < q.1}, M ij.1.1 ij.1.2 ^ (n ij.1 + n ij.1.swap) := by
  have hsplit :
      (∏ q : ι × ι, M q.1 q.2 ^ n q) =
        (∏ q : ι × ι with q.2 < q.1, M q.1 q.2 ^ n q) *
          ∏ q : ι × ι with ¬ q.2 < q.1, M q.1 q.2 ^ n q :=
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun q : ι × ι ↦ q.2 < q.1)
      (fun q ↦ M q.1 q.2 ^ n q)).symm
  have hupper :
      (∏ q : ι × ι with ¬ q.2 < q.1, M q.1 q.2 ^ n q) =
        ∏ q : ι × ι with q.1 < q.2, M q.1 q.2 ^ n q := by
    symm
    refine Finset.prod_subset
      (fun q hq ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ q, (Finset.mem_filter.mp hq).2.not_gt⟩)
      fun q hq hnot ↦ ?_
    have hle : q.1 ≤ q.2 := not_lt.mp (Finset.mem_filter.mp hq).2
    have hlt_false : ¬ q.1 < q.2 := fun hlt ↦
      hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hlt⟩)
    have heq : q.1 = q.2 := le_antisymm hle (not_lt.mp hlt_false)
    simp [heq, hdiag]
  have hswap :
      (∏ q : ι × ι with q.1 < q.2, M q.1 q.2 ^ n q) =
        ∏ q : ι × ι with q.2 < q.1, M q.1 q.2 ^ n q.swap := by
    refine Finset.prod_bij (fun q _ ↦ q.swap) ?_ ?_ ?_ ?_
    · intro q hq
      simpa using (Finset.mem_filter.mp hq).2
    · intro a _ b _ hab
      exact Prod.swap_injective hab
    · intro b hb
      exact ⟨b.swap, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa using (Finset.mem_filter.mp hb).2⟩, Prod.swap_swap b⟩
    · intro q _
      rw [hM.apply q.2 q.1]
      rfl
  rw [hsplit, hupper, hswap, ← Finset.prod_mul_distrib]
  simp_rw [← pow_add]
  exact Finset.prod_subtype {q : ι × ι | q.2 < q.1} (fun _ ↦ by simp) _

/-- Conjugating a matrix by the diagonal sign matrix that flips axis `i` multiplies an entry
monomial `∏ q, M q.1 q.2 ^ n q` by `(-1)` raised to the total degree incident to `i`. -/
theorem prod_pow_signFlip_mul_apply [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (n : ι × ι → ℕ) (i : ι) :
    (∏ q : ι × ι,
        ((if q.1 = i then (-1 : R) else 1) * M q.1 q.2 *
          (if q.2 = i then (-1 : R) else 1)) ^ n q) =
      (-1 : R) ^ (∑ j : ι, (n (i, j) + n (j, i))) * ∏ q : ι × ι, M q.1 q.2 ^ n q := by
  have hleft :
      (∏ q : ι × ι, (if q.1 = i then (-1 : R) else 1) ^ n q) =
        (-1 : R) ^ ∑ j : ι, n (i, j) := by
    rw [Fintype.prod_prod_type, Fintype.prod_eq_single i]
    · simp [Finset.prod_pow_eq_pow_sum]
    · intro a ha
      simp [ha]
  have hright :
      (∏ q : ι × ι, (if q.2 = i then (-1 : R) else 1) ^ n q) =
        (-1 : R) ^ ∑ j : ι, n (j, i) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_eq_single i]
    · simp [Finset.prod_pow_eq_pow_sum]
    · intro b hb
      simp [hb]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [hleft, hright, mul_right_comm, ← pow_add, Finset.sum_add_distrib]

end SymmetryAndSign

end Matrix
