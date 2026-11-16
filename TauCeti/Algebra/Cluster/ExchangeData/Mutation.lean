/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSystem.Normalized
public import TauCeti.Algebra.Cluster.ExchangeData.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility
public import TauCeti.Algebra.Cluster.YSeed.Word

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.NNRat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Mutation of exchange data

Mutation of exchange data `d = (B, (H_k)_{k ∈ K})` in direction `k` with respect to a coefficient
system `c` consists of three steps:

1. Mutate the extended exchange matrix `B` to `B.mutation k`.
2. Reverse `H_k` to `H_k.reverse`.
3. For every `j ≠ k`, dilate `H_j` by `κ_{kj} = H_k.dilationFactor (d.dividedColumn j (row k))`
   and normalize the result via `c.normalize`.

This file defines `TauCeti.ExchangeData.mutatedPolynomial`, `TauCeti.ExchangeData.mutation`, and
the finite word action `TauCeti.ExchangeData.mutationWord`. It proves preservation of degrees,
column divisibility, normalization, endpoint-one and binary data, zero columns, and `H_k(1)`;
invariance of the exchange numerator `E_k(μ_k(d)) = E_k(d)`; involutivity of mutation and
reversibility of mutation words on normalized exchange data; and commutation with reindexing and
homomorphisms of coefficient systems.

For the normalized coefficient system of a coefficient semifield `P`, degree-one normalized
exchange data are identified with `Y`-seeds via `TauCeti.ExchangeData.ySeedEquiv`, intertwining
exchange-data mutation with `YSeed.mutation`.

## Main definitions

* `TauCeti.ExchangeData.mutatedPolynomial`: the mutated exchange polynomial in direction `j`.
* `TauCeti.ExchangeData.mutation`: single-step mutation of exchange data.
* `TauCeti.ExchangeData.mutationWord`: left-fold action of a finite list of mutation directions.
* `TauCeti.ExchangeData.ofYCoeff`: degree-one normalized exchange data from an exchange matrix and
  semifield coefficients `y : K → P`.
* `TauCeti.ExchangeData.ySeedEquiv`: the equivalence between `YSeed K P` and degree-one normalized
  square exchange data over `WithZero P`.

## Main results

* `TauCeti.ExchangeData.mutation_dividedColumn`: exact mutation formula for the divided columns.
* `TauCeti.ExchangeData.exchangeNumerator_mutation`: `E_k(μ_k(d)) = E_k(d)`.
* `TauCeti.ExchangeData.mutation_mutation`: mutation is involutive on normalized exchange data.
* `TauCeti.ExchangeData.mutation_reindex`, `TauCeti.ExchangeData.map_mutation`: equivariance under
  reindexing and homomorphisms of coefficient systems.
* `TauCeti.ExchangeData.mutationWord_mutationWord_reverse`: reversing a word inverts its action on
  normalized exchange data.
* `TauCeti.ExchangeData.mutation_ofYCoeff`, `TauCeti.ExchangeData.ySeedEquiv_mutation`: degree-one
  normalized mutation agrees with `Y`-seed mutation.

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. (2014), §2, equation (2.5).
* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007),
  Definition 2.3 and equation (2.3).
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2.
-/

public section

namespace TauCeti.ExchangeData

variable {𝕂 𝕂' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  {R : Type*} [CommSemiring R] {I I' K K' : Type*} {row : K ↪ I} {row' : K' ↪ I'}

/-! ### Single-step mutation -/

/-- The exchange polynomial in direction `j` after mutating `d` at `k`: `H_k` is reversed, and
every other `H_j` is dilated by `κ_{kj} = H_k.dilationFactor β_{kj}` and normalized by `c`. -/
noncomputable def mutatedPolynomial [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) : ExchangePolynomial 𝕂 :=
  if j = k then (d.polynomial k).reverse
  else c.normalize ((d.polynomial j).dilate
    ((d.polynomial k).dilationFactor (d.dividedColumn j (row k))))

@[simp]
theorem mutatedPolynomial_self [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    d.mutatedPolynomial c k k = (d.polynomial k).reverse := by
  simp [mutatedPolynomial]

theorem mutatedPolynomial_of_ne [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) {k j : K} (h : j ≠ k) :
    d.mutatedPolynomial c k j =
      c.normalize ((d.polynomial j).dilate
        ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))) := by
  simp [mutatedPolynomial, h]

@[simp]
theorem mutatedPolynomial_degree [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) :
    (d.mutatedPolynomial c k j).degree = (d.polynomial j).degree := by
  by_cases h : j = k
  · subst h
    simp
  · simp [mutatedPolynomial_of_ne c d h]

/-- Mutation of exchange data `d` in direction `k` with respect to the coefficient system `c`. -/
noncomputable def mutation [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) : ExchangeData 𝕂 row where
  exchange := d.exchange.mutation k
  polynomial j := d.mutatedPolynomial c k j
  degree_dvd i j := by
    rw [mutatedPolynomial_degree, ExchangeMatrix.mutation_matrix]
    exact dvd_matrixMutation (fun a ↦ d.degree_dvd a j) k i

@[simp]
theorem mutation_exchange [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchange = d.exchange.mutation k :=
  (rfl)

@[simp]
theorem mutation_polynomial [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) :
    (d.mutation c k).polynomial j = d.mutatedPolynomial c k j :=
  (rfl)

theorem mutation_polynomial_degree [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) :
    ((d.mutation c k).polynomial j).degree = (d.polynomial j).degree :=
  d.mutatedPolynomial_degree c k j

/-- Mutation in direction `k` negates the divided column `k`. -/
@[simp]
theorem mutation_dividedColumn_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    (d.mutation c k).dividedColumn k i = -d.dividedColumn k i := by
  simp only [dividedColumn_def, mutation_exchange, ExchangeMatrix.mutation_matrix,
    matrixMutation_apply_col, mutation_polynomial_degree]
  exact Int.neg_ediv_of_dvd (d.degree_dvd i k)

/-- Mutation in direction `k` negates the divided row `row k`. -/
@[simp]
theorem mutation_dividedColumn_row [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) :
    (d.mutation c k).dividedColumn j (row k) = -d.dividedColumn j (row k) := by
  simp only [dividedColumn_def, mutation_exchange, ExchangeMatrix.mutation_matrix,
    matrixMutation_apply_row, mutation_polynomial_degree]
  exact Int.neg_ediv_of_dvd (d.degree_dvd (row k) j)

/-- Exact mutation formula for the divided columns `β_j`. -/
theorem mutation_dividedColumn [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) (i : I) :
    (d.mutation c k).dividedColumn j i =
      if i = row k ∨ j = k then -d.dividedColumn j i
      else d.dividedColumn j i +
          ((d.polynomial k).degree : ℤ) * (d.dividedColumn k i)⁺ *
            (d.dividedColumn j (row k))⁺ -
          ((d.polynomial k).degree : ℤ) * (d.dividedColumn k i)⁻ *
            (d.dividedColumn j (row k))⁻ := by
  simpa only [dividedColumn_def, mutation_exchange, ExchangeMatrix.mutation_matrix,
    mutation_polynomial_degree] using
    matrixMutation_ediv_apply (row := row) (B := d.exchange.matrix)
      (fun l ↦ ((d.polynomial l).degree : ℤ))
      (fun l ↦ Nat.cast_pos.mpr (d.polynomial l).degree_pos) d.degree_dvd k i j

/-! ### Preservation properties, exchange numerator invariance, and involutivity -/

/-- Mutation preserves normalized exchange data. -/
theorem isNormalized_mutation [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (k : K) :
    (d.mutation c k).IsNormalized c := by
  rw [isNormalized_iff] at hd ⊢
  intro j
  by_cases h : j = k
  · subst h
    simpa using hd j
  · simp [mutatedPolynomial_of_ne c d h]

/-- On normalized data with endpoint coefficients equal to `1`, mutation reverses `H_k` and leaves
all other exchange polynomials unchanged, preserving the endpoint-one property. -/
theorem isEndpointOne_mutation [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    {d : ExchangeData 𝕂 row} (hnorm : d.IsNormalized c) (hend : d.IsEndpointOne) (k : K) :
    (d.mutation c k).IsEndpointOne := by
  rw [isNormalized_iff] at hnorm
  rw [isEndpointOne_iff] at hend ⊢
  intro j
  by_cases h : j = k
  · subst h
    simpa using hend j
  · rw [mutation_polynomial, mutatedPolynomial_of_ne c d h,
      (hend k).dilationFactor_eq_one, ExchangePolynomial.dilate_one,
      (c.normalize_eq_self_iff _).mpr (hnorm j)]
    exact hend j

/-- Whenever the binary polynomial is normalized in `c`, mutation preserves binary exchange data. -/
theorem isBinary_mutation [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (hbin : c.IsNormalized ExchangePolynomial.binary) {d : ExchangeData 𝕂 row} (hd : d.IsBinary)
    (k : K) : (d.mutation c k).IsBinary := by
  rw [isBinary_iff] at hd ⊢
  intro j
  by_cases h : j = k
  · subst h
    simp [hd j]
  · simp [mutatedPolynomial_of_ne c d h, hd k, hd j, hbin]

/-- A column is zero after exchange-data mutation if and only if it was zero before. -/
theorem mutation_column_eq_zero_iff [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k j : K) :
    (∀ i, (d.mutation c k).exchange.matrix i j = 0) ↔ ∀ i, d.exchange.matrix i j = 0 := by
  simpa only [mutation_exchange, ExchangeMatrix.mutation_matrix] using
    matrixMutation_column_eq_zero_iff (row := row) (B := d.exchange.matrix) (j := j) k

/-- Away from the mutation direction, a normalized polynomial on a zero column is unchanged by
mutation. -/
theorem mutation_polynomial_of_col_eq_zero [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) {k j : K} (hne : j ≠ k)
    (hnorm : c.IsNormalized (d.polynomial j)) (hzero : ∀ i, d.exchange.matrix i j = 0) :
    (d.mutation c k).polynomial j = d.polynomial j := by
  have hdiv : d.dividedColumn j (row k) = 0 :=
    (d.dividedColumn_eq_zero_iff j (row k)).mpr (hzero (row k))
  rw [mutation_polynomial, mutatedPolynomial_of_ne c d hne, hdiv,
    ExchangePolynomial.dilationFactor_zero, ExchangePolynomial.dilate_one,
    (c.normalize_eq_self_iff _).mpr hnorm]

/-- Mutation in direction `k` preserves the scalar sum `H_k(1)`. -/
@[simp]
theorem valueAtOne_mutation_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).valueAtOne c k = d.valueAtOne c k := by
  simp only [valueAtOne_def, mutation_polynomial, mutatedPolynomial_self,
    ExchangePolynomial.reverse_degree]
  have hsum :
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
          c.toScalar ((d.polynomial k).reverse.coeff l) =
        ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
          c.toScalar ((d.polynomial k).coeff ((d.polynomial k).degree + 1 - 1 - l)) := by
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hle : l ≤ (d.polynomial k).degree := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    simp [hle]
  exact hsum.trans (Finset.sum_range_reflect
    (fun l ↦ c.toScalar ((d.polynomial k).coeff l)) ((d.polynomial k).degree + 1))

/-- On normalized exchange data, mutation preserves `H_j(1)` for every zero column `j`. -/
theorem valueAtOne_mutation_of_col_eq_zero [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row} (hnorm : d.IsNormalized c) (k j : K)
    (hzero : ∀ i, d.exchange.matrix i j = 0) :
    (d.mutation c k).valueAtOne c j = d.valueAtOne c j := by
  rw [isNormalized_iff] at hnorm
  by_cases h : j = k
  · subst h
    exact d.valueAtOne_mutation_self c j
  · rw [valueAtOne_def, valueAtOne_def,
      d.mutation_polynomial_of_col_eq_zero c h (hnorm j) hzero]

/-- Mutation in direction `k` leaves the exchange numerator `E_k` unchanged. -/
@[simp]
theorem exchangeNumerator_mutation [Finite I] [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchangeNumerator c k = d.exchangeNumerator c k := by
  simp only [exchangeNumerator_def, mutation_polynomial, mutatedPolynomial_self,
    ExchangePolynomial.reverse_degree, mutation_dividedColumn_self, posPart_neg, negPart_neg]
  have hsum :
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
          AddMonoidAlgebra.single
            (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
              (l : ℤ) * (d.dividedColumn k i.1)⁻ +
                (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i.1)⁺)
            (c.toScalar ((d.polynomial k).reverse.coeff l)) =
        ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
          AddMonoidAlgebra.single
            (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
              (((d.polynomial k).degree + 1 - 1 - l : ℕ) : ℤ) * (d.dividedColumn k i.1)⁺ +
                (((d.polynomial k).degree - ((d.polynomial k).degree + 1 - 1 - l) : ℕ) : ℤ) *
                  (d.dividedColumn k i.1)⁻)
            (c.toScalar ((d.polynomial k).coeff ((d.polynomial k).degree + 1 - 1 - l))) := by
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hle : l ≤ (d.polynomial k).degree := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    congr 1
    · ext i
      simp [Nat.sub_sub_self hle, add_comm]
    · simp [hle]
  exact hsum.trans (Finset.sum_range_reflect (fun l ↦
    AddMonoidAlgebra.single
      (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
        (l : ℤ) * (d.dividedColumn k i.1)⁺ +
          (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i.1)⁻)
      (c.toScalar ((d.polynomial k).coeff l))) ((d.polynomial k).degree + 1))

/-- Mutation is an involution on normalized exchange data. -/
theorem mutation_mutation [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (k : K) :
    (d.mutation c k).mutation c k = d := by
  rw [isNormalized_iff] at hd
  ext : 1
  · simp
  · funext j
    by_cases h : j = k
    · subst h
      simp
    · simp only [mutation_polynomial, mutatedPolynomial_of_ne c _ h, mutatedPolynomial_self,
        mutation_dividedColumn_row, ExchangePolynomial.dilationFactor_reverse_neg]
      let H := (d.polynomial j).dilate
        ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))
      rw [CoefficientSystem.normalize_def c H, ExchangePolynomial.dilate_scale,
        ExchangePolynomial.dilate_inv_dilate,
        c.normalize_scale_of_mem (c.normalizer_mem_normalizerSubgroup H),
        (c.normalize_eq_self_iff _).mpr (hd j)]

/-! ### Functoriality under reindexing and coefficient-system homomorphisms -/

/-- Reindexing carries mutation in direction `k` to mutation in direction `eK k`. -/
theorem mutation_reindex [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
    (c : CoefficientSystem 𝕂 R) (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) (k : K) :
    (reindex eI eK h d).mutation c (eK k) = reindex eI eK h (d.mutation c k) := by
  ext : 1
  · simp only [mutation_exchange, reindex_exchange]
    exact d.exchange.mutation_reindex eI eK h k
  · funext j
    by_cases hj : j = eK k
    · subst hj
      simp
    · have hj' : eK.symm j ≠ k := by simpa [Equiv.symm_apply_eq] using hj
      have hrow : eI.symm (row' (eK k)) = row k := by rw [← h k, Equiv.symm_apply_apply]
      simp [mutatedPolynomial_of_ne c _ hj, mutatedPolynomial_of_ne c _ hj', hrow]

/-- A homomorphism of coefficient systems commutes with exchange-data mutation. -/
theorem map_mutation [DecidableEq I] [DecidableEq K]
    {c₁ : CoefficientSystem 𝕂 R} {c₂ : CoefficientSystem 𝕂' R} (ψ : c₁.Hom c₂)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c₁ k).map ψ.toMonoidWithZeroHom =
      (d.map ψ.toMonoidWithZeroHom).mutation c₂ k := by
  ext : 1
  · simp
  · funext j
    by_cases h : j = k
    · subst h
      simp
    · simp [mutatedPolynomial_of_ne _ _ h]

/-! ### Finite mutation words -/

/-- Apply a finite sequence of mutations to exchange data in reading order. -/
noncomputable def mutationWord [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (w : List K) : ExchangeData 𝕂 row :=
  w.foldl (mutation c) d

/-- The word action is the left fold of single-step exchange-data mutation. -/
theorem mutationWord_eq_foldl [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (w : List K) :
    d.mutationWord c w = w.foldl (mutation c) d :=
  (rfl)

@[simp]
theorem mutationWord_nil [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) : d.mutationWord c [] = d :=
  (rfl)

@[simp]
theorem mutationWord_cons [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) (w : List K) :
    d.mutationWord c (k :: w) = (d.mutation c k).mutationWord c w :=
  (rfl)

@[simp]
theorem mutationWord_append [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (u v : List K) :
    d.mutationWord c (u ++ v) = (d.mutationWord c u).mutationWord c v :=
  List.foldl_append

@[simp]
theorem mutationWord_exchange [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (w : List K) :
    (d.mutationWord c w).exchange = d.exchange.mutationWord w := by
  rw [mutationWord, ExchangeMatrix.mutationWord_eq_foldl]
  exact (List.foldl_hom (fun d : ExchangeData 𝕂 row ↦ d.exchange) (fun _ _ ↦ rfl)).symm

@[simp]
theorem mutationWord_polynomial_degree [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (w : List K) (j : K) :
    ((d.mutationWord c w).polynomial j).degree = (d.polynomial j).degree := by
  induction w generalizing d with
  | nil => rfl
  | cons k _ ih => simpa using ih (d.mutation c k)

/-- Every finite mutation word preserves normalized exchange data. -/
theorem isNormalized_mutationWord [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w).IsNormalized c := by
  induction w generalizing d with
  | nil => exact hd
  | cons k _ ih => exact ih (d.isNormalized_mutation c hd k)

/-- Reversing a mutation word inverts its action on normalized exchange data. -/
theorem mutationWord_mutationWord_reverse [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w).mutationWord c w.reverse = d := by
  induction w generalizing d with
  | nil => simp
  | cons k w ih =>
    rw [List.reverse_cons, mutationWord_cons, mutationWord_append,
      ih (d.isNormalized_mutation c hd k), mutationWord_cons, mutationWord_nil,
      d.mutation_mutation c hd k]

/-- Applying the reversed mutation word first also inverts the word action on normalized data. -/
theorem mutationWord_reverse_mutationWord [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w.reverse).mutationWord c w = d := by
  simpa only [List.reverse_reverse] using
    d.mutationWord_mutationWord_reverse c hd w.reverse

/-- Equal adjacent directions cancel inside a mutation word on normalized exchange data. -/
theorem mutationWord_append_cons_cons_self [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c)
    (u v : List K) (k : K) :
    d.mutationWord c (u ++ k :: k :: v) = d.mutationWord c (u ++ v) := by
  simp [mutation_mutation c (d.isNormalized_mutationWord c hd u) k]

/-- Reindexing transports every finite mutation word. -/
theorem reindex_mutationWord [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
    (c : CoefficientSystem 𝕂 R) (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) (w : List K) :
    reindex eI eK h (d.mutationWord c w) = (reindex eI eK h d).mutationWord c (w.map eK) := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (reindex eI eK h) (fun x k ↦ x.mutation_reindex c eI eK h k)).symm

/-- Homomorphisms of coefficient systems commute with every finite mutation word. -/
@[simp]
theorem map_mutationWord [DecidableEq I] [DecidableEq K]
    {c₁ : CoefficientSystem 𝕂 R} {c₂ : CoefficientSystem 𝕂' R} (ψ : c₁.Hom c₂)
    (d : ExchangeData 𝕂 row) (w : List K) :
    (d.mutationWord c₁ w).map ψ.toMonoidWithZeroHom =
      (d.map ψ.toMonoidWithZeroHom).mutationWord c₂ w :=
  (List.foldl_hom (map ψ.toMonoidWithZeroHom) (fun x k ↦ (x.map_mutation ψ k).symm)).symm

/-! ### Degree-one normalized data and equivalence with `Y`-seeds -/

section Normalized

variable {P Q : Type*} [CoefficientSemifield P] [CoefficientSemifield Q]

/-- Degree-one normalized exchange data over `WithZero P` built from an extended exchange matrix
and semifield coefficients `y : K → P`. -/
def ofYCoeff (B : ExchangeMatrix row) (y : K → P) : ExchangeData (WithZero P) row where
  exchange := B
  polynomial k := CoefficientSystem.normalizedBinomial (y k)
  degree_dvd _ _ := by simp

@[simp]
theorem ofYCoeff_exchange (B : ExchangeMatrix row) (y : K → P) :
    (ofYCoeff B y).exchange = B :=
  (rfl)

@[simp]
theorem ofYCoeff_polynomial (B : ExchangeMatrix row) (y : K → P) (k : K) :
    (ofYCoeff B y).polynomial k = CoefficientSystem.normalizedBinomial (y k) :=
  (rfl)

@[simp]
theorem ofYCoeff_dividedColumn (B : ExchangeMatrix row) (y : K → P) (k : K) (i : I) :
    (ofYCoeff B y).dividedColumn k i = B.matrix i k := by
  simp [dividedColumn_def]

@[simp]
theorem isNormalized_ofYCoeff (φ : P →* Rˣ) (B : ExchangeMatrix row) (y : K → P) :
    (ofYCoeff B y).IsNormalized (CoefficientSystem.normalized φ) := by
  rw [isNormalized_iff]
  intro k
  exact CoefficientSystem.isNormalized_normalizedBinomial φ (y k)

/-- Mutating degree-one normalized exchange data performs matrix mutation together with `Y`-mutation
using the principal block `B.matrix (row k) j`. -/
theorem mutation_ofYCoeff [DecidableEq I] [DecidableEq K] (φ : P →* Rˣ)
    (B : ExchangeMatrix row) (y : K → P) (k : K) :
    (ofYCoeff B y).mutation (CoefficientSystem.normalized φ) k =
      ofYCoeff (B.mutation k) fun j ↦
        if j = k then (y k)⁻¹
        else y j * y k ^ (B.matrix (row k) j)⁺ * (y k + 1) ^ (-B.matrix (row k) j) := by
  ext : 1
  · rfl
  · funext j
    by_cases h : j = k
    · subst h
      simp
    · rw [mutation_polynomial, mutatedPolynomial_of_ne _ _ h, ofYCoeff_polynomial,
        ofYCoeff_polynomial, ofYCoeff_dividedColumn,
        CoefficientSystem.dilationFactor_normalizedBinomial,
        CoefficientSystem.normalize_dilate_normalizedBinomial, ofYCoeff_polynomial]
      simp [h, mul_assoc]

/-- The exchange numerator of degree-one normalized exchange data has the standard binomial form
`φ(y_k + 1)⁻¹ (φ(y_k) m_{k,+} + m_{k,-})`. -/
theorem exchangeNumerator_ofYCoeff [Finite I] (φ : P →* Rˣ)
    (B : ExchangeMatrix row) (y : K → P) (k : K) :
    (ofYCoeff B y).exchangeNumerator (CoefficientSystem.normalized φ) k =
      ((φ (y k + 1)⁻¹ : Rˣ) : R) •
        (((φ (y k) : Rˣ) : R) •
          AddMonoidAlgebra.single
            (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦ (B.matrix i.1 k)⁺) 1 +
          AddMonoidAlgebra.single
            (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
              (B.matrix i.1 k)⁻) 1) := by
  rw [exchangeNumerator_def, ofYCoeff_polynomial, CoefficientSystem.normalizedBinomial_degree,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [ofYCoeff_dividedColumn, CoefficientSystem.normalizedBinomial_coeff_zero,
    CoefficientSystem.normalizedBinomial_coeff_one, CoefficientSystem.normalized_toScalar_coe,
    map_mul, Units.val_mul, Nat.cast_zero, zero_mul, zero_add, Nat.sub_zero, Nat.cast_one, one_mul,
    Nat.sub_self, smul_add, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one, add_comm]
  rw [mul_comm ((φ (y k + 1)⁻¹ : Rˣ) : R)]

/-- Equivalence between `Y`-seeds over `P` and degree-one normalized square exchange data over
`WithZero P`. -/
noncomputable def ySeedEquiv (φ : P →* Rˣ) :
    YSeed K P ≃
      {d : ExchangeData (WithZero P) (Function.Embedding.refl K) //
        (∀ k, (d.polynomial k).degree = 1) ∧
          d.IsNormalized (CoefficientSystem.normalized φ)} where
  toFun s := ⟨ofYCoeff s.exchangeMatrix s.coefficient,
    fun k ↦ CoefficientSystem.normalizedBinomial_degree (s.coefficient k),
    isNormalized_ofYCoeff φ s.exchangeMatrix s.coefficient⟩
  invFun d :=
    { coefficient := fun k ↦
        (CoefficientSystem.normalizedBinomialEquiv φ).symm
          ⟨d.1.polynomial k, d.2.1 k, (isNormalized_iff _ _).mp d.2.2 k⟩
      exchangeMatrix := d.1.exchange }
  left_inv s := by
    ext : 1
    · funext k
      have heq :
          (⟨(ofYCoeff s.exchangeMatrix s.coefficient).polynomial k,
              CoefficientSystem.normalizedBinomial_degree (s.coefficient k),
              (isNormalized_iff _ _).mp
                (isNormalized_ofYCoeff φ s.exchangeMatrix s.coefficient) k⟩ :
            {H : ExchangePolynomial (WithZero P) //
              H.degree = 1 ∧ (CoefficientSystem.normalized φ).IsNormalized H}) =
            CoefficientSystem.normalizedBinomialEquiv φ (s.coefficient k) :=
        Subtype.ext (CoefficientSystem.normalizedBinomialEquiv_apply φ (s.coefficient k)).symm
      dsimp only
      rw [heq]
      exact (CoefficientSystem.normalizedBinomialEquiv φ).symm_apply_apply (s.coefficient k)
    · rfl
  right_inv d := by
    apply Subtype.ext
    ext : 1
    · rfl
    · funext k
      simpa only [ofYCoeff_polynomial, ← CoefficientSystem.normalizedBinomialEquiv_apply φ] using
        congrArg Subtype.val
          ((CoefficientSystem.normalizedBinomialEquiv φ).apply_symm_apply
            ⟨d.1.polynomial k, d.2.1 k, (isNormalized_iff _ _).mp d.2.2 k⟩)

@[simp]
theorem ySeedEquiv_apply (φ : P →* Rˣ) (s : YSeed K P) :
    (ySeedEquiv φ s).1 = ofYCoeff s.exchangeMatrix s.coefficient :=
  (rfl)

/-- `ySeedEquiv` intertwines `YSeed.mutation` with exchange-data mutation. -/
theorem ySeedEquiv_mutation [DecidableEq K] (φ : P →* Rˣ) (s : YSeed K P) (k : K) :
    (ySeedEquiv φ (s.mutation k)).1 =
      (ySeedEquiv φ s).1.mutation (CoefficientSystem.normalized φ) k := by
  rw [ySeedEquiv_apply, ySeedEquiv_apply, mutation_ofYCoeff]
  ext : 1
  · simp
  · funext j
    by_cases h : j = k
    · subst h
      simp
    · simp [h, YSeed.mutation_coefficient_of_ne]

/-- `ySeedEquiv` intertwines finite mutation words on `Y`-seeds and exchange data. -/
theorem ySeedEquiv_mutationWord [DecidableEq K] (φ : P →* Rˣ) (s : YSeed K P) (w : List K) :
    (ySeedEquiv φ (s.mutationWord w)).1 =
      (ySeedEquiv φ s).1.mutationWord (CoefficientSystem.normalized φ) w := by
  rw [YSeed.mutationWord_eq_foldl, mutationWord_eq_foldl]
  exact (List.foldl_hom (fun s : YSeed K P ↦ (ySeedEquiv φ s).1)
    (fun s k ↦ (ySeedEquiv_mutation φ s k).symm)).symm

/-- `ySeedEquiv` intertwines `YSeed.map` with pushforward along `WithZero.map'`. -/
theorem ySeedEquiv_map (f : CoefficientSemifieldHom P Q) (φ₁ : P →* Rˣ) (φ₂ : Q →* Rˣ)
    (s : YSeed K P) :
    (ySeedEquiv φ₂ (s.map f)).1 = (ySeedEquiv φ₁ s).1.map (WithZero.map' f.toMonoidHom) := by
  ext : 1
  · simp
  · funext k
    simp [ofYCoeff]

/-- `ySeedEquiv` intertwines `YSeed.reindex` with `ExchangeData.reindex`. -/
theorem ySeedEquiv_reindex (φ : P →* Rˣ) (e : K ≃ K') (s : YSeed K P) :
    (ySeedEquiv φ (YSeed.reindex e s)).1 =
      reindex (row := Function.Embedding.refl K) (row' := Function.Embedding.refl K')
        e e (fun _ ↦ by simp only [Function.Embedding.refl_apply]) (ySeedEquiv φ s).1 := by
  ext : 1
  · simp
  · funext k
    simp

end Normalized

/-! ### Rank-two examples -/

section Examples

private def nnratUnit (q : ℚ≥0) (hq : q ≠ 0 := by norm_num) : ℚ≥0ˣ :=
  Units.mk0 q hq

private def quadPoly (a b c : ℚ≥0ˣ) : ExchangePolynomial (WithZero ℚ≥0ˣ) where
  degree := 2
  degree_pos := by decide
  coeff
    | 0 => (a : WithZero ℚ≥0ˣ)
    | 1 => (b : WithZero ℚ≥0ˣ)
    | 2 => (c : WithZero ℚ≥0ˣ)
    | _ + 3 => 0
  coeff_of_gt l hl := by
    obtain _ | _ | _ | l := l <;> first | omega | rfl
  isUnit_coeff_zero := (WithZero.unitsWithZeroEquiv.symm a).isUnit
  isUnit_coeff_degree := (WithZero.unitsWithZeroEquiv.symm c).isUnit

private theorem quadPoly_degree (a b c : ℚ≥0ˣ) : (quadPoly a b c).degree = 2 := (rfl)
private theorem quadPoly_coeff_zero (a b c : ℚ≥0ˣ) :
    (quadPoly a b c).coeff 0 = (a : WithZero ℚ≥0ˣ) := (rfl)
private theorem quadPoly_coeff_one (a b c : ℚ≥0ˣ) :
    (quadPoly a b c).coeff 1 = (b : WithZero ℚ≥0ˣ) := (rfl)
private theorem quadPoly_coeff_two (a b c : ℚ≥0ˣ) :
    (quadPoly a b c).coeff 2 = (c : WithZero ℚ≥0ˣ) := (rfl)

private theorem reverse_quadPoly (a b c : ℚ≥0ˣ) : (quadPoly a b c).reverse = quadPoly c b a := by
  ext l hl
  · simp [quadPoly_degree]
  · simp only [ExchangePolynomial.reverse_degree, quadPoly_degree] at hl
    have hl' : l = 0 ∨ l = 1 ∨ l = 2 := by omega
    rcases hl' with rfl | rfl | rfl <;>
      simp [quadPoly_degree, quadPoly_coeff_zero, quadPoly_coeff_one, quadPoly_coeff_two]

private theorem dilationFactor_quadPoly_one (a b c : ℚ≥0ˣ) :
    (quadPoly a b c).dilationFactor 1 = WithZero.unitsWithZeroEquiv.symm c := by
  rw [(quadPoly a b c).dilationFactor_eq 1
    (u₀ := WithZero.unitsWithZeroEquiv.symm a)
    (uᵣ := WithZero.unitsWithZeroEquiv.symm c) rfl rfl]
  simp

private theorem normalize_dilate_quadPoly (a b c κ : ℚ≥0ˣ) :
    (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)).normalize
        ((quadPoly a b c).dilate (WithZero.unitsWithZeroEquiv.symm κ)) =
      quadPoly ((a + b * κ + c * κ ^ 2)⁻¹ * a)
        ((a + b * κ + c * κ ^ 2)⁻¹ * (b * κ))
        ((a + b * κ + c * κ ^ 2)⁻¹ * (c * κ ^ 2)) := by
  let H := (quadPoly a b c).dilate (WithZero.unitsWithZeroEquiv.symm κ)
  have hν : (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)).normalizer H =
      WithZero.unitsWithZeroEquiv.symm (a + b * κ + c * κ ^ 2)⁻¹ := by
    apply Units.ext
    rw [CoefficientSystem.val_normalized_normalizer]
    have hdeg : H.degree = 2 := by simp [H, quadPoly_degree]
    rw [hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [H, ExchangePolynomial.dilate_coeff, quadPoly_coeff_zero, quadPoly_coeff_one,
      quadPoly_coeff_two, WithZero.unitsWithZeroEquiv_symm_apply, Units.val_mk0, pow_zero, mul_one,
      pow_one, ← WithZero.coe_mul, ← WithZero.coe_add, ← WithZero.coe_pow, ← WithZero.coe_inv]
  ext l hl
  · simp [quadPoly_degree]
  · simp only [CoefficientSystem.normalize_degree, ExchangePolynomial.dilate_degree,
      quadPoly_degree] at hl
    have hl' : l = 0 ∨ l = 1 ∨ l = 2 := by omega
    rcases hl' with rfl | rfl | rfl <;>
      rw [CoefficientSystem.normalize_def, hν] <;>
      simp [quadPoly_coeff_zero, quadPoly_coeff_one, quadPoly_coeff_two,
        -WithZero.coe_add, -WithZero.coe_inv, ← WithZero.coe_mul, ← WithZero.coe_pow]

private def rankTwoA2Pos : ExchangeMatrix (Function.Embedding.refl (Fin 2)) where
  matrix := !![0, 1; -1, 0]
  symmetrizer := ![1, 1]
  isSkewSymmetrizer := ⟨by decide, by decide⟩

private def rankTwoA2Neg : ExchangeMatrix (Function.Embedding.refl (Fin 2)) where
  matrix := !![0, -1; 1, 0]
  symmetrizer := ![1, 1]
  isSkewSymmetrizer := ⟨by decide, by decide⟩

private theorem rankTwoA2Pos_mutation_zero (y₀ y₁ : ℚ≥0ˣ) :
    (ofYCoeff rankTwoA2Pos ![y₀, y₁]).mutation
        (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) 0 =
      ofYCoeff rankTwoA2Neg ![y₀⁻¹, y₁ * y₀ * (y₀ + 1)⁻¹] := by
  rw [mutation_ofYCoeff]
  have hB : rankTwoA2Pos.mutation 0 = rankTwoA2Neg := by
    ext : 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [rankTwoA2Pos, rankTwoA2Neg, matrixMutation_apply]
    · simp [rankTwoA2Pos, rankTwoA2Neg]
  rw [hB]
  congr 1
  funext j
  fin_cases j <;> simp [rankTwoA2Pos]

private theorem rankTwoA2Neg_mutation_one (y₀ y₁ : ℚ≥0ˣ) :
    (ofYCoeff rankTwoA2Neg ![y₀, y₁]).mutation
        (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) 1 =
      ofYCoeff rankTwoA2Pos ![y₀ * y₁ * (y₁ + 1)⁻¹, y₁⁻¹] := by
  rw [mutation_ofYCoeff]
  have hB : rankTwoA2Neg.mutation 1 = rankTwoA2Pos := by
    ext : 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [rankTwoA2Pos, rankTwoA2Neg, matrixMutation_apply]
    · simp [rankTwoA2Pos, rankTwoA2Neg]
  rw [hB]
  congr 1
  funext j
  fin_cases j <;> simp [rankTwoA2Neg]

/-- In type `A₂` over the normalized system of `ℚ≥0ˣ`, five alternating mutations on `y = ![2, 3]`
interchange the two coefficients to `![3, 2]`. -/
example :
    ((ofYCoeff rankTwoA2Pos ![nnratUnit 2, nnratUnit 3]).mutationWord
        (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) [0, 1, 0, 1, 0]).polynomial =
      ![CoefficientSystem.normalizedBinomial (nnratUnit 3),
        CoefficientSystem.normalizedBinomial (nnratUnit 2)] := by
  have hpair {M : ExchangeMatrix (Function.Embedding.refl (Fin 2))}
      {a₁ a₂ b₁ b₂ : ℚ≥0ˣ} (ha : (a₁ : ℚ≥0) = a₂) (hb : (b₁ : ℚ≥0) = b₂) :
      ofYCoeff M ![a₁, b₁] = ofYCoeff M ![a₂, b₂] := by
    rw [Units.ext ha, Units.ext hb]
  have hword :
      (ofYCoeff rankTwoA2Pos ![nnratUnit 2, nnratUnit 3]).mutationWord
          (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) [0, 1, 0, 1, 0] =
        ofYCoeff rankTwoA2Neg ![nnratUnit 3, nnratUnit 2] := by
    rw [mutationWord_cons, rankTwoA2Pos_mutation_zero,
      hpair (a₂ := nnratUnit (1 / 2)) (b₂ := nnratUnit 2)
        (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
      mutationWord_cons, rankTwoA2Neg_mutation_one,
      hpair (a₂ := nnratUnit (1 / 3)) (b₂ := nnratUnit (1 / 2))
        (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
      mutationWord_cons, rankTwoA2Pos_mutation_zero,
      hpair (a₂ := nnratUnit 3) (b₂ := nnratUnit (1 / 8))
        (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
      mutationWord_cons, rankTwoA2Neg_mutation_one,
      hpair (a₂ := nnratUnit (1 / 3)) (b₂ := nnratUnit 8)
        (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
      mutationWord_cons, rankTwoA2Pos_mutation_zero, mutationWord_nil]
    exact hpair (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
  rw [hword]
  funext j
  fin_cases j <;> rfl

private def rankTwoB2Pos : ExchangeMatrix (Function.Embedding.refl (Fin 2)) where
  matrix := !![0, 2; -1, 0]
  symmetrizer := ![1, 2]
  isSkewSymmetrizer := ⟨by decide, by decide⟩

private def rankTwoB2Neg : ExchangeMatrix (Function.Embedding.refl (Fin 2)) where
  matrix := !![0, -2; 1, 0]
  symmetrizer := ![1, 2]
  isSkewSymmetrizer := ⟨by decide, by decide⟩

private def rankTwoQuadData (pos : Bool) (y a b c : ℚ≥0ˣ) :
    ExchangeData (WithZero ℚ≥0ˣ) (Function.Embedding.refl (Fin 2)) where
  exchange := if pos then rankTwoB2Pos else rankTwoB2Neg
  polynomial := ![CoefficientSystem.normalizedBinomial y, quadPoly a b c]
  degree_dvd i k := by
    cases pos <;> fin_cases i <;> fin_cases k <;>
      simp [rankTwoB2Pos, rankTwoB2Neg, quadPoly_degree]

private theorem rankTwoQuadData_mutation_zero (y a b c : ℚ≥0ˣ) :
    (rankTwoQuadData true y a b c).mutation
        (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) 0 =
      let κ := y * (y + 1)⁻¹
      let s := a + b * κ + c * κ ^ 2
      rankTwoQuadData false y⁻¹ (s⁻¹ * a) (s⁻¹ * (b * κ)) (s⁻¹ * (c * κ ^ 2)) := by
  ext : 1
  · ext : 1
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rankTwoQuadData, rankTwoB2Pos, rankTwoB2Neg, matrixMutation_apply]
    · simp [rankTwoQuadData, rankTwoB2Pos, rankTwoB2Neg]
  · funext j
    match j with
    | 0 => simp [rankTwoQuadData, mutatedPolynomial_self]
    | 1 =>
      have hdiv : (rankTwoQuadData true y a b c).dividedColumn 1 0 = 1 := by
        simp [dividedColumn_def, rankTwoQuadData, rankTwoB2Pos, quadPoly_degree]
      have hpos : (1 : ℤ)⁺ = 1 := by decide
      rw [mutation_polynomial, mutatedPolynomial_of_ne _ _ (by decide),
        Function.Embedding.refl_apply, hdiv]
      simp only [rankTwoQuadData, Matrix.cons_val_zero, Matrix.cons_val_one,
        CoefficientSystem.dilationFactor_normalizedBinomial, hpos, zpow_one, zpow_neg_one]
      exact normalize_dilate_quadPoly a b c (y * (y + 1)⁻¹)

private theorem rankTwoQuadData_mutation_one (y a b c : ℚ≥0ˣ) :
    (rankTwoQuadData false y a b c).mutation
        (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) 1 =
      rankTwoQuadData true (y * c) c b a := by
  ext : 1
  · ext : 1
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rankTwoQuadData, rankTwoB2Pos, rankTwoB2Neg, matrixMutation_apply]
    · simp [rankTwoQuadData, rankTwoB2Pos, rankTwoB2Neg]
  · funext j
    match j with
    | 0 =>
      have hdiv : (rankTwoQuadData false y a b c).dividedColumn 0 1 = 1 := by
        simp [dividedColumn_def, rankTwoQuadData, rankTwoB2Neg]
      rw [mutation_polynomial, mutatedPolynomial_of_ne _ _ (by decide),
        Function.Embedding.refl_apply, hdiv]
      simp only [rankTwoQuadData, Matrix.cons_val_zero, Matrix.cons_val_one,
        dilationFactor_quadPoly_one]
      exact CoefficientSystem.normalize_dilate_normalizedBinomial (1 : ℚ≥0ˣ →* ℚˣ) y c
    | 1 => simp [rankTwoQuadData, mutatedPolynomial_self, reverse_quadPoly]

/-- In rank two with exchange matrix `!![0, 2; -1, 0]` and degrees `(1, 2)` over the normalized
system of `ℚ≥0ˣ`, six alternating mutations starting from `H₀ = (1 + 2T)/3` and
`H₁ = (1 + 4T + 3T²)/8` return the exact initial exchange data. -/
example :
    let d := rankTwoQuadData true (nnratUnit 2)
      (nnratUnit (1 / 8)) (nnratUnit (1 / 2)) (nnratUnit (3 / 8))
    d.mutationWord (CoefficientSystem.normalized (1 : ℚ≥0ˣ →* ℚˣ)) [0, 1, 0, 1, 0, 1] = d := by
  have heq {pos : Bool} {y₁ y₂ a₁ a₂ b₁ b₂ c₁ c₂ : ℚ≥0ˣ}
      (hy : (y₁ : ℚ≥0) = y₂) (ha : (a₁ : ℚ≥0) = a₂) (hb : (b₁ : ℚ≥0) = b₂)
      (hc : (c₁ : ℚ≥0) = c₂) :
      rankTwoQuadData pos y₁ a₁ b₁ c₁ = rankTwoQuadData pos y₂ a₂ b₂ c₂ := by
    rw [Units.ext hy, Units.ext ha, Units.ext hb, Units.ext hc]
  dsimp only
  rw [mutationWord_cons, rankTwoQuadData_mutation_zero,
    heq (y₂ := nnratUnit (1 / 2)) (a₂ := nnratUnit (1 / 5))
      (b₂ := nnratUnit (8 / 15)) (c₂ := nnratUnit (4 / 15))
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
    mutationWord_cons, rankTwoQuadData_mutation_one,
    heq (y₂ := nnratUnit (2 / 15)) (a₂ := nnratUnit (4 / 15))
      (b₂ := nnratUnit (8 / 15)) (c₂ := nnratUnit (1 / 5))
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
    mutationWord_cons, rankTwoQuadData_mutation_zero,
    heq (y₂ := nnratUnit (15 / 2)) (a₂ := nnratUnit (289 / 360))
      (b₂ := nnratUnit (17 / 90)) (c₂ := nnratUnit (1 / 120))
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
    mutationWord_cons, rankTwoQuadData_mutation_one,
    heq (y₂ := nnratUnit (1 / 16)) (a₂ := nnratUnit (1 / 120))
      (b₂ := nnratUnit (17 / 90)) (c₂ := nnratUnit (289 / 360))
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
    mutationWord_cons, rankTwoQuadData_mutation_zero,
    heq (y₂ := nnratUnit 16) (a₂ := nnratUnit (3 / 8))
      (b₂ := nnratUnit (1 / 2)) (c₂ := nnratUnit (1 / 8))
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
      (by norm_num [nnratUnit]) (by norm_num [nnratUnit]),
    mutationWord_cons, rankTwoQuadData_mutation_one, mutationWord_nil]
  exact heq (by norm_num [nnratUnit]) (by norm_num [nnratUnit])
    (by norm_num [nnratUnit]) (by norm_num [nnratUnit])

end Examples

end TauCeti.ExchangeData
