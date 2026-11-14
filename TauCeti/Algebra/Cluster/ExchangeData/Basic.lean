/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSystem.Hom
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.NNRat
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exchange data and polynomial state mutation

*Exchange data* combine an extended exchange matrix `B` along `row : K ↪ I` with a family of
exchange polynomials `H_k` (`k ∈ K`) over `𝕂` whose positive degrees `r_k` divide the respective
columns of `B`. This single structure serves as the combinatorial and coefficient state of a seed
across all coefficient systems:

* for `CoefficientSystem.trivial R`, mutation of exchange data is unnormalized polynomial mutation;
* when every `H_k` is `ExchangePolynomial.binary` (`1 + T`), mutation reduces to ordinary binary
  matrix mutation;
* for `CoefficientSystem.ofSemifield φ`, mutation reverses `H_k`, dilates every other polynomial
  `H_j` by `κ_{kj} = h_{k,r_k}^{(b_{kj}/r_j)⁺} h_{k,0}^{-(b_{kj}/r_j)⁻}`, and normalizes the result
  so its coefficient sum remains `1`.

No finiteness hypothesis on `I` or `K` is needed for exchange data, their mutations, or their word
actions.

## Main definitions

* `TauCeti.ExchangeData 𝕂 row`: an extended exchange matrix together with exchange polynomials whose
  degrees divide the columns.
* `TauCeti.ExchangeData.dividedColumn`: the exact integer quotient `β_k i = b_{ik} / r_k`.
* `TauCeti.ExchangeData.mutatedPolynomial` and `TauCeti.ExchangeData.mutation`: single-step state
  mutation with respect to a `CoefficientSystem`.
* `TauCeti.ExchangeData.mutationWord`: left-fold action of a finite word of mutable directions.
* `TauCeti.ExchangeData.IsNormalized`, `TauCeti.ExchangeData.IsBinary`,
  `TauCeti.ExchangeData.IsEndpointOne`: normalized, binary, and endpoint-one state predicates.
* `TauCeti.ExchangeData.valueAtOne`: the scalar value `H_k(1) = ∑_l φ(h_{k,l}) ∈ R`.
* `TauCeti.ExchangeData.map` and `TauCeti.ExchangeData.reindex`: coefficient transport and index
  relabelling.

## Main results

* `TauCeti.ExchangeData.IsNormalized.mutation`: mutation preserves normalized states.
* `TauCeti.ExchangeData.mutation_mutation`: mutation in any fixed direction is an involution on
  normalized exchange data (and unconditionally for `CoefficientSystem.trivial R`).
* `TauCeti.ExchangeData.valueAtOne_mutation_of_column_eq_zero`: zero columns stay zero under
  mutation and preserve `H_j(1)` on normalized states.
* `TauCeti.ExchangeData.map_mutation` and `TauCeti.ExchangeData.mutation_reindex`: homomorphisms of
  coefficient systems and index equivalences commute with mutation and mutation words.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  Definition 2.1 and §5, for binomial propagation and semifield normalization.
* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014 (2014), (2.5), for polynomial
  exchange propagation.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  §2, for normalized mutation of higher-degree exchange polynomials.
-/

public section

namespace TauCeti

/-- *Exchange data* over `𝕂` along the mutable row embedding `row : K ↪ I`: an extended exchange
matrix together with an exchange polynomial in each mutable direction whose formal degree divides
every entry of its column. -/
@[ext]
structure ExchangeData (𝕂 : Type*) [CommMonoidWithZero 𝕂] {I K : Type*} (row : K ↪ I) where
  /-- The extended exchange matrix with its principal-block symmetrizer. -/
  exchange : ExchangeMatrix row
  /-- The exchange polynomial attached to each mutable direction. -/
  polynomial : K → ExchangePolynomial 𝕂
  /-- Each polynomial's degree divides every entry of its column in the extended matrix. -/
  degree_dvd : ∀ i k, ((polynomial k).degree : ℤ) ∣ exchange.matrix i k

namespace ExchangeData

section Basic

variable {𝕂 : Type*} [CommMonoidWithZero 𝕂] {R : Type*} [CommSemiring R]
  {I K : Type*} {row : K ↪ I}

/-- The divided column `β_k i = b_{ik} / r_k`, using exact integer division by
`(polynomial k).degree`. -/
def dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) : ℤ :=
  d.exchange.matrix i k / ((d.polynomial k).degree : ℤ)

theorem dividedColumn_def (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = d.exchange.matrix i k / ((d.polynomial k).degree : ℤ) :=
  (rfl)

theorem degree_pos_int (d : ExchangeData 𝕂 row) (k : K) :
    (0 : ℤ) < (d.polynomial k).degree :=
  Nat.cast_pos.mpr (d.polynomial k).degree_pos

theorem degree_ne_zero_int (d : ExchangeData 𝕂 row) (k : K) :
    ((d.polynomial k).degree : ℤ) ≠ 0 :=
  (d.degree_pos_int k).ne'

@[simp]
theorem mul_dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    ((d.polynomial k).degree : ℤ) * d.dividedColumn k i = d.exchange.matrix i k :=
  Int.mul_ediv_cancel' (d.degree_dvd i k)

theorem dividedColumn_mul (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i * ((d.polynomial k).degree : ℤ) = d.exchange.matrix i k :=
  Int.ediv_mul_cancel (d.degree_dvd i k)

@[simp]
theorem dividedColumn_row_self (d : ExchangeData 𝕂 row) (k : K) :
    d.dividedColumn k (row k) = 0 := by
  simp [dividedColumn_def]

@[simp]
theorem dividedColumn_eq_zero_iff (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = 0 ↔ d.exchange.matrix i k = 0 := by
  rw [← mul_right_inj' (d.degree_ne_zero_int k), mul_dividedColumn, mul_zero]

theorem dividedColumn_row_eq_zero_iff (d : ExchangeData 𝕂 row) (i j : K) :
    d.dividedColumn j (row i) = 0 ↔ d.dividedColumn i (row j) = 0 := by
  simp only [dividedColumn_eq_zero_iff]
  exact d.exchange.isSkewSymmetrizer.apply_eq_zero_iff

/-- All exchange polynomials of `d` have normalizer `1` with respect to `c`. -/
def IsNormalized (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, c.normalizer (d.polynomial k) = 1

theorem isNormalized_def {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row} :
    d.IsNormalized c ↔ ∀ k, c.normalizer (d.polynomial k) = 1 :=
  Iff.rfl

theorem isNormalized_iff {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row} :
    d.IsNormalized c ↔ ∀ k, c.IsNormalized (d.polynomial k) :=
  forall_congr' fun _ ↦ c.isNormalized_iff.symm

protected theorem IsNormalized.apply {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) : c.IsNormalized (d.polynomial k) :=
  c.isNormalized_iff.mpr (hd k)

@[simp]
theorem isNormalized_trivial (d : ExchangeData R row) :
    d.IsNormalized (CoefficientSystem.trivial R) :=
  fun k ↦ CoefficientSystem.trivial_normalizer (d.polynomial k)

/-- Canonical binary exchange data attached to an extended exchange matrix `B`, carrying
`ExchangePolynomial.binary` (`1 + T`) in every mutable direction. -/
def binary (B : ExchangeMatrix row) : ExchangeData 𝕂 row where
  exchange := B
  polynomial _ := ExchangePolynomial.binary
  degree_dvd _ _ := by simp

@[simp]
theorem binary_exchange (B : ExchangeMatrix row) : (binary (𝕂 := 𝕂) B).exchange = B :=
  (rfl)

@[simp]
theorem binary_polynomial (B : ExchangeMatrix row) (k : K) :
    (binary (𝕂 := 𝕂) B).polynomial k = ExchangePolynomial.binary :=
  (rfl)

/-- Binary exchange data: `H_k = 1 + T` (`ExchangePolynomial.binary`) in every direction. -/
def IsBinary (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, d.polynomial k = ExchangePolynomial.binary

theorem isBinary_iff {d : ExchangeData 𝕂 row} :
    d.IsBinary ↔ ∀ k, d.polynomial k = ExchangePolynomial.binary :=
  Iff.rfl

@[simp]
theorem isBinary_binary (B : ExchangeMatrix row) : (binary (𝕂 := 𝕂) B).IsBinary :=
  fun _ ↦ rfl

/-- Endpoint-one exchange data: `h_{k,0} = 1` and `h_{k,r_k} = 1` in every direction. -/
def IsEndpointOne (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, (d.polynomial k).IsEndpointOne

theorem isEndpointOne_iff {d : ExchangeData 𝕂 row} :
    d.IsEndpointOne ↔ ∀ k, (d.polynomial k).IsEndpointOne :=
  Iff.rfl

protected theorem IsBinary.isEndpointOne {d : ExchangeData 𝕂 row} (hd : d.IsBinary) :
    d.IsEndpointOne := fun k ↦ by
  rw [hd k]
  exact ExchangePolynomial.isEndpointOne_binary

/-- The value `H_k(1) = ∑_l φ(h_{k,l})` of the `k`-th exchange polynomial in the scalar
semiring `R`. -/
def valueAtOne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) : R :=
  ∑ l, c.toScalar ((d.polynomial k).coeff l)

theorem valueAtOne_def (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.valueAtOne c k = ∑ l, c.toScalar ((d.polynomial k).coeff l) :=
  (rfl)

protected theorem IsBinary.valueAtOne {d : ExchangeData 𝕂 row} (hd : d.IsBinary)
    (c : CoefficientSystem 𝕂 R) (k : K) : d.valueAtOne c k = 2 := by
  rw [valueAtOne_def, hd k]
  let e : Fin ((ExchangePolynomial.binary : ExchangePolynomial 𝕂).degree + 1) ≃ Fin 2 :=
    finCongr (by simp)
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_two]
  simp [one_add_one_eq_two]

end Basic

/-! ### Mutated polynomials and state mutation -/

section MutatedPolynomial

variable {𝕂 : Type*} [CommMonoidWithZero 𝕂] {R : Type*} [CommSemiring R]
  {I K : Type*} [DecidableEq K] {row : K ↪ I}

/-- The exchange polynomials after mutation in direction `k`: reverse `H_k`, and for `j ≠ k` dilate
`H_j` by `(H_k).dilationFactor (d.dividedColumn j (row k))` and normalize with `c`. -/
noncomputable def mutatedPolynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) : ExchangePolynomial 𝕂 :=
  if j = k then (d.polynomial k).reverse
  else c.normalize ((d.polynomial j).dilate
    ((d.polynomial k).dilationFactor (d.dividedColumn j (row k))))

theorem mutatedPolynomial_def (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) :
    d.mutatedPolynomial c k j =
      if j = k then (d.polynomial k).reverse
      else c.normalize ((d.polynomial j).dilate
        ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))) :=
  (rfl)

@[simp]
theorem mutatedPolynomial_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.mutatedPolynomial c k k = (d.polynomial k).reverse := by
  simp [mutatedPolynomial]

theorem mutatedPolynomial_of_ne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    {k j : K} (hj : j ≠ k) :
    d.mutatedPolynomial c k j =
      c.normalize ((d.polynomial j).dilate
        ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))) := by
  simp [mutatedPolynomial, hj]

@[simp]
theorem degree_mutatedPolynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k j : K) :
    (d.mutatedPolynomial c k j).degree = (d.polynomial j).degree := by
  by_cases hj : j = k
  · subst hj
    simp
  · simp [mutatedPolynomial_of_ne c d hj]

theorem coeff_mutatedPolynomial_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) (l : Fin ((d.mutatedPolynomial c k k).degree + 1)) :
    (d.mutatedPolynomial c k k).coeff l =
      (d.polynomial k).coeff (l.cast (by simp)).rev := by
  rw [ExchangePolynomial.coeff_eq_of_eq (mutatedPolynomial_self c d k) l,
    ExchangePolynomial.reverse_coeff]
  rfl

theorem coeff_mutatedPolynomial_of_ne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    {k j : K} (hj : j ≠ k) (l : Fin ((d.mutatedPolynomial c k j).degree + 1)) :
    (d.mutatedPolynomial c k j).coeff l =
      let κ := (d.polynomial k).dilationFactor (d.dividedColumn j (row k))
      (c.normalizer ((d.polynomial j).dilate κ) : 𝕂) *
        ((κ : 𝕂) ^ l.val * (d.polynomial j).coeff (l.cast (by simp))) := by
  rw [ExchangePolynomial.coeff_eq_of_eq (mutatedPolynomial_of_ne c d hj) l]
  simp [mul_comm ((d.polynomial j).coeff _)]

/-- Coordinate formula for mutated exchange polynomials in the normalized coefficient system of a
semifield with trivial additive units. -/
theorem coeff_mutatedPolynomial_ofSemifield_of_ne {F : Type*} [Semifield F]
    [Subsingleton (AddUnits F)] (φ : F →*₀ R) (d : ExchangeData F row) {k j : K} (hj : j ≠ k)
    (l : Fin ((d.mutatedPolynomial (CoefficientSystem.ofSemifield φ) k j).degree + 1)) :
    (d.mutatedPolynomial (CoefficientSystem.ofSemifield φ) k j).coeff l =
      let κ : F :=
        (d.polynomial k).coeff (Fin.last (d.polynomial k).degree) ^ (d.dividedColumn j (row k))⁺ *
          (d.polynomial k).coeff 0 ^ (-(d.dividedColumn j (row k))⁻)
      (∑ m, κ ^ m.val * (d.polynomial j).coeff m)⁻¹ *
        (κ ^ l.val * (d.polynomial j).coeff (l.cast (by simp))) := by
  rw [coeff_mutatedPolynomial_of_ne _ d hj]
  simp only [CoefficientSystem.val_ofSemifield_normalizer,
    ExchangePolynomial.sum_dilate_coeff _ _ fun x ↦ x]
  have hκ : (((d.polynomial k).dilationFactor (d.dividedColumn j (row k)) : Fˣ) : F) =
      (d.polynomial k).coeff (Fin.last (d.polynomial k).degree) ^ (d.dividedColumn j (row k))⁺ *
        (d.polynomial k).coeff 0 ^ (-(d.dividedColumn j (row k))⁻) := by
    simp [ExchangePolynomial.dilationFactor_def]
  rw [hκ]

theorem mutatedPolynomial_of_matrix_row_eq_zero (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) {k j : K} (hj : j ≠ k) (h0 : d.exchange.matrix (row k) j = 0) :
    d.mutatedPolynomial c k j = c.normalize (d.polynomial j) := by
  have hb : d.dividedColumn j (row k) = 0 := (d.dividedColumn_eq_zero_iff j (row k)).mpr h0
  simp [mutatedPolynomial_of_ne c d hj, hb]

theorem mutatedPolynomial_of_ne_of_isEndpointOne {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} {k j : K} (hj : j ≠ k) (hk : (d.polynomial k).IsEndpointOne)
    (hnorm : c.IsNormalized (d.polynomial j)) :
    d.mutatedPolynomial c k j = d.polynomial j := by
  rw [mutatedPolynomial_of_ne c d hj, hk.dilationFactor, ExchangePolynomial.dilate_one,
    hnorm.normalize_eq]

end MutatedPolynomial

section Mutation

variable {𝕂 : Type*} [CommMonoidWithZero 𝕂] {R : Type*} [CommSemiring R]
  {I K : Type*} [DecidableEq I] [DecidableEq K] {row : K ↪ I}

/-- Mutate exchange data in direction `k` with respect to the coefficient system `c`: mutate the
extended exchange matrix and update the exchange polynomials via `mutatedPolynomial`. -/
noncomputable def mutation (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    ExchangeData 𝕂 row where
  exchange := d.exchange.mutation k
  polynomial := d.mutatedPolynomial c k
  degree_dvd i j := by
    rw [degree_mutatedPolynomial, ExchangeMatrix.mutation_matrix]
    exact dvd_matrixMutation (fun a ↦ d.degree_dvd a j) k i

@[simp]
theorem mutation_exchange (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchange = d.exchange.mutation k :=
  (rfl)

@[simp]
theorem mutation_polynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).polynomial = d.mutatedPolynomial c k :=
  (rfl)

/-- Exact mutation formula for the divided columns `β_j i = b_{ij} / r_j`. -/
theorem dividedColumn_mutation (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) (i : I) :
    (d.mutation c k).dividedColumn j i =
      if i = row k ∨ j = k then -d.dividedColumn j i
      else d.dividedColumn j i +
        (d.polynomial k).degree * (d.dividedColumn k i)⁺ * (d.dividedColumn j (row k))⁺ -
        (d.polynomial k).degree * (d.dividedColumn k i)⁻ * (d.dividedColumn j (row k))⁻ := by
  simpa only [dividedColumn_def, mutation_exchange, ExchangeMatrix.mutation_matrix,
    mutation_polynomial, degree_mutatedPolynomial] using
    matrixMutation_ediv_apply (row := row) (B := d.exchange.matrix)
      (fun m ↦ ((d.polynomial m).degree : ℤ)) d.degree_pos_int d.degree_dvd k i j

@[simp]
theorem dividedColumn_mutation_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) (i : I) :
    (d.mutation c k).dividedColumn k i = -d.dividedColumn k i := by
  simp [dividedColumn_mutation]

@[simp]
theorem dividedColumn_mutation_row (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) :
    (d.mutation c k).dividedColumn j (row k) = -d.dividedColumn j (row k) := by
  simp [dividedColumn_mutation]

theorem dividedColumn_mutation_of_ne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    {k j : K} {i : I} (hi : i ≠ row k) (hj : j ≠ k) :
    (d.mutation c k).dividedColumn j i =
      d.dividedColumn j i +
        (d.polynomial k).degree * (d.dividedColumn k i)⁺ * (d.dividedColumn j (row k))⁺ -
        (d.polynomial k).degree * (d.dividedColumn k i)⁻ * (d.dividedColumn j (row k))⁻ := by
  simp [dividedColumn_mutation, hi, hj]

/-- Mutation preserves normalized exchange data. -/
protected theorem IsNormalized.mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) : (d.mutation c k).IsNormalized c := by
  intro j
  by_cases hj : j = k
  · subst hj
    simpa using hd j
  · simp [mutatedPolynomial_of_ne c d hj]

/-- **Involutivity of state mutation**: mutating normalized exchange data twice in the same
direction recovers the original state. -/
theorem mutation_mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) :
    (d.mutation c k).mutation c k = d := by
  ext : 1
  · simp
  · funext j
    by_cases hj : j = k
    · subst hj
      simp
    · rw [mutation_polynomial, mutatedPolynomial_of_ne c (d.mutation c k) hj]
      simp only [mutation_polynomial, mutatedPolynomial_self, dividedColumn_mutation_row,
        ExchangePolynomial.dilationFactor_reverse, neg_neg, mutatedPolynomial_of_ne c d hj]
      set κ := (d.polynomial k).dilationFactor (d.dividedColumn j (row k))
      rw [c.normalize_def ((d.polynomial j).dilate κ), ExchangePolynomial.scale_dilate,
        ExchangePolynomial.dilate_dilate, mul_inv_cancel, ExchangePolynomial.dilate_one,
        c.normalize_scale_normalizer, (hd.apply j).normalize_eq]

@[simp]
theorem mutation_mutation_trivial (d : ExchangeData R row) (k : K) :
    (d.mutation (CoefficientSystem.trivial R) k).mutation (CoefficientSystem.trivial R) k = d :=
  mutation_mutation d.isNormalized_trivial k

theorem mutation_involutive_trivial (k : K) :
    Function.Involutive fun d : ExchangeData R row ↦ d.mutation (CoefficientSystem.trivial R) k :=
  fun d ↦ d.mutation_mutation_trivial k

/-! ### Zero columns, endpoint-one data, and binary data -/

theorem mutation_column_eq_zero_iff (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) :
    (∀ i, (d.mutation c k).exchange.matrix i j = 0) ↔ ∀ i, d.exchange.matrix i j = 0 := by
  simp only [mutation_exchange, ExchangeMatrix.mutation_matrix]
  exact matrixMutation_column_eq_zero_iff k

@[simp]
theorem valueAtOne_mutation_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).valueAtOne c k = d.valueAtOne c k := by
  have hp : (d.mutation c k).polynomial k = (d.polynomial k).reverse := by simp
  rw [valueAtOne_def, valueAtOne_def, hp]
  exact (d.polynomial k).sum_reverse_coeff c.toScalar

theorem valueAtOne_mutation_of_matrix_row_eq_zero {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} {k j : K} (hnorm : c.IsNormalized (d.polynomial j))
    (h0 : d.exchange.matrix (row k) j = 0) :
    (d.mutation c k).valueAtOne c j = d.valueAtOne c j := by
  by_cases hj : j = k
  · subst hj
    exact d.valueAtOne_mutation_self c j
  · have hp : (d.mutation c k).polynomial j = d.polynomial j := by
      rw [mutation_polynomial, d.mutatedPolynomial_of_matrix_row_eq_zero c hj h0,
        hnorm.normalize_eq]
    rw [valueAtOne_def, valueAtOne_def, hp]

/-- On normalized exchange data, every zero column keeps the same scalar value `H_j(1)` after any
mutation. -/
theorem valueAtOne_mutation_of_column_eq_zero {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) {j : K}
    (hcol : ∀ i, d.exchange.matrix i j = 0) (k : K) :
    (d.mutation c k).valueAtOne c j = d.valueAtOne c j :=
  valueAtOne_mutation_of_matrix_row_eq_zero (hd.apply j) (hcol (row k))

protected theorem IsEndpointOne.mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsEndpointOne) (hnorm : d.IsNormalized c) (k : K) :
    (d.mutation c k).IsEndpointOne := by
  intro j
  by_cases hj : j = k
  · subst hj
    simpa using (hd j).reverse
  · rw [mutation_polynomial, mutatedPolynomial_of_ne_of_isEndpointOne hj (hd k) (hnorm.apply j)]
    exact hd j

protected theorem IsEndpointOne.mutation_trivial {d : ExchangeData R row}
    (hd : d.IsEndpointOne) (k : K) :
    (d.mutation (CoefficientSystem.trivial R) k).IsEndpointOne :=
  hd.mutation d.isNormalized_trivial k

protected theorem IsBinary.mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsBinary) (hc : c.IsNormalized ExchangePolynomial.binary) (k : K) :
    (d.mutation c k).IsBinary := by
  intro j
  by_cases hj : j = k
  · subst hj
    simp [hd j]
  · have hnorm : c.IsNormalized (d.polynomial j) := by rwa [hd j]
    rw [mutation_polynomial,
      mutatedPolynomial_of_ne_of_isEndpointOne hj (hd.isEndpointOne k) hnorm, hd j]

protected theorem IsBinary.mutation_trivial {d : ExchangeData R row} (hd : d.IsBinary) (k : K) :
    (d.mutation (CoefficientSystem.trivial R) k).IsBinary :=
  hd.mutation (CoefficientSystem.isNormalized_trivial _) k

/-- When `1 + T` is normalized in `c`, state mutation on `binary B` reduces to ordinary exchange
matrix mutation. -/
theorem binary_mutation {c : CoefficientSystem 𝕂 R}
    (hc : c.IsNormalized ExchangePolynomial.binary) (B : ExchangeMatrix row) (k : K) :
    (binary (𝕂 := 𝕂) B).mutation c k = binary (B.mutation k) := by
  ext : 1
  · rfl
  · funext j
    exact ((isBinary_binary (𝕂 := 𝕂) B).mutation hc k) j

@[simp]
theorem binary_mutation_trivial (B : ExchangeMatrix row) (k : K) :
    (binary (𝕂 := R) B).mutation (CoefficientSystem.trivial R) k = binary (B.mutation k) :=
  binary_mutation (CoefficientSystem.isNormalized_trivial _) B k

/-! ### Finite mutation words -/

/-- Apply a finite sequence of mutations in reading order. -/
noncomputable def mutationWord (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) : ExchangeData 𝕂 row :=
  w.foldl (fun s k ↦ s.mutation c k) d

theorem mutationWord_eq_foldl (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    d.mutationWord c w = w.foldl (fun s k ↦ s.mutation c k) d :=
  (rfl)

@[simp]
theorem mutationWord_nil (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) :
    d.mutationWord c [] = d :=
  (rfl)

@[simp]
theorem mutationWord_cons (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) (w : List K) :
    d.mutationWord c (k :: w) = (d.mutation c k).mutationWord c w :=
  (rfl)

@[simp]
theorem mutationWord_append (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (u v : List K) :
    d.mutationWord c (u ++ v) = (d.mutationWord c u).mutationWord c v :=
  List.foldl_append

@[simp]
theorem mutationWord_exchange (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    (d.mutationWord c w).exchange = d.exchange.mutationWord w := by
  rw [mutationWord_eq_foldl, ExchangeMatrix.mutationWord_eq_foldl]
  exact (List.foldl_hom (fun s : ExchangeData 𝕂 row ↦ s.exchange)
    (fun s k ↦ (s.mutation_exchange c k).symm)).symm

@[simp]
theorem degree_mutationWord (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) (j : K) :
    ((d.mutationWord c w).polynomial j).degree = (d.polynomial j).degree := by
  induction w generalizing d with
  | nil => rfl
  | cons k _w ih => simpa using ih (d.mutation c k)

theorem mutationWord_column_eq_zero_iff (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) (j : K) :
    (∀ i, (d.mutationWord c w).exchange.matrix i j = 0) ↔ ∀ i, d.exchange.matrix i j = 0 := by
  simp [ExchangeMatrix.mutationWord_matrix]

protected theorem IsNormalized.mutationWord {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (w : List K) : (d.mutationWord c w).IsNormalized c := by
  induction w generalizing d with
  | nil => exact hd
  | cons k _w ih => exact ih (hd.mutation k)

private noncomputable def normalizedMutation (c : CoefficientSystem 𝕂 R)
    (s : {d : ExchangeData 𝕂 row // d.IsNormalized c}) (k : K) :
    {d : ExchangeData 𝕂 row // d.IsNormalized c} :=
  ⟨s.val.mutation c k, s.prop.mutation k⟩

private theorem normalizedMutation_involutive (c : CoefficientSystem 𝕂 R) (k : K) :
    Function.Involutive (fun s ↦ normalizedMutation (row := row) c s k) := fun s ↦
  Subtype.ext (mutation_mutation s.prop k)

private theorem val_foldl_normalizedMutation (c : CoefficientSystem 𝕂 R)
    (s : {d : ExchangeData 𝕂 row // d.IsNormalized c}) (w : List K) :
    (w.foldl (normalizedMutation c) s).val = s.val.mutationWord c w := by
  induction w generalizing s with
  | nil => rfl
  | cons k _w ih => exact ih (normalizedMutation c s k)

/-- Reversing a mutation word undoes its action on normalized exchange data. -/
theorem mutationWord_mutationWord_reverse {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w).mutationWord c w.reverse = d := by
  have h := congrArg Subtype.val <|
    foldl_reverse_foldl_of_involutive (normalizedMutation (row := row) c)
      (normalizedMutation_involutive c) w ⟨d, hd⟩
  rwa [val_foldl_normalizedMutation, val_foldl_normalizedMutation] at h

theorem mutationWord_reverse_mutationWord {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w.reverse).mutationWord c w = d := by
  simpa using mutationWord_mutationWord_reverse hd w.reverse

theorem mutationWord_append_cons_cons_self {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (u v : List K) (k : K) :
    d.mutationWord c (u ++ k :: k :: v) = d.mutationWord c (u ++ v) := by
  have h := congrArg Subtype.val <|
    foldl_append_cons_cons_of_involutive (normalizedMutation (row := row) c)
      (normalizedMutation_involutive c k) u v ⟨d, hd⟩
  rwa [val_foldl_normalizedMutation, val_foldl_normalizedMutation] at h

@[simp]
theorem mutationWord_mutationWord_reverse_trivial (d : ExchangeData R row) (w : List K) :
    (d.mutationWord (CoefficientSystem.trivial R) w).mutationWord
      (CoefficientSystem.trivial R) w.reverse = d :=
  mutationWord_mutationWord_reverse d.isNormalized_trivial w

@[simp]
theorem mutationWord_reverse_mutationWord_trivial (d : ExchangeData R row) (w : List K) :
    (d.mutationWord (CoefficientSystem.trivial R) w.reverse).mutationWord
      (CoefficientSystem.trivial R) w = d :=
  mutationWord_reverse_mutationWord d.isNormalized_trivial w

theorem mutationWord_append_cons_cons_self_trivial (d : ExchangeData R row)
    (u v : List K) (k : K) :
    d.mutationWord (CoefficientSystem.trivial R) (u ++ k :: k :: v) =
      d.mutationWord (CoefficientSystem.trivial R) (u ++ v) :=
  mutationWord_append_cons_cons_self d.isNormalized_trivial u v k

end Mutation

/-! ### Functoriality along coefficient morphisms -/

section Map

variable {𝕂 𝕂' 𝕂'' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] {R : Type*} [CommSemiring R]
  {I K : Type*} {row : K ↪ I}

/-- Transport exchange data coefficientwise along any morphism of monoids with zero `ψ : 𝕂 →*₀ 𝕂'`.
In particular, `d.map c.toScalar` realizes the polynomials of `d` in the scalar system over `R`. -/
def map (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) : ExchangeData 𝕂' row where
  exchange := d.exchange
  polynomial k := (d.polynomial k).map ψ
  degree_dvd i k := by simpa using d.degree_dvd i k

@[simp]
theorem map_exchange (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) :
    (d.map ψ).exchange = d.exchange :=
  (rfl)

@[simp]
theorem map_polynomial (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ).polynomial k = (d.polynomial k).map ψ :=
  (rfl)

@[simp]
theorem map_id (d : ExchangeData 𝕂 row) : d.map (MonoidWithZeroHom.id 𝕂) = d := by
  ext : 1
  · rfl
  · funext k
    simp

@[simp]
theorem map_map (ψ' : 𝕂' →*₀ 𝕂'') (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) :
    (d.map ψ).map ψ' = d.map (ψ'.comp ψ) := by
  ext : 1
  · rfl
  · funext k
    simp

@[simp]
theorem dividedColumn_map (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    (d.map ψ).dividedColumn k i = d.dividedColumn k i := by
  simp [dividedColumn_def]

protected theorem IsNormalized.map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (f : c.Hom c') :
    (d.map f.toMonoidWithZeroHom).IsNormalized c' :=
  isNormalized_iff.mpr fun k ↦ by
    simpa only [map_polynomial] using (hd.apply k).map f

@[simp]
theorem valueAtOne_map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : c.Hom c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map f.toMonoidWithZeroHom).valueAtOne c' k = d.valueAtOne c k := by
  rw [valueAtOne_def, valueAtOne_def, map_polynomial,
    (d.polynomial k).sum_map_coeff f.toMonoidWithZeroHom c'.toScalar]
  exact Finset.sum_congr rfl fun l _ ↦ f.toScalar_apply _

/-- Homomorphisms of coefficient systems commute with state mutation. -/
@[simp]
theorem map_mutation [DecidableEq I] [DecidableEq K]
    {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : c.Hom c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).map f.toMonoidWithZeroHom =
      (d.map f.toMonoidWithZeroHom).mutation c' k := by
  ext : 1
  · rfl
  · funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [mutatedPolynomial_of_ne _ _ hj]

@[simp]
theorem map_mutationWord [DecidableEq I] [DecidableEq K]
    {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : c.Hom c') (d : ExchangeData 𝕂 row) (w : List K) :
    (d.mutationWord c w).map f.toMonoidWithZeroHom =
      (d.map f.toMonoidWithZeroHom).mutationWord c' w :=
  (List.foldl_hom (fun s : ExchangeData 𝕂 row ↦ s.map f.toMonoidWithZeroHom)
    (fun s k ↦ (s.map_mutation f k).symm)).symm

end Map

/-! ### Reindexing -/

section Reindex

variable {𝕂 𝕂' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  {R : Type*} [CommSemiring R]
  {I I' I'' K K' K'' : Type*} {row : K ↪ I} {row' : K' ↪ I'} {row'' : K'' ↪ I''}

/-- Reindex exchange data along equivalences of the row and mutable index types commuting with the
mutable embeddings. -/
def reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    ExchangeData 𝕂 row ≃ ExchangeData 𝕂 row' where
  toFun d :=
    { exchange := ExchangeMatrix.reindex eI eK h d.exchange
      polynomial k' := d.polynomial (eK.symm k')
      degree_dvd i' k' := by simpa using d.degree_dvd (eI.symm i') (eK.symm k') }
  invFun d :=
    { exchange := (ExchangeMatrix.reindex eI eK h).symm d.exchange
      polynomial k := d.polynomial (eK k)
      degree_dvd i k := by simpa using d.degree_dvd (eI i) (eK k) }
  left_inv d := by
    ext : 1
    · exact (ExchangeMatrix.reindex eI eK h).symm_apply_apply d.exchange
    · funext k
      simp
  right_inv d := by
    ext : 1
    · exact (ExchangeMatrix.reindex eI eK h).apply_symm_apply d.exchange
    · funext k
      simp

@[simp]
theorem reindex_exchange (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).exchange = ExchangeMatrix.reindex eI eK h d.exchange :=
  (rfl)

@[simp]
theorem reindex_polynomial (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k' : K') :
    (reindex eI eK h d).polynomial k' = d.polynomial (eK.symm k') :=
  (rfl)

@[simp]
theorem reindex_symm (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex (𝕂 := 𝕂) eI eK h).symm =
      reindex eI.symm eK.symm (fun k' ↦ by simp [Equiv.symm_apply_eq, h]) := by
  ext d : 2
  · ext : 1 <;> simp [reindex]
  · funext k
    simp [reindex]

@[simp]
theorem reindex_refl (h : ∀ k, Equiv.refl I (row k) = row (Equiv.refl K k)) :
    reindex (𝕂 := 𝕂) (Equiv.refl I) (Equiv.refl K) h = Equiv.refl (ExchangeData 𝕂 row) := by
  ext d : 2
  · simp
  · funext k
    simp

theorem reindex_trans (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    (reindex (𝕂 := 𝕂) eI eK h).trans (reindex eI' eK' h') =
      reindex (eI.trans eI') (eK.trans eK') (fun k ↦ by
        rw [Equiv.trans_apply, Equiv.trans_apply, h, h']) := by
  ext d : 2
  · simp only [Equiv.trans_apply, reindex_exchange]
    exact congrArg (fun e ↦ e d.exchange) (ExchangeMatrix.reindex_trans eI eK h eI' eK' h')
  · funext k
    simp

@[simp]
theorem dividedColumn_reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k' : K') (i' : I') :
    (reindex eI eK h d).dividedColumn k' i' = d.dividedColumn (eK.symm k') (eI.symm i') := by
  simp [dividedColumn_def]

@[simp]
theorem isNormalized_reindex_iff (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).IsNormalized c ↔ d.IsNormalized c :=
  ⟨fun hd k ↦ by simpa using hd (eK k), fun hd k' ↦ hd (eK.symm k')⟩

@[simp]
theorem isBinary_reindex_iff (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).IsBinary ↔ d.IsBinary :=
  ⟨fun hd k ↦ by simpa using hd (eK k), fun hd k' ↦ hd (eK.symm k')⟩

@[simp]
theorem isEndpointOne_reindex_iff (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).IsEndpointOne ↔ d.IsEndpointOne :=
  ⟨fun hd k ↦ by simpa using hd (eK k), fun hd k' ↦ hd (eK.symm k')⟩

@[simp]
theorem valueAtOne_reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k' : K') :
    (reindex eI eK h d).valueAtOne c k' = d.valueAtOne c (eK.symm k') :=
  (rfl)

@[simp]
theorem map_reindex (ψ : 𝕂 →*₀ 𝕂') (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).map ψ = reindex eI eK h (d.map ψ) := by
  ext : 1 <;> rfl

/-- Reindexing commutes with state mutation. -/
theorem mutation_reindex [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (reindex eI eK h d).mutation c (eK k) = reindex eI eK h (d.mutation c k) := by
  ext : 1
  · simp only [mutation_exchange, reindex_exchange]
    exact d.exchange.mutation_reindex eI eK h k
  · funext j'
    by_cases hj : j' = eK k
    · subst hj
      simp
    · have hj' : eK.symm j' ≠ k := by simpa [Equiv.symm_apply_eq] using hj
      have hrow : eI.symm (row' (eK k)) = row k := Equiv.symm_apply_eq eI |>.mpr (h k).symm
      simp [mutatedPolynomial_of_ne _ _ hj, mutatedPolynomial_of_ne _ _ hj', hrow]

theorem reindex_mutationWord [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    reindex eI eK h (d.mutationWord c w) =
      (reindex eI eK h d).mutationWord c (w.map eK) := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (reindex eI eK h)
    (fun s k ↦ s.mutation_reindex eI eK h c k)).symm

end Reindex

/-! ### Checks -/

/-- For `H = 1 + T + T²` on a rank-one zero column over `𝔽₃` (`ZMod 3`), the value `H(1)` vanishes,
exhibiting an inadmissible zero column over a field. -/
example :
    let H : ExchangePolynomial (ZMod 3) :=
      { degree := 2
        degree_pos := by decide
        coeff := fun _ ↦ 1
        isUnit_coeff_zero := isUnit_one
        isUnit_coeff_last := isUnit_one }
    let d : ExchangeData (ZMod 3) (Function.Embedding.refl Unit) :=
      { exchange :=
          { matrix := 0
            symmetrizer := fun _ ↦ 1
            isSkewSymmetrizer := ⟨by decide, by decide⟩ }
        polynomial := fun _ ↦ H
        degree_dvd := fun _ _ ↦ dvd_zero _ }
    d.valueAtOne (CoefficientSystem.trivial (ZMod 3)) () = 0 := by
  intro H d
  rw [valueAtOne_def]
  simp only [d, H, CoefficientSystem.trivial_toScalar, MonoidWithZeroHom.id_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  decide

section B2PeriodicityExample

private abbrev mkB2Poly1 (a b : ℚ≥0) (ha : a ≠ 0) (hb : b ≠ 0) : ExchangePolynomial ℚ≥0 where
  degree := 1
  degree_pos := by decide
  coeff l := if l = 0 then a else b
  isUnit_coeff_zero := isUnit_iff_ne_zero.mpr (by simp [ha])
  isUnit_coeff_last := isUnit_iff_ne_zero.mpr (by simp [hb])

private abbrev mkB2Poly2 (a b g : ℚ≥0) (ha : a ≠ 0) (hg : g ≠ 0) : ExchangePolynomial ℚ≥0 where
  degree := 2
  degree_pos := by decide
  coeff l := if l = 0 then a else if l = 1 then b else g
  isUnit_coeff_zero := isUnit_iff_ne_zero.mpr (by simp [ha])
  isUnit_coeff_last := isUnit_iff_ne_zero.mpr (by simp [hg])

private abbrev mkB2State (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : (B.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2])
    (hdvd : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ B i k)
    (a₀ b₀ a₁ b₁ c₁ : ℚ≥0) (ha₀ : a₀ ≠ 0) (hb₀ : b₀ ≠ 0) (ha₁ : a₁ ≠ 0) (hc₁ : c₁ ≠ 0) :
    ExchangeData ℚ≥0 (Function.Embedding.refl (Fin 2)) where
  exchange := { matrix := B, symmetrizer := ![1, 2], isSkewSymmetrizer := hB }
  polynomial k := if k = 0 then mkB2Poly1 a₀ b₀ ha₀ hb₀ else mkB2Poly2 a₁ b₁ c₁ ha₁ hc₁
  degree_dvd i k := by fin_cases k <;> exact hdvd i _

private noncomputable def b2CoeffSystem : CoefficientSystem ℚ≥0 ℚ :=
  CoefficientSystem.ofSemifield NNRat.coeHom.toMonoidWithZeroHom

private theorem b2Step0 {B B' : Matrix (Fin 2) (Fin 2) ℤ}
    {a₀ b₀ a₁ b₁ c₁ a₀' b₀' a₁' b₁' c₁' : ℚ≥0} (κ : ℚ≥0)
    (hmat : ∀ i j : Fin 2, B' i j = matrixMutation (Function.Embedding.refl (Fin 2)) B 0 i j)
    (hκ : b₀ ^ (B 0 1 / 2)⁺ * a₀ ^ (-(B 0 1 / 2)⁻) = κ)
    (h0 : a₀' = b₀) (h1 : b₀' = a₀)
    (g0 : a₁' = (κ ^ 0 * a₁ + κ ^ 1 * b₁ + κ ^ 2 * c₁)⁻¹ * (κ ^ 0 * a₁))
    (g1 : b₁' = (κ ^ 0 * a₁ + κ ^ 1 * b₁ + κ ^ 2 * c₁)⁻¹ * (κ ^ 1 * b₁))
    (g2 : c₁' = (κ ^ 0 * a₁ + κ ^ 1 * b₁ + κ ^ 2 * c₁)⁻¹ * (κ ^ 2 * c₁))
    (hB : (B.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2] := by
      assumption)
    (hB' : (B'.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2] := by
      assumption)
    (hdvd : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ B i k := by assumption)
    (hdvd' : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ B' i k := by assumption)
    (ha₀ : a₀ ≠ 0 := by norm_num) (hb₀ : b₀ ≠ 0 := by norm_num)
    (ha₁ : a₁ ≠ 0 := by norm_num) (hc₁ : c₁ ≠ 0 := by norm_num)
    (ha₀' : a₀' ≠ 0 := by norm_num) (hb₀' : b₀' ≠ 0 := by norm_num)
    (ha₁' : a₁' ≠ 0 := by norm_num) (hc₁' : c₁' ≠ 0 := by norm_num) :
    (mkB2State B hB hdvd a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁).mutation b2CoeffSystem 0 =
      mkB2State B' hB' hdvd' a₀' b₀' a₁' b₁' c₁' ha₀' hb₀' ha₁' hc₁' := by
  let u := mkB2State B hB hdvd a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁
  symm
  ext : 1
  · rw [mutation_exchange]
    ext : 1
    · ext i j
      rw [ExchangeMatrix.mutation_matrix]
      exact hmat i j
    · rw [ExchangeMatrix.mutation_symmetrizer]
  · rw [funext_iff, Fin.forall_fin_two]
    constructor
    · rw [mutation_polynomial]
      refine ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_
      rw [coeff_mutatedPolynomial_self]
      fin_cases l
      · exact h0
      · exact h1
    · rw [mutation_polynomial]
      refine ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_
      rw [b2CoeffSystem, coeff_mutatedPolynomial_ofSemifield_of_ne _ u (by decide)]
      dsimp only
      have hdiv : u.dividedColumn 1 (Function.Embedding.refl (Fin 2) 0) = B 0 1 / 2 := rfl
      have hlast : (u.polynomial 0).coeff (Fin.last (u.polynomial 0).degree) = b₀ := rfl
      have hzero : (u.polynomial 0).coeff 0 = a₀ := rfl
      have hsum : ∑ m, κ ^ m.val * (u.polynomial 1).coeff m =
          κ ^ 0 * a₁ + κ ^ 1 * b₁ + κ ^ 2 * c₁ :=
        Fin.sum_univ_three fun m ↦ κ ^ m.val * (u.polynomial 1).coeff m
      rw [hdiv, hlast, hzero, hκ, hsum]
      fin_cases l
      · exact g0
      · exact g1
      · exact g2

private theorem b2Step1 {B B' : Matrix (Fin 2) (Fin 2) ℤ}
    {a₀ b₀ a₁ b₁ c₁ a₀' b₀' a₁' b₁' c₁' : ℚ≥0} (κ : ℚ≥0)
    (hmat : ∀ i j : Fin 2, B' i j = matrixMutation (Function.Embedding.refl (Fin 2)) B 1 i j)
    (hκ : c₁ ^ (B 1 0 / 1)⁺ * a₁ ^ (-(B 1 0 / 1)⁻) = κ)
    (h0 : a₀' = (κ ^ 0 * a₀ + κ ^ 1 * b₀)⁻¹ * (κ ^ 0 * a₀))
    (h1 : b₀' = (κ ^ 0 * a₀ + κ ^ 1 * b₀)⁻¹ * (κ ^ 1 * b₀))
    (g0 : a₁' = c₁) (g1 : b₁' = b₁) (g2 : c₁' = a₁)
    (hB : (B.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2] := by
      assumption)
    (hB' : (B'.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2] := by
      assumption)
    (hdvd : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ B i k := by assumption)
    (hdvd' : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ B' i k := by assumption)
    (ha₀ : a₀ ≠ 0 := by norm_num) (hb₀ : b₀ ≠ 0 := by norm_num)
    (ha₁ : a₁ ≠ 0 := by norm_num) (hc₁ : c₁ ≠ 0 := by norm_num)
    (ha₀' : a₀' ≠ 0 := by norm_num) (hb₀' : b₀' ≠ 0 := by norm_num)
    (ha₁' : a₁' ≠ 0 := by norm_num) (hc₁' : c₁' ≠ 0 := by norm_num) :
    (mkB2State B hB hdvd a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁).mutation b2CoeffSystem 1 =
      mkB2State B' hB' hdvd' a₀' b₀' a₁' b₁' c₁' ha₀' hb₀' ha₁' hc₁' := by
  let u := mkB2State B hB hdvd a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁
  symm
  ext : 1
  · rw [mutation_exchange]
    ext : 1
    · ext i j
      rw [ExchangeMatrix.mutation_matrix]
      exact hmat i j
    · rw [ExchangeMatrix.mutation_symmetrizer]
  · rw [funext_iff, Fin.forall_fin_two]
    constructor
    · rw [mutation_polynomial]
      refine ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_
      rw [b2CoeffSystem, coeff_mutatedPolynomial_ofSemifield_of_ne _ u (by decide)]
      dsimp only
      have hdiv : u.dividedColumn 0 (Function.Embedding.refl (Fin 2) 1) = B 1 0 / 1 := rfl
      have hlast : (u.polynomial 1).coeff (Fin.last (u.polynomial 1).degree) = c₁ := rfl
      have hzero : (u.polynomial 1).coeff 0 = a₁ := rfl
      have hsum : ∑ m, κ ^ m.val * (u.polynomial 0).coeff m = κ ^ 0 * a₀ + κ ^ 1 * b₀ :=
        Fin.sum_univ_two fun m ↦ κ ^ m.val * (u.polynomial 0).coeff m
      rw [hdiv, hlast, hzero, hκ, hsum]
      fin_cases l
      · exact h0
      · exact h1
    · rw [mutation_polynomial]
      refine ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_
      rw [coeff_mutatedPolynomial_self]
      fin_cases l
      · exact g0
      · exact g1
      · exact g2

/-- Six-step periodicity in type `B₂`/`C₂` with unequal polynomial degrees `(1, 2)` over `ℚ≥0`:
for `B = !![0, 2; -1, 0]`, `H₀(T) = (1 + 2T)/3`, and `H₁(T) = (1 + 4T + 3T²)/8` in the normalized
coefficient system of `ℚ≥0`, six alternating mutations `[0, 1, 0, 1, 0, 1]` return the exact
initial exchange data. -/
example :
    let c : CoefficientSystem ℚ≥0 ℚ :=
      CoefficientSystem.ofSemifield NNRat.coeHom.toMonoidWithZeroHom
    let H₀ : ExchangePolynomial ℚ≥0 :=
      { degree := 1
        degree_pos := by decide
        coeff := ![1 / 3, 2 / 3]
        isUnit_coeff_zero := isUnit_iff_ne_zero.mpr (by simp)
        isUnit_coeff_last := isUnit_iff_ne_zero.mpr
          (by simp only [Fin.last, Matrix.cons_val_succ', Matrix.cons_val_zero']; norm_num) }
    let H₁ : ExchangePolynomial ℚ≥0 :=
      { degree := 2
        degree_pos := by decide
        coeff := ![1 / 8, 4 / 8, 3 / 8]
        isUnit_coeff_zero := isUnit_iff_ne_zero.mpr (by simp)
        isUnit_coeff_last := isUnit_iff_ne_zero.mpr
          (by simp only [Fin.last, Matrix.cons_val_succ', Matrix.cons_val_zero']; norm_num) }
    let d : ExchangeData ℚ≥0 (Function.Embedding.refl (Fin 2)) :=
      { exchange :=
          { matrix := !![0, 2; -1, 0]
            symmetrizer := ![1, 2]
            isSkewSymmetrizer := ⟨by decide, by decide⟩ }
        polynomial := ![H₀, H₁]
        degree_dvd := by
          intro i k
          fin_cases i <;> fin_cases k <;> decide }
    d.mutationWord c [0, 1, 0, 1, 0, 1] = d := by
  intro c H₀ H₁ d
  let Bpos : Matrix (Fin 2) (Fin 2) ℤ := !![0, 2; -1, 0]
  let Bneg : Matrix (Fin 2) (Fin 2) ℤ := !![0, -2; 1, 0]
  have hBpos : (Bpos.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2] :=
    ⟨by decide, by decide⟩
  have hBneg : (Bneg.submatrix (Function.Embedding.refl (Fin 2)) id).IsSkewSymmetrizer ![1, 2] :=
    ⟨by decide, by decide⟩
  have hdvdPos : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ Bpos i k := by
    intro i k; fin_cases i <;> fin_cases k <;> decide
  have hdvdNeg : ∀ i k : Fin 2, ((if k = 0 then (1 : ℕ) else 2 : ℕ) : ℤ) ∣ Bneg i k := by
    intro i k; fin_cases i <;> fin_cases k <;> decide
  set s₀ := mkB2State Bpos hBpos hdvdPos (1 / 3) (2 / 3) (1 / 8) (4 / 8) (3 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd_eq : d = s₀ := by
    ext : 1
    · rfl
    · rw [funext_iff, Fin.forall_fin_two]
      exact ⟨ExchangePolynomial.ext rfl fun l ↦ by fin_cases l <;> rfl,
        ExchangePolynomial.ext rfl fun l ↦ by fin_cases l <;> rfl⟩
  have hc_eq : c = b2CoeffSystem := rfl
  rw [hd_eq, hc_eq]
  have hmatPos0 : ∀ i j : Fin 2,
      Bneg i j = matrixMutation (Function.Embedding.refl (Fin 2)) Bpos 0 i j := by
    rw [Fin.forall_fin_two]; refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;>
      simp [Bpos, Bneg, matrixMutation_apply]
  have hmatNeg0 : ∀ i j : Fin 2,
      Bpos i j = matrixMutation (Function.Embedding.refl (Fin 2)) Bneg 0 i j := by
    rw [Fin.forall_fin_two]; refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;>
      simp [Bpos, Bneg, matrixMutation_apply]
  have hmatPos1 : ∀ i j : Fin 2,
      Bneg i j = matrixMutation (Function.Embedding.refl (Fin 2)) Bpos 1 i j := by
    rw [Fin.forall_fin_two]; refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;>
      simp [Bpos, Bneg, matrixMutation_apply]
  have hmatNeg1 : ∀ i j : Fin 2,
      Bpos i j = matrixMutation (Function.Embedding.refl (Fin 2)) Bneg 1 i j := by
    rw [Fin.forall_fin_two]; refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;>
      simp [Bpos, Bneg, matrixMutation_apply]
  have hePos0 : (Bpos 0 1 / 2)⁺ = 1 ∧ -(Bpos 0 1 / 2)⁻ = 0 := by decide
  have heNeg0 : (Bneg 0 1 / 2)⁺ = 0 ∧ -(Bneg 0 1 / 2)⁻ = -1 := by decide
  have hePos1 : (Bpos 1 0 / 1)⁺ = 0 ∧ -(Bpos 1 0 / 1)⁻ = -1 := by decide
  have heNeg1 : (Bneg 1 0 / 1)⁺ = 1 ∧ -(Bneg 1 0 / 1)⁻ = 0 := by decide
  set s₁ := mkB2State Bneg hBneg hdvdNeg (2 / 3) (1 / 3) (3 / 15) (8 / 15) (4 / 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set s₂ := mkB2State Bpos hBpos hdvdPos (15 / 17) (2 / 17) (4 / 15) (8 / 15) (3 / 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set mid := mkB2State Bneg hBneg hdvdNeg (2 / 17) (15 / 17) (289 / 360) (68 / 360) (3 / 360)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set t₁ := mkB2State Bneg hBneg hdvdNeg (1 / 17) (16 / 17) (3 / 8) (4 / 8) (1 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set t₂ := mkB2State Bpos hBpos hdvdPos (16 / 17) (1 / 17) (3 / 360) (68 / 360) (289 / 360)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : s₀.IsNormalized b2CoeffSystem := by
    rw [isNormalized_iff, Fin.forall_fin_two, b2CoeffSystem]
    constructor
    · have hsum : ∑ l, (s₀.polynomial 0).coeff l = (1 / 3 : ℚ≥0) + 2 / 3 :=
        Fin.sum_univ_two fun l ↦ (s₀.polynomial 0).coeff l
      rw [CoefficientSystem.isNormalized_ofSemifield_iff, hsum]
      norm_num
    · have hsum : ∑ l, (s₀.polynomial 1).coeff l = (1 / 8 : ℚ≥0) + 4 / 8 + 3 / 8 :=
        Fin.sum_univ_three fun l ↦ (s₀.polynomial 1).coeff l
      rw [CoefficientSystem.isNormalized_ofSemifield_iff, hsum]
      norm_num
  have hs₁ : s₀.mutation b2CoeffSystem 0 = s₁ :=
    b2Step0 (2 / 3) hmatPos0 (by rw [hePos0.1, hePos0.2]; norm_num) rfl rfl
      (by norm_num) (by norm_num) (by norm_num)
  have hs₂ : s₁.mutation b2CoeffSystem 1 = s₂ :=
    b2Step1 (4 / 15) hmatNeg1 (by rw [heNeg1.1, heNeg1.2]; norm_num)
      (by norm_num) (by norm_num) rfl rfl rfl
  have hmid₁ : s₂.mutation b2CoeffSystem 0 = mid :=
    b2Step0 (2 / 17) hmatPos0 (by rw [hePos0.1, hePos0.2]; norm_num) rfl rfl
      (by norm_num) (by norm_num) (by norm_num)
  have ht₁ : s₀.mutation b2CoeffSystem 1 = t₁ :=
    b2Step1 8 hmatPos1 (by rw [hePos1.1, hePos1.2]; norm_num)
      (by norm_num) (by norm_num) rfl rfl rfl
  have ht₂ : t₁.mutation b2CoeffSystem 0 = t₂ :=
    b2Step0 17 hmatNeg0 (by rw [heNeg0.1, heNeg0.2]; norm_num) rfl rfl
      (by norm_num) (by norm_num) (by norm_num)
  have hmid₂ : t₂.mutation b2CoeffSystem 1 = mid :=
    b2Step1 120 hmatPos1 (by rw [hePos1.1, hePos1.2]; norm_num)
      (by norm_num) (by norm_num) rfl rfl rfl
  have hmid :
      s₀.mutationWord b2CoeffSystem [0, 1, 0] = s₀.mutationWord b2CoeffSystem [1, 0, 1] := by
    simp only [mutationWord_cons, mutationWord_nil, hs₁, hs₂, hmid₁, ht₁, ht₂, hmid₂]
  have hword :
      ([0, 1, 0, 1, 0, 1] : List (Fin 2)) = [0, 1, 0] ++ ([1, 0, 1] : List (Fin 2)).reverse :=
    rfl
  rw [hword, mutationWord_append, hmid]
  exact mutationWord_mutationWord_reverse hd [1, 0, 1]

end B2PeriodicityExample

end ExchangeData

end TauCeti
