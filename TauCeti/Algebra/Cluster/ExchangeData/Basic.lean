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

*Exchange data* combine an extended exchange matrix `B` along `row : K ↪ I` with exchange
polynomials `H_k` (`k ∈ K`) over `𝕂` whose positive degrees `r_k` divide the columns of `B`.
Mutation in direction `k` with respect to a `CoefficientSystem` mutates `B`, reverses `H_k`, and
dilates and normalizes every other `H_j` by `(H_k).dilationFactor (b_{kj} / r_j)`. On normalized
exchange data, state mutation is involutive and commutes with coefficient-system homomorphisms and
index equivalences, with no finiteness assumption on `I` or `K`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  Definition 2.1 and §5.
* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014 (2014), (2.5).
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  §2.
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
    d.dividedColumn k i = d.exchange.matrix i k / ((d.polynomial k).degree : ℤ) := (rfl)

theorem degree_pos_int (d : ExchangeData 𝕂 row) (k : K) : (0 : ℤ) < (d.polynomial k).degree :=
  Nat.cast_pos.mpr (d.polynomial k).degree_pos

theorem degree_ne_zero_int (d : ExchangeData 𝕂 row) (k : K) :
    ((d.polynomial k).degree : ℤ) ≠ 0 := (d.degree_pos_int k).ne'

@[simp]
theorem mul_dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    ((d.polynomial k).degree : ℤ) * d.dividedColumn k i = d.exchange.matrix i k :=
  Int.mul_ediv_cancel' (d.degree_dvd i k)

@[simp]
theorem dividedColumn_row_self (d : ExchangeData 𝕂 row) (k : K) :
    d.dividedColumn k (row k) = 0 := by simp [dividedColumn_def]

@[simp]
theorem dividedColumn_eq_zero_iff (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = 0 ↔ d.exchange.matrix i k = 0 := by
  rw [← mul_right_inj' (d.degree_ne_zero_int k), mul_dividedColumn, mul_zero]

/-- All exchange polynomials of `d` have normalizer `1` with respect to `c`. -/
def IsNormalized (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, c.normalizer (d.polynomial k) = 1

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

/-- Canonical binary exchange data attached to `B`, carrying `1 + T` in every direction. -/
def binary (B : ExchangeMatrix row) : ExchangeData 𝕂 row where
  exchange := B
  polynomial _ := ExchangePolynomial.binary
  degree_dvd _ _ := by simp

@[simp] theorem binary_exchange (B : ExchangeMatrix row) : (binary (𝕂 := 𝕂) B).exchange = B := (rfl)

@[simp]
theorem binary_polynomial (B : ExchangeMatrix row) (k : K) :
    (binary (𝕂 := 𝕂) B).polynomial k = ExchangePolynomial.binary := (rfl)

/-- Binary exchange data: `H_k = 1 + T` (`ExchangePolynomial.binary`) in every direction. -/
def IsBinary (d : ExchangeData 𝕂 row) : Prop := ∀ k, d.polynomial k = ExchangePolynomial.binary

@[simp]
theorem isBinary_binary (B : ExchangeMatrix row) : (binary (𝕂 := 𝕂) B).IsBinary := fun _ ↦ rfl

/-- The value `H_k(1) = ∑_l φ(h_{k,l})` of the `k`-th exchange polynomial in `R`. -/
def valueAtOne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) : R :=
  ∑ l, c.toScalar ((d.polynomial k).coeff l)

theorem valueAtOne_def (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.valueAtOne c k = ∑ l, c.toScalar ((d.polynomial k).coeff l) := (rfl)

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

@[simp]
theorem mutatedPolynomial_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.mutatedPolynomial c k k = (d.polynomial k).reverse := by simp [mutatedPolynomial]

theorem mutatedPolynomial_of_ne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    {k j : K} (hj : j ≠ k) :
    d.mutatedPolynomial c k j =
      c.normalize ((d.polynomial j).dilate
        ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))) := by
  simp [mutatedPolynomial, hj]

@[simp]
theorem degree_mutatedPolynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k j : K) :
    (d.mutatedPolynomial c k j).degree = (d.polynomial j).degree := by
  by_cases hj : j = k <;> simp [mutatedPolynomial, hj]

theorem coeff_mutatedPolynomial_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) (l : Fin ((d.mutatedPolynomial c k k).degree + 1)) :
    (d.mutatedPolynomial c k k).coeff l = (d.polynomial k).coeff (l.cast (by simp)).rev := by
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

/-- Coordinate formula for mutated exchange polynomials in `CoefficientSystem.ofSemifield φ`. -/
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
  simp [mutatedPolynomial_of_ne c d hj, (d.dividedColumn_eq_zero_iff j (row k)).mpr h0]

end MutatedPolynomial

section Mutation

variable {𝕂 : Type*} [CommMonoidWithZero 𝕂] {R : Type*} [CommSemiring R]
  {I K : Type*} [DecidableEq I] [DecidableEq K] {row : K ↪ I}

/-- Mutate exchange data in direction `k` with respect to the coefficient system `c`. -/
noncomputable def mutation (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    ExchangeData 𝕂 row where
  exchange := d.exchange.mutation k
  polynomial := d.mutatedPolynomial c k
  degree_dvd i j := by
    rw [degree_mutatedPolynomial, ExchangeMatrix.mutation_matrix]
    exact dvd_matrixMutation (fun a ↦ d.degree_dvd a j) k i

@[simp]
theorem mutation_exchange (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchange = d.exchange.mutation k := (rfl)

@[simp]
theorem mutation_polynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).polynomial = d.mutatedPolynomial c k := (rfl)

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
    (k : K) (i : I) : (d.mutation c k).dividedColumn k i = -d.dividedColumn k i := by
  simp [dividedColumn_mutation]

@[simp]
theorem dividedColumn_mutation_row (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) : (d.mutation c k).dividedColumn j (row k) = -d.dividedColumn j (row k) := by
  simp [dividedColumn_mutation]

/-- Mutation preserves normalized exchange data. -/
protected theorem IsNormalized.mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) : (d.mutation c k).IsNormalized c := fun j ↦ by
  by_cases hj : j = k
  · subst hj; simpa using hd j
  · simp [mutatedPolynomial_of_ne c d hj]

/-- **Involutivity of state mutation**: mutating normalized exchange data twice in the same
direction recovers the original state. -/
theorem mutation_mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) : (d.mutation c k).mutation c k = d := by
  ext : 1; · simp
  funext j
  by_cases hj : j = k
  · subst hj; simp
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

/-! ### Zero columns and binary data -/

theorem mutation_column_eq_zero_iff (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) :
    (∀ i, (d.mutation c k).exchange.matrix i j = 0) ↔ ∀ i, d.exchange.matrix i j = 0 := by
  simpa only [mutation_exchange, ExchangeMatrix.mutation_matrix] using
    matrixMutation_column_eq_zero_iff (row := row) (B := d.exchange.matrix) (j := j) k

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
  · exact hj ▸ d.valueAtOne_mutation_self c k
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

protected theorem IsBinary.mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsBinary) (hc : c.IsNormalized ExchangePolynomial.binary) (k : K) :
    (d.mutation c k).IsBinary := fun j ↦ by
  by_cases hj : j = k
  · subst hj; simp [hd j]
  · rw [mutation_polynomial, mutatedPolynomial_of_ne c d hj, hd k, hd j,
      ExchangePolynomial.dilationFactor_binary, ExchangePolynomial.dilate_one, hc.normalize_eq]

theorem binary_mutation {c : CoefficientSystem 𝕂 R}
    (hc : c.IsNormalized ExchangePolynomial.binary) (B : ExchangeMatrix row) (k : K) :
    (binary (𝕂 := 𝕂) B).mutation c k = binary (B.mutation k) := by
  ext : 1; · rfl
  exact funext ((isBinary_binary (𝕂 := 𝕂) B).mutation hc k)

/-! ### Finite mutation words -/

/-- Apply a finite sequence of mutations in reading order. -/
noncomputable def mutationWord (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) : ExchangeData 𝕂 row :=
  w.foldl (fun s k ↦ s.mutation c k) d

theorem mutationWord_eq_foldl (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    d.mutationWord c w = w.foldl (fun s k ↦ s.mutation c k) d := (rfl)

@[simp] theorem mutationWord_nil (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) :
    d.mutationWord c [] = d := (rfl)

@[simp]
theorem mutationWord_cons (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) (w : List K) : d.mutationWord c (k :: w) = (d.mutation c k).mutationWord c w := (rfl)

@[simp]
theorem mutationWord_append (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (u v : List K) :
    d.mutationWord c (u ++ v) = (d.mutationWord c u).mutationWord c v := List.foldl_append

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
  | cons k _ ih => simpa using ih (d.mutation c k)

protected theorem IsNormalized.mutationWord {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (w : List K) : (d.mutationWord c w).IsNormalized c := by
  induction w generalizing d with
  | nil => exact hd
  | cons k _ ih => exact ih (hd.mutation k)

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
  | cons k _ ih => exact ih (normalizedMutation c s k)

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

end Mutation

/-! ### Functoriality along coefficient morphisms -/

section Map

variable {𝕂 𝕂' 𝕂'' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] {R : Type*} [CommSemiring R]
  {I K : Type*} {row : K ↪ I}

/-- Transport exchange data coefficientwise along `ψ : 𝕂 →*₀ 𝕂'`. -/
def map (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) : ExchangeData 𝕂' row where
  exchange := d.exchange
  polynomial k := (d.polynomial k).map ψ
  degree_dvd i k := by simpa using d.degree_dvd i k

@[simp] theorem map_exchange (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) :
    (d.map ψ).exchange = d.exchange := (rfl)

@[simp] theorem map_polynomial (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ).polynomial k = (d.polynomial k).map ψ := (rfl)

@[simp] theorem map_id (d : ExchangeData 𝕂 row) : d.map (MonoidWithZeroHom.id 𝕂) = d := by
  ext : 1; · rfl
  funext k; simp

@[simp]
theorem map_map (ψ' : 𝕂' →*₀ 𝕂'') (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) :
    (d.map ψ).map ψ' = d.map (ψ'.comp ψ) := by
  ext : 1; · rfl
  funext k; simp

@[simp]
theorem dividedColumn_map (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    (d.map ψ).dividedColumn k i = d.dividedColumn k i := by simp [dividedColumn_def]

protected theorem IsNormalized.map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (f : c.Hom c') :
    (d.map f.toMonoidWithZeroHom).IsNormalized c' :=
  isNormalized_iff.mpr fun k ↦ by simpa only [map_polynomial] using (hd.apply k).map f

@[simp]
theorem valueAtOne_map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : c.Hom c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map f.toMonoidWithZeroHom).valueAtOne c' k = d.valueAtOne c k := by
  rw [valueAtOne_def, valueAtOne_def, map_polynomial,
    (d.polynomial k).sum_map_coeff f.toMonoidWithZeroHom c'.toScalar]
  exact Finset.sum_congr rfl fun _ _ ↦ f.toScalar_apply _

/-- Homomorphisms of coefficient systems commute with state mutation. -/
@[simp]
theorem map_mutation [DecidableEq I] [DecidableEq K]
    {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : c.Hom c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).map f.toMonoidWithZeroHom =
      (d.map f.toMonoidWithZeroHom).mutation c' k := by
  ext : 1; · rfl
  funext j
  by_cases hj : j = k
  · subst hj; simp
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

/-- Reindex exchange data along equivalences commuting with the mutable embeddings. -/
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
    · funext k; simp
  right_inv d := by
    ext : 1
    · exact (ExchangeMatrix.reindex eI eK h).apply_symm_apply d.exchange
    · funext k; simp

@[simp]
theorem reindex_exchange (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).exchange = ExchangeMatrix.reindex eI eK h d.exchange := (rfl)

@[simp]
theorem reindex_polynomial (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k' : K') :
    (reindex eI eK h d).polynomial k' = d.polynomial (eK.symm k') := (rfl)

@[simp]
theorem reindex_symm (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex (𝕂 := 𝕂) eI eK h).symm =
      reindex eI.symm eK.symm (fun _ ↦ by simp [Equiv.symm_apply_eq, h]) := by
  ext d : 2
  · ext : 1 <;> simp [reindex]
  · funext k; simp [reindex]

@[simp]
theorem reindex_refl (h : ∀ k, Equiv.refl I (row k) = row (Equiv.refl K k)) :
    reindex (𝕂 := 𝕂) (Equiv.refl I) (Equiv.refl K) h = Equiv.refl (ExchangeData 𝕂 row) := by
  ext d : 2
  · simp
  · funext k; simp

theorem reindex_trans (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    (reindex (𝕂 := 𝕂) eI eK h).trans (reindex eI' eK' h') =
      reindex (eI.trans eI') (eK.trans eK')
        (fun k ↦ by rw [Equiv.trans_apply, Equiv.trans_apply, h, h']) := by
  ext d : 2
  · exact congrArg (fun e ↦ e d.exchange) (ExchangeMatrix.reindex_trans eI eK h eI' eK' h')
  · funext k; simp

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
    (d : ExchangeData 𝕂 row) : (reindex eI eK h d).IsBinary ↔ d.IsBinary :=
  ⟨fun hd k ↦ by simpa using hd (eK k), fun hd k' ↦ hd (eK.symm k')⟩

@[simp]
theorem valueAtOne_reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k' : K') :
    (reindex eI eK h d).valueAtOne c k' = d.valueAtOne c (eK.symm k') := (rfl)

@[simp]
theorem map_reindex (ψ : 𝕂 →*₀ 𝕂') (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).map ψ = reindex eI eK h (d.map ψ) := by ext : 1 <;> rfl

/-- Reindexing commutes with state mutation. -/
theorem reindex_mutation [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    reindex eI eK h (d.mutation c k) = (reindex eI eK h d).mutation c (eK k) := by
  ext : 1
  · exact (d.exchange.mutation_reindex eI eK h k).symm
  · funext j'
    by_cases hj : j' = eK k
    · subst hj; simp
    · have hj' : eK.symm j' ≠ k := by simpa [Equiv.symm_apply_eq] using hj
      have hrow : eI.symm (row' (eK k)) = row k := (Equiv.symm_apply_eq eI).mpr (h k).symm
      simp [mutatedPolynomial_of_ne _ _ hj, mutatedPolynomial_of_ne _ _ hj', hrow]

theorem reindex_mutationWord [DecidableEq I] [DecidableEq I'] [DecidableEq K] [DecidableEq K']
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    reindex eI eK h (d.mutationWord c w) = (reindex eI eK h d).mutationWord c (w.map eK) := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (reindex eI eK h) fun s k ↦ (s.reindex_mutation eI eK h c k).symm).symm

end Reindex

/-! ### Checks -/

/-- For `H = 1 + T + T²` on a rank-one zero column over `𝔽₃`, the value `H(1)` vanishes. -/
example :
    let H : ExchangePolynomial (ZMod 3) := ⟨2, by decide, fun _ ↦ 1, isUnit_one, isUnit_one⟩
    let d : ExchangeData (ZMod 3) (Function.Embedding.refl Unit) :=
      ⟨⟨0, fun _ ↦ 1, ⟨by decide, by decide⟩⟩, fun _ ↦ H, fun _ _ ↦ dvd_zero _⟩
    d.valueAtOne (CoefficientSystem.trivial (ZMod 3)) () = 0 := by
  intro H d
  simp only [valueAtOne_def, d, H, CoefficientSystem.trivial_toScalar, MonoidWithZeroHom.id_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  decide

section B2PeriodicityExample

private abbrev b2Exch (ε : Bool) : ExchangeMatrix (Function.Embedding.refl (Fin 2)) where
  matrix := if ε then !![0, 2; -1, 0] else !![0, -2; 1, 0]
  symmetrizer := ![1, 2]
  isSkewSymmetrizer := by cases ε <;> exact ⟨by decide, by decide⟩

private theorem b2Exch_mutation (ε : Bool) (k : Fin 2) : (b2Exch ε).mutation k = b2Exch (!ε) := by
  ext i j : 2
  · cases ε <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [b2Exch, ExchangeMatrix.mutation_matrix, matrixMutation_apply]
  · simp [b2Exch]

private abbrev mkB2 (ε : Bool) (a₀ b₀ a₁ b₁ c₁ : ℚ≥0)
    (ha₀ : a₀ ≠ 0 := by norm_num) (hb₀ : b₀ ≠ 0 := by norm_num)
    (ha₁ : a₁ ≠ 0 := by norm_num) (hc₁ : c₁ ≠ 0 := by norm_num) :
    ExchangeData ℚ≥0 (Function.Embedding.refl (Fin 2)) where
  exchange := b2Exch ε
  polynomial := ![
    ⟨1, by decide, ![a₀, b₀], isUnit_iff_ne_zero.mpr ha₀,
      isUnit_iff_ne_zero.mpr (by simpa [Fin.last] using hb₀)⟩,
    ⟨2, by decide, ![a₁, b₁, c₁], isUnit_iff_ne_zero.mpr ha₁,
      isUnit_iff_ne_zero.mpr (by simpa [Fin.last] using hc₁)⟩]
  degree_dvd i k := by cases ε <;> fin_cases i <;> fin_cases k <;> dsimp <;> decide

private noncomputable abbrev b2Sys : CoefficientSystem ℚ≥0 ℚ :=
  CoefficientSystem.ofSemifield NNRat.coeHom.toMonoidWithZeroHom

private theorem b2_divCol0 (ε : Bool) {a₀ b₀ a₁ b₁ c₁ : ℚ≥0} {ha₀ hb₀ ha₁ hc₁} :
    (mkB2 ε a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁).dividedColumn 1 0 = if ε then 1 else -1 := by
  cases ε <;> simp [dividedColumn_def]

private theorem b2_divCol1 (ε : Bool) {a₀ b₀ a₁ b₁ c₁ : ℚ≥0} {ha₀ hb₀ ha₁ hc₁} :
    (mkB2 ε a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁).dividedColumn 0 1 = if ε then -1 else 1 := by
  cases ε <;> simp [dividedColumn_def]

private theorem b2Step0 (ε : Bool) {a₀ b₀ a₁ b₁ c₁ a₁' b₁' c₁' : ℚ≥0}
    {ha₀ : a₀ ≠ 0} {hb₀ : b₀ ≠ 0} {ha₁ : a₁ ≠ 0} {hc₁ : c₁ ≠ 0}
    {ha₁' : a₁' ≠ 0} {hc₁' : c₁' ≠ 0}
    (hg : let κ := if ε then b₀ else a₀⁻¹
      let s := (κ ^ 0 * a₁ + κ ^ 1 * b₁ + κ ^ 2 * c₁)⁻¹
      a₁' = s * (κ ^ 0 * a₁) ∧ b₁' = s * (κ ^ 1 * b₁) ∧ c₁' = s * (κ ^ 2 * c₁) := by
        dsimp; norm_num) :
    (mkB2 ε a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁).mutation b2Sys 0 =
      mkB2 (!ε) b₀ a₀ a₁' b₁' c₁' hb₀ ha₀ ha₁' hc₁' := by
  symm; ext : 1; · exact (b2Exch_mutation ε 0).symm
  rw [funext_iff, Fin.forall_fin_two]; simp only [mutation_polynomial]
  refine ⟨ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_,
    ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_⟩
  · rw [coeff_mutatedPolynomial_self]; fin_cases l <;> rfl
  · let u := mkB2 ε a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁
    let κ : ℚ≥0 := if ε then b₀ else a₀⁻¹
    rw [coeff_mutatedPolynomial_ofSemifield_of_ne _ u (by decide)]
    dsimp only
    have hκ : (u.polynomial 0).coeff (Fin.last (u.polynomial 0).degree) ^
        (u.dividedColumn 1 (Function.Embedding.refl (Fin 2) 0))⁺ *
        (u.polynomial 0).coeff 0 ^
          (-(u.dividedColumn 1 (Function.Embedding.refl (Fin 2) 0))⁻) = κ := by
      have h0 : (u.polynomial 0).coeff 0 = a₀ := rfl
      have h1 : (u.polynomial 0).coeff (Fin.last (u.polynomial 0).degree) = b₀ := rfl
      rw [h0, h1]; dsimp [u, κ]; cases ε <;> simp [b2_divCol0]
    have hsum : ∑ m, κ ^ m.val * (u.polynomial 1).coeff m =
        κ ^ 0 * a₁ + κ ^ 1 * b₁ + κ ^ 2 * c₁ :=
      Fin.sum_univ_three fun m ↦ κ ^ m.val * (u.polynomial 1).coeff m
    rw [hκ, hsum]
    fin_cases l
    · exact hg.1
    · exact hg.2.1
    · exact hg.2.2

private theorem b2Step1 (ε : Bool) {a₀ b₀ a₁ b₁ c₁ a₀' b₀' : ℚ≥0}
    {ha₀ : a₀ ≠ 0} {hb₀ : b₀ ≠ 0} {ha₁ : a₁ ≠ 0} {hc₁ : c₁ ≠ 0}
    {ha₀' : a₀' ≠ 0} {hb₀' : b₀' ≠ 0}
    (hh : let κ := if ε then a₁⁻¹ else c₁
      let s := (κ ^ 0 * a₀ + κ ^ 1 * b₀)⁻¹
      a₀' = s * (κ ^ 0 * a₀) ∧ b₀' = s * (κ ^ 1 * b₀) := by dsimp; norm_num) :
    (mkB2 ε a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁).mutation b2Sys 1 =
      mkB2 (!ε) a₀' b₀' c₁ b₁ a₁ ha₀' hb₀' hc₁ ha₁ := by
  symm; ext : 1; · exact (b2Exch_mutation ε 1).symm
  rw [funext_iff, Fin.forall_fin_two]; simp only [mutation_polynomial]
  refine ⟨ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_,
    ExchangePolynomial.ext (by rw [degree_mutatedPolynomial]; rfl) fun l ↦ ?_⟩
  · let u := mkB2 ε a₀ b₀ a₁ b₁ c₁ ha₀ hb₀ ha₁ hc₁
    let κ : ℚ≥0 := if ε then a₁⁻¹ else c₁
    rw [coeff_mutatedPolynomial_ofSemifield_of_ne _ u (by decide)]
    dsimp only
    have hκ : (u.polynomial 1).coeff (Fin.last (u.polynomial 1).degree) ^
        (u.dividedColumn 0 (Function.Embedding.refl (Fin 2) 1))⁺ *
        (u.polynomial 1).coeff 0 ^
          (-(u.dividedColumn 0 (Function.Embedding.refl (Fin 2) 1))⁻) = κ := by
      have h0 : (u.polynomial 1).coeff 0 = a₁ := rfl
      have h1 : (u.polynomial 1).coeff (Fin.last (u.polynomial 1).degree) = c₁ := rfl
      rw [h0, h1]; dsimp [u, κ]; cases ε <;> simp [b2_divCol1]
    have hsum : ∑ m, κ ^ m.val * (u.polynomial 0).coeff m = κ ^ 0 * a₀ + κ ^ 1 * b₀ :=
      Fin.sum_univ_two fun m ↦ κ ^ m.val * (u.polynomial 0).coeff m
    rw [hκ, hsum]
    fin_cases l
    · exact hh.1
    · exact hh.2
  · rw [coeff_mutatedPolynomial_self]; fin_cases l <;> rfl

/-- Six-step periodicity in type `B₂`/`C₂` with degrees `(1, 2)` over `ℚ≥0`: for
`B = !![0, 2; -1, 0]`, `H₀(T) = (1 + 2T)/3`, and `H₁(T) = (1 + 4T + 3T²)/8`, six alternating
mutations `[0, 1, 0, 1, 0, 1]` return the initial exchange data. -/
example :
    let c : CoefficientSystem ℚ≥0 ℚ :=
      CoefficientSystem.ofSemifield NNRat.coeHom.toMonoidWithZeroHom
    let H₀ : ExchangePolynomial ℚ≥0 :=
      ⟨1, by decide, ![1 / 3, 2 / 3], isUnit_iff_ne_zero.mpr (by simp),
        isUnit_iff_ne_zero.mpr (by simp [Fin.last])⟩
    let H₁ : ExchangePolynomial ℚ≥0 :=
      ⟨2, by decide, ![1 / 8, 4 / 8, 3 / 8], isUnit_iff_ne_zero.mpr (by simp),
        isUnit_iff_ne_zero.mpr (by simp [Fin.last])⟩
    let d : ExchangeData ℚ≥0 (Function.Embedding.refl (Fin 2)) :=
      ⟨⟨!![0, 2; -1, 0], ![1, 2], ⟨by decide, by decide⟩⟩, ![H₀, H₁],
        fun i k ↦ by fin_cases i <;> fin_cases k <;> decide⟩
    d.mutationWord c [0, 1, 0, 1, 0, 1] = d := by
  intro c H₀ H₁ d
  set s₀ := mkB2 true (1 / 3) (2 / 3) (1 / 8) (4 / 8) (3 / 8)
  change s₀.mutationWord b2Sys [0, 1, 0, 1, 0, 1] = s₀
  have hd : s₀.IsNormalized b2Sys := by
    rw [isNormalized_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [CoefficientSystem.isNormalized_ofSemifield_iff,
        show ∑ l, (s₀.polynomial 0).coeff l = (1 / 3 : ℚ≥0) + 2 / 3 from
          Fin.sum_univ_two fun l ↦ (s₀.polynomial 0).coeff l]; norm_num
    · rw [CoefficientSystem.isNormalized_ofSemifield_iff,
        show ∑ l, (s₀.polynomial 1).coeff l = (1 / 8 : ℚ≥0) + 4 / 8 + 3 / 8 from
          Fin.sum_univ_three fun l ↦ (s₀.polynomial 1).coeff l]; norm_num
  set s₁ := mkB2 false (2 / 3) (1 / 3) (3 / 15) (8 / 15) (4 / 15)
  set s₂ := mkB2 true (15 / 17) (2 / 17) (4 / 15) (8 / 15) (3 / 15)
  set mid := mkB2 false (2 / 17) (15 / 17) (289 / 360) (68 / 360) (3 / 360)
  set t₁ := mkB2 false (1 / 17) (16 / 17) (3 / 8) (4 / 8) (1 / 8)
  set t₂ := mkB2 true (16 / 17) (1 / 17) (3 / 360) (68 / 360) (289 / 360)
  have hs₁ : s₀.mutation b2Sys 0 = s₁ := b2Step0 true
  have hs₂ : s₁.mutation b2Sys 1 = s₂ := b2Step1 false
  have hmid₁ : s₂.mutation b2Sys 0 = mid := b2Step0 true
  have ht₁ : s₀.mutation b2Sys 1 = t₁ := b2Step1 true
  have ht₂ : t₁.mutation b2Sys 0 = t₂ := b2Step0 false
  have hmid₂ : t₂.mutation b2Sys 1 = mid := b2Step1 true
  have hmid : s₀.mutationWord b2Sys [0, 1, 0] = s₀.mutationWord b2Sys [1, 0, 1] := by
    simp only [mutationWord_cons, mutationWord_nil, hs₁, hs₂, hmid₁, ht₁, ht₂, hmid₂]
  rw [show ([0, 1, 0, 1, 0, 1] : List (Fin 2)) = [0, 1, 0] ++ ([1, 0, 1] : List (Fin 2)).reverse
    from rfl, mutationWord_append, hmid]
  exact mutationWord_mutationWord_reverse hd [1, 0, 1]

end B2PeriodicityExample

end ExchangeData

end TauCeti
