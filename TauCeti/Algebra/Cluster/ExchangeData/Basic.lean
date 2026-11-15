/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSystem.Hom
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Divisibility

import Mathlib.Algebra.Field.Rat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exchange data and polynomial mutation

*Exchange data* along an embedding `row : K ↪ I` of mutable indices into all indices package an
extended `ExchangeMatrix row` together with an `ExchangePolynomial 𝕂` at each mutable index `k : K`
whose degree divides every entry of column `k`. Dividing column `k` by its positive exchange degree
produces the integer vector `dividedColumn d k : I → ℤ`.

Given a `CoefficientSystem 𝕂 R`, mutation of exchange data in direction `k` has three components:

1. mutate the extended exchange matrix in direction `k`, preserving column divisibility;
2. reverse the exchange polynomial at `k`;
3. dilate every other exchange polynomial `H_j` by
   `(H_k).dilationFactor (d.dividedColumn j (row k))` and normalize the result with `c.normalize`.

When all polynomials of `d` are normalized (`d.IsNormalized c`), the mutated exchange data remain
normalized and mutating twice in the same direction recovers `d`. Consequently, finite mutation
words act on normalized exchange data by involutive steps, reversing a word inverts its action, and
homomorphisms of coefficient systems commute with single-step and word mutation.

In the scalar system `CoefficientSystem.trivial R`, every state is normalized and `c.normalize` is
the identity; this recovers unnormalized polynomial mutation, under which states with unit-one
endpoints (`HasUnitOneEndpoints`) and binary states (`IsBinary`) are closed.

## Main definitions

* `TauCeti.ExchangeData 𝕂 row`: an extended exchange matrix together with exchange polynomials over
  `𝕂` whose degrees divide the corresponding columns.
* `TauCeti.ExchangeData.dividedColumn`: the exact integer quotient `B_{•, k} / deg(H_k)`.
* `TauCeti.ExchangeData.mutatedPolynomial` and `TauCeti.ExchangeData.mutation`: single-step mutation
  of exchange polynomials and bundled exchange data for a coefficient system `c`.
* `TauCeti.ExchangeData.mutationWord`: left-fold action of a finite mutation word `List K`.
* `TauCeti.ExchangeData.IsNormalized`: predicate that every exchange polynomial is normalized for
  `c`.
* `TauCeti.ExchangeData.HasUnitOneEndpoints` and `TauCeti.ExchangeData.IsBinary`: exchange data
  whose polynomials have endpoint coefficients `1`, respectively equal `1 + T`.
* `TauCeti.ExchangeData.submatrix`, `TauCeti.ExchangeData.principal`,
  `TauCeti.ExchangeData.reindex`, and `TauCeti.ExchangeData.map`: restriction, passage to the
  principal block, index equivalence, and pushforward along multiplicative maps of coefficients.

## Main results

* `TauCeti.ExchangeData.dividedColumn_mutation`: exact mutation law for the divided columns.
* `TauCeti.ExchangeData.IsNormalized.mutation` and
  `TauCeti.ExchangeData.IsNormalized.mutation_mutation`: mutation preserves normalized exchange data
  and is an involution on them.
* `TauCeti.ExchangeData.IsNormalized.mutationWord_mutationWord_reverse`: reversing a mutation word
  undoes its action on normalized exchange data.
* `TauCeti.ExchangeData.map_mutation` and `TauCeti.ExchangeData.map_mutationWord`: homomorphisms of
  coefficient systems commute with mutation and mutation words.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014, §2.
* T. Nakanishi and D. Rupel, *Companion cluster algebras to a generalized cluster algebra*,
  Proc. Amer. Math. Soc. 140 (2012), §3.
-/

public section

namespace TauCeti

/-- *Exchange data* over a coefficient monoid `𝕂` along the mutable row embedding `row : K ↪ I`:
an extended exchange matrix together with an exchange polynomial in each mutable direction whose
degree divides every entry of that column. -/
@[ext]
structure ExchangeData (𝕂 : Type*) [CommMonoidWithZero 𝕂] {I K : Type*} (row : K ↪ I) where
  /-- The underlying extended exchange matrix with its principal skew-symmetrizer. -/
  exchange : ExchangeMatrix row
  /-- The exchange polynomial attached to each mutable index. -/
  polynomial : K → ExchangePolynomial 𝕂
  /-- Each exchange degree divides every entry of its column, including frozen rows. -/
  degree_dvd : ∀ i k, ((polynomial k).degree : ℤ) ∣ exchange.matrix i k

namespace ExchangeData

variable {𝕂 𝕂' 𝕂'' R : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] [CommSemiring R]
  {I K I' K' I'' K'' : Type*} {row : K ↪ I} {row' : K' ↪ I'} {row'' : K'' ↪ I''}

/-! ### Degrees and divided columns -/

/-- The integer exchange degree `(d.polynomial k).degree` is positive. -/
theorem degree_intCast_pos (d : ExchangeData 𝕂 row) (k : K) :
    (0 : ℤ) < (d.polynomial k).degree :=
  Int.natCast_pos.mpr (d.polynomial k).degree_pos

theorem degree_intCast_ne_zero (d : ExchangeData 𝕂 row) (k : K) :
    ((d.polynomial k).degree : ℤ) ≠ 0 :=
  (d.degree_intCast_pos k).ne'

/-- The divided column `β_k(i) = B_{i, k} / deg(H_k)`. Because `deg(H_k)` divides every entry of
column `k`, this integer division is exact. -/
def dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) : ℤ :=
  d.exchange.matrix i k / ((d.polynomial k).degree : ℤ)

theorem dividedColumn_def (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = d.exchange.matrix i k / ((d.polynomial k).degree : ℤ) :=
  (rfl)

@[simp]
theorem dividedColumn_mul_degree (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i * ((d.polynomial k).degree : ℤ) = d.exchange.matrix i k :=
  Int.ediv_mul_cancel (d.degree_dvd i k)

@[simp]
theorem degree_mul_dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    ((d.polynomial k).degree : ℤ) * d.dividedColumn k i = d.exchange.matrix i k :=
  Int.mul_ediv_cancel' (d.degree_dvd i k)

/-- The diagonal entry of every divided column vanishes. -/
@[simp]
theorem dividedColumn_row_self (d : ExchangeData 𝕂 row) (k : K) :
    d.dividedColumn k (row k) = 0 := by
  simp [dividedColumn_def]

/-- An entry of `dividedColumn` vanishes if and only if the corresponding matrix entry vanishes. -/
@[simp]
theorem dividedColumn_eq_zero_iff (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = 0 ↔ d.exchange.matrix i k = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [dividedColumn_def, h]⟩
  rw [← d.dividedColumn_mul_degree k i, h, zero_mul]

/-- A divided column is positive at `i` if and only if the matrix entry is positive. -/
theorem dividedColumn_pos_iff (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    0 < d.dividedColumn k i ↔ 0 < d.exchange.matrix i k := by
  rw [← d.dividedColumn_mul_degree k i, mul_pos_iff_of_pos_right (d.degree_intCast_pos k)]

/-! ### Restriction, principal block, reindexing, and coefficient maps -/

/-- Restrict and relabel the rows and mutable indices of exchange data along compatible maps. -/
def submatrix (d : ExchangeData 𝕂 row) (f : I' → I) (g : K' → K)
    (h : ∀ k, f (row' k) = row (g k)) : ExchangeData 𝕂 row' where
  exchange := d.exchange.submatrix f g h
  polynomial := d.polynomial ∘ g
  degree_dvd i k := by simpa using d.degree_dvd (f i) (g k)

@[simp]
theorem submatrix_exchange (d : ExchangeData 𝕂 row) (f : I' → I) (g : K' → K)
    (h : ∀ k, f (row' k) = row (g k)) :
    (d.submatrix f g h).exchange = d.exchange.submatrix f g h :=
  (rfl)

@[simp]
theorem submatrix_polynomial (d : ExchangeData 𝕂 row) (f : I' → I) (g : K' → K)
    (h : ∀ k, f (row' k) = row (g k)) (k : K') :
    (d.submatrix f g h).polynomial k = d.polynomial (g k) :=
  (rfl)

@[simp]
theorem dividedColumn_submatrix (d : ExchangeData 𝕂 row) (f : I' → I) (g : K' → K)
    (h : ∀ k, f (row' k) = row (g k)) (k : K') (i : I') :
    (d.submatrix f g h).dividedColumn k i = d.dividedColumn (g k) (f i) := by
  simp [dividedColumn_def]

@[simp]
theorem submatrix_id (d : ExchangeData 𝕂 row) (h : ∀ k, id (row k) = row (id k)) :
    d.submatrix id id h = d :=
  ExchangeData.ext (d.exchange.submatrix_id h) rfl

@[simp]
theorem submatrix_submatrix (d : ExchangeData 𝕂 row) (f : I' → I) (g : K' → K)
    (h : ∀ k, f (row' k) = row (g k)) (f' : I'' → I') (g' : K'' → K')
    (h' : ∀ k, f' (row'' k) = row' (g' k)) :
    (d.submatrix f g h).submatrix f' g' h' =
      d.submatrix (f ∘ f') (g ∘ g') (fun k ↦ by
        rw [Function.comp_apply, Function.comp_apply, h', h]) :=
  ExchangeData.ext (d.exchange.submatrix_submatrix f g h f' g' h') rfl

/-- The principal part of exchange data: forget the frozen rows while keeping all exchange
polynomials. -/
def principal (d : ExchangeData 𝕂 row) : ExchangeData 𝕂 (Function.Embedding.refl K) :=
  d.submatrix row id fun k ↦ by rw [Function.Embedding.refl_apply, id_eq]

@[simp]
theorem principal_exchange (d : ExchangeData 𝕂 row) :
    d.principal.exchange = d.exchange.principal := by
  ext : 1 <;> simp [principal]

@[simp]
theorem principal_polynomial (d : ExchangeData 𝕂 row) (k : K) :
    d.principal.polynomial k = d.polynomial k :=
  (rfl)

@[simp]
theorem dividedColumn_principal (d : ExchangeData 𝕂 row) (k j : K) :
    d.principal.dividedColumn k j = d.dividedColumn k (row j) := by
  simp [principal]

/-- Reindex exchange data along equivalences of `I` and `K` commuting with `row`. -/
def reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    ExchangeData 𝕂 row ≃ ExchangeData 𝕂 row' where
  toFun d := d.submatrix eI.symm eK.symm fun k ↦ by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  invFun d := d.submatrix eI eK h
  left_inv d := by
    refine ExchangeData.ext ?_ (funext fun k ↦ ?_) <;> simp
  right_inv d := by
    refine ExchangeData.ext ?_ (funext fun k ↦ ?_) <;> simp

@[simp]
theorem reindex_exchange (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).exchange = ExchangeMatrix.reindex eI eK h d.exchange := by
  rw [ExchangeMatrix.reindex_apply]
  rfl

@[simp]
theorem reindex_polynomial (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k : K') :
    (reindex eI eK h d).polynomial k = d.polynomial (eK.symm k) :=
  (rfl)

@[simp]
theorem reindex_symm_apply (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row') :
    (reindex eI eK h).symm d = d.submatrix eI eK h :=
  (rfl)

@[simp]
theorem dividedColumn_reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k : K') (i : I') :
    (reindex eI eK h d).dividedColumn k i = d.dividedColumn (eK.symm k) (eI.symm i) := by
  simp [reindex]

/-- Push exchange data forward along a monoid-with-zero homomorphism `ψ : 𝕂 → 𝕂'`. -/
def map {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
    (d : ExchangeData 𝕂 row) : ExchangeData 𝕂' row where
  exchange := d.exchange
  polynomial k := (d.polynomial k).map ψ
  degree_dvd i k := by simpa using d.degree_dvd i k

@[simp]
theorem map_exchange {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
    (d : ExchangeData 𝕂 row) : (d.map ψ).exchange = d.exchange :=
  (rfl)

@[simp]
theorem map_polynomial {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
    (d : ExchangeData 𝕂 row) (k : K) : (d.map ψ).polynomial k = (d.polynomial k).map ψ :=
  (rfl)

@[simp]
theorem dividedColumn_map {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂'] (ψ : F)
    (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    (d.map ψ).dividedColumn k i = d.dividedColumn k i := by
  simp [dividedColumn_def]

@[simp]
theorem map_id (d : ExchangeData 𝕂 row) : d.map (MonoidWithZeroHom.id 𝕂) = d :=
  ExchangeData.ext rfl (funext fun _ ↦ ExchangePolynomial.map_id _)

theorem map_map {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂']
    {G : Type*} [FunLike G 𝕂' 𝕂''] [MonoidWithZeroHomClass G 𝕂' 𝕂''] (ψ : F) (χ : G)
    (d : ExchangeData 𝕂 row) :
    (d.map ψ).map χ =
      d.map ((MonoidWithZeroHom.ofClass χ).comp (MonoidWithZeroHom.ofClass ψ)) :=
  ExchangeData.ext rfl (funext fun _ ↦ ExchangePolynomial.map_map _ _ _)

/-! ### Predicates on exchange data -/

/-- Exchange data `d` are *normalized* for `c` when every exchange polynomial of `d` is normalized
for `c`. -/
def IsNormalized (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, c.IsNormalized (d.polynomial k)

theorem isNormalized_def {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row} :
    d.IsNormalized c ↔ ∀ k, c.IsNormalized (d.polynomial k) :=
  Iff.rfl

theorem IsNormalized.apply {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) : c.IsNormalized (d.polynomial k) :=
  hd k

@[simp]
theorem isNormalized_trivial (d : ExchangeData R row) :
    d.IsNormalized (CoefficientSystem.trivial R) :=
  fun k ↦ CoefficientSystem.isNormalized_trivial (d.polynomial k)

/-- Homomorphisms of coefficient systems preserve normalized exchange data. -/
theorem IsNormalized.map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (f : CoefficientSystemHom c c') :
    (d.map f).IsNormalized c' :=
  fun k ↦ (hd k).map f

/-- Exchange data have *unit-one endpoints* when every exchange polynomial has constant and leading
coefficients equal to `1`. -/
def HasUnitOneEndpoints (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, (d.polynomial k).HasUnitOneEndpoints

theorem hasUnitOneEndpoints_def {d : ExchangeData 𝕂 row} :
    d.HasUnitOneEndpoints ↔ ∀ k, (d.polynomial k).HasUnitOneEndpoints :=
  Iff.rfl

theorem HasUnitOneEndpoints.apply {d : ExchangeData 𝕂 row} (hd : d.HasUnitOneEndpoints) (k : K) :
    (d.polynomial k).HasUnitOneEndpoints :=
  hd k

/-- Exchange data are *binary* when every exchange polynomial equals `1 + T`. -/
def IsBinary (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, d.polynomial k = ExchangePolynomial.binary

theorem isBinary_def {d : ExchangeData 𝕂 row} :
    d.IsBinary ↔ ∀ k, d.polynomial k = ExchangePolynomial.binary :=
  Iff.rfl

theorem IsBinary.polynomial_eq {d : ExchangeData 𝕂 row} (hd : d.IsBinary) (k : K) :
    d.polynomial k = ExchangePolynomial.binary :=
  hd k

protected theorem IsBinary.hasUnitOneEndpoints {d : ExchangeData 𝕂 row} (hd : d.IsBinary) :
    d.HasUnitOneEndpoints :=
  fun k ↦ (hd k).symm ▸ ExchangePolynomial.hasUnitOneEndpoints_binary

/-- Canonical binary exchange data attached to any `ExchangeMatrix row`, with `H_k = 1 + T` in
every mutable direction. -/
def ofExchangeMatrix (B : ExchangeMatrix row) : ExchangeData 𝕂 row where
  exchange := B
  polynomial _ := ExchangePolynomial.binary
  degree_dvd _ _ := by simp

@[simp]
theorem ofExchangeMatrix_exchange (B : ExchangeMatrix row) :
    (ofExchangeMatrix B : ExchangeData 𝕂 row).exchange = B :=
  (rfl)

@[simp]
theorem ofExchangeMatrix_polynomial (B : ExchangeMatrix row) (k : K) :
    (ofExchangeMatrix B : ExchangeData 𝕂 row).polynomial k = ExchangePolynomial.binary :=
  (rfl)

@[simp]
theorem isBinary_ofExchangeMatrix (B : ExchangeMatrix row) :
    (ofExchangeMatrix B : ExchangeData 𝕂 row).IsBinary :=
  fun _ ↦ rfl

@[simp]
theorem dividedColumn_of_isBinary {d : ExchangeData 𝕂 row} (hd : d.IsBinary) (k : K) (i : I) :
    d.dividedColumn k i = d.exchange.matrix i k := by
  simp [dividedColumn_def, hd k]

/-! ### Mutation of exchange data -/

section MutatedPolynomial

variable [DecidableEq K]

/-- The family of exchange polynomials after mutating `d` at `k` in the coefficient system `c`:
reverse `d.polynomial k`, and dilate every other `d.polynomial j` by
`(d.polynomial k).dilationFactor (d.dividedColumn j (row k))` followed by `c.normalize`. -/
noncomputable def mutatedPolynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) : ExchangePolynomial 𝕂 :=
  if j = k then (d.polynomial k).reverse
  else c.normalize ((d.polynomial j).dilate
    ((d.polynomial k).dilationFactor (d.dividedColumn j (row k))))

@[simp]
theorem mutatedPolynomial_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.mutatedPolynomial c k k = (d.polynomial k).reverse := by
  simp [mutatedPolynomial]

theorem mutatedPolynomial_of_ne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) {k j : K}
    (hj : j ≠ k) :
    d.mutatedPolynomial c k j =
      c.normalize ((d.polynomial j).dilate
        ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))) := by
  simp [mutatedPolynomial, hj]

/-- Mutation preserves the exchange degree in every mutable direction. -/
@[simp]
theorem mutatedPolynomial_degree (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) : (d.mutatedPolynomial c k j).degree = (d.polynomial j).degree := by
  obtain rfl | hj := eq_or_ne j k
  · simp
  · simp [mutatedPolynomial_of_ne c d hj]

end MutatedPolynomial

section Mutation

variable [DecidableEq I] [DecidableEq K]

/-- Mutate exchange data `d` in direction `k` with respect to the coefficient system `c`. -/
noncomputable def mutation (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    ExchangeData 𝕂 row where
  exchange := d.exchange.mutation k
  polynomial := d.mutatedPolynomial c k
  degree_dvd i j := by
    rw [mutatedPolynomial_degree, ExchangeMatrix.mutation_matrix]
    exact dvd_matrixMutation (fun a ↦ d.degree_dvd a j) k i

@[simp]
theorem mutation_exchange (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchange = d.exchange.mutation k :=
  (rfl)

@[simp]
theorem mutation_polynomial (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k j : K) :
    (d.mutation c k).polynomial j = d.mutatedPolynomial c k j :=
  (rfl)

/-- Exact mutation formula for the divided columns of `d.mutation c k`. -/
theorem dividedColumn_mutation (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) (i : I) :
    (d.mutation c k).dividedColumn j i =
      if i = row k ∨ j = k then -d.dividedColumn j i
      else d.dividedColumn j i +
        ((d.polynomial k).degree : ℤ) * (d.dividedColumn k i)⁺ * (d.dividedColumn j (row k))⁺ -
        ((d.polynomial k).degree : ℤ) * (d.dividedColumn k i)⁻ * (d.dividedColumn j (row k))⁻ := by
  simpa only [dividedColumn_def, mutation_exchange, ExchangeMatrix.mutation_matrix,
    mutation_polynomial, mutatedPolynomial_degree] using
    matrixMutation_ediv_apply (row := row) (B := d.exchange.matrix)
      (fun j ↦ ((d.polynomial j).degree : ℤ)) d.degree_intCast_pos d.degree_dvd k i j

@[simp]
theorem dividedColumn_mutation_row (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) :
    (d.mutation c k).dividedColumn j (row k) = -d.dividedColumn j (row k) := by
  simp [dividedColumn_mutation]

@[simp]
theorem dividedColumn_mutation_self (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) (i : I) :
    (d.mutation c k).dividedColumn k i = -d.dividedColumn k i := by
  simp [dividedColumn_mutation]

/-- A column of `d.mutation c k` vanishes if and only if it vanished in `d`. -/
theorem mutation_column_eq_zero_iff (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k j : K) :
    (∀ i, (d.mutation c k).exchange.matrix i j = 0) ↔ ∀ i, d.exchange.matrix i j = 0 := by
  simp

/-- Mutation preserves normalized exchange data. -/
protected theorem IsNormalized.mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) : (d.mutation c k).IsNormalized c := by
  intro j
  obtain rfl | hj := eq_or_ne j k
  · simpa using (hd j).reverse
  · simp [mutatedPolynomial_of_ne c d hj]

/-- On normalized exchange data, an entry `B_{row k, j} = 0` with `j ≠ k` leaves `polynomial j`
unchanged under mutation at `k`. -/
theorem IsNormalized.mutation_polynomial_of_matrix_row_eq_zero {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) {k j : K} (hj : j ≠ k)
    (h0 : d.exchange.matrix (row k) j = 0) :
    (d.mutation c k).polynomial j = d.polynomial j := by
  have hdiv : d.dividedColumn j (row k) = 0 := (d.dividedColumn_eq_zero_iff j (row k)).mpr h0
  rw [mutation_polynomial, mutatedPolynomial_of_ne c d hj, hdiv,
    ExchangePolynomial.dilationFactor_zero, ExchangePolynomial.dilate_one, (hd j).normalize_eq]

/-- **Involutivity of exchange-data mutation**: mutating normalized exchange data twice in the same
direction recovers the original exchange data. -/
theorem IsNormalized.mutation_mutation {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (k : K) :
    (d.mutation c k).mutation c k = d := by
  refine ExchangeData.ext (by simp) (funext fun j ↦ ?_)
  obtain rfl | hj := eq_or_ne j k
  · simp
  · let p := (d.polynomial j).dilate ((d.polynomial k).dilationFactor (d.dividedColumn j (row k)))
    have hpolj : (d.mutation c k).polynomial j = p.scale (c.normalizer p) := by
      simp [p, mutatedPolynomial_of_ne c d hj, CoefficientSystem.normalize_def]
    rw [mutation_polynomial, mutatedPolynomial_of_ne c (d.mutation c k) hj, hpolj,
      mutation_polynomial, mutatedPolynomial_self, dividedColumn_mutation_row,
      ExchangePolynomial.dilationFactor_reverse_neg, ExchangePolynomial.dilate_scale,
      CoefficientSystem.normalize_scale_normalizer, ExchangePolynomial.dilate_mul_inv_cancel,
      (hd j).normalize_eq]

/-- Polynomial mutation in the scalar system `CoefficientSystem.trivial R` is unconditionally an
involution. -/
@[simp]
theorem mutation_trivial_mutation (d : ExchangeData R row) (k : K) :
    (d.mutation (CoefficientSystem.trivial R) k).mutation (CoefficientSystem.trivial R) k = d :=
  d.isNormalized_trivial.mutation_mutation k

/-! ### Finite mutation words -/

/-- Mutate exchange data along a finite word `w : List K` in reading order. -/
noncomputable def mutationWord (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) : ExchangeData 𝕂 row :=
  w.foldl (fun e k ↦ e.mutation c k) d

theorem mutationWord_eq_foldl (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    d.mutationWord c w = w.foldl (fun e k ↦ e.mutation c k) d :=
  (rfl)

@[simp]
theorem mutationWord_nil (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) :
    d.mutationWord c [] = d :=
  (rfl)

@[simp]
theorem mutationWord_cons (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K)
    (w : List K) :
    d.mutationWord c (k :: w) = (d.mutation c k).mutationWord c w :=
  (rfl)

@[simp]
theorem mutationWord_append (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (u v : List K) :
    d.mutationWord c (u ++ v) = (d.mutationWord c u).mutationWord c v :=
  List.foldl_append

/-- Projecting to the underlying `ExchangeMatrix` commutes with every mutation word. -/
@[simp]
theorem mutationWord_exchange (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (w : List K) :
    (d.mutationWord c w).exchange = d.exchange.mutationWord w := by
  rw [mutationWord_eq_foldl, ExchangeMatrix.mutationWord_eq_foldl]
  exact (List.foldl_hom (fun e : ExchangeData 𝕂 row ↦ e.exchange)
    (fun e k ↦ (e.mutation_exchange c k).symm)).symm

@[simp]
theorem mutationWord_polynomial_degree (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) (j : K) :
    ((d.mutationWord c w).polynomial j).degree = (d.polynomial j).degree := by
  induction w generalizing d with
  | nil => rfl
  | cons k _w ih => simpa using ih (d.mutation c k)

/-- A column of `d.mutationWord c w` vanishes if and only if it vanished in `d`. -/
theorem mutationWord_column_eq_zero_iff (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (w : List K) (j : K) :
    (∀ i, (d.mutationWord c w).exchange.matrix i j = 0) ↔ ∀ i, d.exchange.matrix i j = 0 := by
  simp

/-- Mutation words preserve normalized exchange data. -/
protected theorem IsNormalized.mutationWord {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row}
    (hd : d.IsNormalized c) (w : List K) : (d.mutationWord c w).IsNormalized c := by
  induction w generalizing d with
  | nil => exact hd
  | cons k _w ih => exact ih (hd.mutation k)

/-- Reversing a mutation word undoes its action on normalized exchange data. -/
theorem IsNormalized.mutationWord_mutationWord_reverse {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w).mutationWord c w.reverse = d := by
  let step (x : {e : ExchangeData 𝕂 row // e.IsNormalized c}) (k : K) :
      {e : ExchangeData 𝕂 row // e.IsNormalized c} :=
    ⟨x.1.mutation c k, x.2.mutation k⟩
  have hinv : ∀ k, Function.Involutive (fun x ↦ step x k) := fun k x ↦
    Subtype.ext (x.2.mutation_mutation k)
  have hfold : ∀ (u : List K) (x : {e : ExchangeData 𝕂 row // e.IsNormalized c}),
      (u.foldl step x).1 = x.1.mutationWord c u := by
    intro u
    induction u with
    | nil => intro x; rfl
    | cons k _u ih => intro x; exact ih (step x k)
  have key := foldl_reverse_foldl_of_involutive step hinv w ⟨d, hd⟩
  simpa only [hfold] using congrArg Subtype.val key

/-- Applying the reversed mutation word first also inverts the word action on normalized data. -/
theorem IsNormalized.mutationWord_reverse_mutationWord {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (w : List K) :
    (d.mutationWord c w.reverse).mutationWord c w = d := by
  simpa only [List.reverse_reverse] using hd.mutationWord_mutationWord_reverse w.reverse

/-- Adjacent equal directions cancel inside a mutation word on normalized exchange data. -/
theorem IsNormalized.mutationWord_append_cons_cons_self {c : CoefficientSystem 𝕂 R}
    {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (u v : List K) (k : K) :
    d.mutationWord c (u ++ k :: k :: v) = d.mutationWord c (u ++ v) := by
  simp only [mutationWord_append, mutationWord_cons]
  rw [(hd.mutationWord u).mutation_mutation k]

/-! ### Compatibility of mutation with restriction, reindexing, and coefficient maps -/

/-- Injective row restriction commutes with exchange-data mutation. -/
theorem submatrix_mutation [DecidableEq I'] [DecidableEq K'] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) {f : I' → I} {g : K' → K} (hf : Function.Injective f)
    (h : ∀ k, f (row' k) = row (g k)) (k : K') :
    (d.mutation c (g k)).submatrix f g h = (d.submatrix f g h).mutation c k := by
  have hg : Function.Injective g := fun _ _ hk ↦
    row'.injective (hf (by rw [h, h, hk]))
  refine ExchangeData.ext (d.exchange.submatrix_mutation hf h k) (funext fun j ↦ ?_)
  simp only [submatrix_polynomial, mutation_polynomial, mutatedPolynomial, hg.eq_iff]
  split_ifs with hjk
  · rfl
  · simp [h]

/-- Taking the principal block commutes with exchange-data mutation. -/
@[simp]
theorem principal_mutation (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).principal = d.principal.mutation c k :=
  d.submatrix_mutation c row.injective (fun _ ↦ rfl) k

/-- Reindexing commutes with exchange-data mutation. -/
theorem mutation_reindex [DecidableEq I'] [DecidableEq K'] (c : CoefficientSystem 𝕂 R)
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k : K) :
    (reindex eI eK h d).mutation c (eK k) = reindex eI eK h (d.mutation c k) := by
  have h' : ∀ k', eI.symm (row' k') = row (eK.symm k') := fun k' ↦ by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  simpa only [reindex, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using
    (d.submatrix_mutation c eI.symm.injective h' (eK k)).symm

/-- Reindexing commutes with every finite mutation word. -/
theorem reindex_mutationWord [DecidableEq I'] [DecidableEq K'] (c : CoefficientSystem 𝕂 R)
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (w : List K) :
    reindex eI eK h (d.mutationWord c w) =
      (reindex eI eK h d).mutationWord c (w.map eK) := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (reindex eI eK h)
    (fun e k ↦ mutation_reindex c eI eK h e k)).symm

/-- Homomorphisms of coefficient systems commute with exchange-data mutation. -/
@[simp]
theorem map_mutation {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : CoefficientSystemHom c c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).map f = (d.map f).mutation c' k := by
  refine ExchangeData.ext rfl (funext fun j ↦ ?_)
  obtain rfl | hj := eq_or_ne j k
  · simp
  · simp [mutatedPolynomial_of_ne _ _ hj]

/-- Homomorphisms of coefficient systems commute with finite mutation words. -/
@[simp]
theorem map_mutationWord {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : CoefficientSystemHom c c') (d : ExchangeData 𝕂 row) (w : List K) :
    (d.mutationWord c w).map f = (d.map f).mutationWord c' w :=
  (List.foldl_hom (fun e : ExchangeData 𝕂 row ↦ e.map f)
    (fun e k ↦ (map_mutation f e k).symm)).symm

/-- On exchange data with endpoint coefficients `1`, polynomial mutation in the scalar system fixes
every polynomial away from the mutated direction `k`. -/
theorem HasUnitOneEndpoints.mutation_trivial_polynomial_of_ne {d : ExchangeData R row}
    (hd : d.HasUnitOneEndpoints) {k j : K} (hj : j ≠ k) :
    (d.mutation (CoefficientSystem.trivial R) k).polynomial j = d.polynomial j := by
  rw [mutation_polynomial, mutatedPolynomial_of_ne _ _ hj, (hd k).dilationFactor_eq_one,
    ExchangePolynomial.dilate_one, CoefficientSystem.normalize_trivial]

/-- Exchange data with endpoint coefficients `1` are closed under polynomial mutation in the scalar
system. -/
protected theorem HasUnitOneEndpoints.mutation_trivial {d : ExchangeData R row}
    (hd : d.HasUnitOneEndpoints) (k : K) :
    (d.mutation (CoefficientSystem.trivial R) k).HasUnitOneEndpoints := by
  intro j
  obtain rfl | hj := eq_or_ne j k
  · simpa using (hd j).reverse
  · rw [hd.mutation_trivial_polynomial_of_ne hj]
    exact hd j

/-- Binary exchange data are closed under polynomial mutation in the scalar system. -/
protected theorem IsBinary.mutation_trivial {d : ExchangeData R row} (hd : d.IsBinary) (k : K) :
    (d.mutation (CoefficientSystem.trivial R) k).IsBinary := by
  intro j
  obtain rfl | hj := eq_or_ne j k
  · simp [hd j]
  · rw [hd.hasUnitOneEndpoints.mutation_trivial_polynomial_of_ne hj, hd j]

@[simp]
theorem mutation_trivial_ofExchangeMatrix (B : ExchangeMatrix row) (k : K) :
    (ofExchangeMatrix B : ExchangeData R row).mutation (CoefficientSystem.trivial R) k =
      ofExchangeMatrix (B.mutation k) :=
  ExchangeData.ext rfl (funext fun j ↦ (isBinary_ofExchangeMatrix B).mutation_trivial k j)

end Mutation

/-! ### Checks -/

/-- On rank-2 exchange data with non-skew-symmetric matrix `[[0, 2], [-1, 0]]`, symmetrizer
`(1, 2)`, `H_0(T) = 1 + 2T` of degree `1`, and `H_1(T) = 1 + 3T + 5T²` of degree `2`, polynomial
mutation at `0` reverses `H_0` to `2 + T` and dilates `H_1` by `2^{2 / 2} = 2` to
`1 + 6T + 20T²`. -/
noncomputable example :
    let B : ExchangeMatrix (Function.Embedding.refl (Fin 2)) :=
      ⟨!![0, 2; -1, 0], ![1, 2], ⟨by decide, by decide⟩⟩
    let H₀ : ExchangePolynomial ℚ :=
      ⟨1, Nat.one_pos, fun l ↦ if (l : ℕ) = 0 then 1 else 2, isUnit_one, by norm_num⟩
    let H₁ : ExchangePolynomial ℚ :=
      ⟨2, by decide, fun l ↦ if (l : ℕ) = 0 then 1 else if (l : ℕ) = 1 then 3 else 5,
        isUnit_one, by norm_num⟩
    let d : ExchangeData ℚ (Function.Embedding.refl (Fin 2)) :=
      { exchange := B
        polynomial := ![H₀, H₁]
        degree_dvd i k := by
          fin_cases i <;> fin_cases k <;> simp [B, H₀, H₁] }
    let d' := d.mutation (CoefficientSystem.trivial ℚ) 0
    (d'.polynomial 0).coeff 0 = 2 ∧
      (d'.polynomial 1).coeff ⟨1, by simp [d', d, H₁]⟩ = 6 ∧
      (d'.polynomial 1).coeff (Fin.last (d'.polynomial 1).degree) = 20 ∧
      d'.mutation (CoefficientSystem.trivial ℚ) 0 = d := by
  intro B H₀ H₁ d d'
  have hdiv : d.dividedColumn 1 0 = 1 := by
    simp [dividedColumn_def, d, B, H₁]
  have hdil :
      (d.polynomial 0).dilationFactor (d.dividedColumn 1 0) = Units.mk0 2 (by norm_num) := by
    rw [hdiv, ExchangePolynomial.dilationFactor_of_nonneg _ (by omega)]
    ext
    simp [d, H₀]
  have hp0 : d'.polynomial 0 = H₀.reverse := by
    simp [d', d]
  have hp1 : d'.polynomial 1 = H₁.dilate (Units.mk0 2 (by norm_num)) := by
    have hmut : d'.polynomial 1 = d.mutatedPolynomial (CoefficientSystem.trivial ℚ) 0 1 :=
      d.mutation_polynomial _ 0 1
    rw [hmut, d.mutatedPolynomial_of_ne _ (by decide), Function.Embedding.refl_apply, hdil,
      CoefficientSystem.normalize_trivial]
    simp [d]
  refine ⟨?_, ?_, ?_, d.mutation_trivial_mutation 0⟩
  · rw [ExchangePolynomial.ext_iff] at hp0
    simpa [H₀] using hp0.2 0
  · rw [ExchangePolynomial.ext_iff] at hp1
    have h1 := hp1.2 ⟨1, by simp [d', d, H₁]⟩
    simp only [ExchangePolynomial.dilate_coeff, Fin.val_cast, Units.val_mk0] at h1
    rw [h1]
    norm_num [H₁]
  · rw [ExchangePolynomial.ext_iff] at hp1
    have hlast := hp1.2 (Fin.last (d'.polynomial 1).degree)
    simp only [Fin.cast_last, ExchangePolynomial.dilate_coeff, Fin.val_last,
      ExchangePolynomial.dilate_degree, Units.val_mk0] at hlast
    rw [hlast]
    norm_num [H₁]

end ExchangeData

end TauCeti
