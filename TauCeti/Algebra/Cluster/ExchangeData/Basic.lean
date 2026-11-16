/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.Algebra.Cluster.CoefficientSystem.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

/-!
# Exchange data

*Exchange data* over a commutative monoid with zero `𝕂` along an embedding `row : K ↪ I` of mutable
indices into all indices consist of an extended exchange matrix `B` and a family of exchange
polynomials `H_k` (`k ∈ K`) over `𝕂` whose degrees `r_k` divide every entry of column `k`.

This file defines `TauCeti.ExchangeData` together with its divided columns `β_k = b_{•k} / r_k`,
the predicates of normalized, binary, and endpoint-one data, the scalar sum `H_k(1)`, the exchange
exponents `-e_k + l [β_k]₊ + (r_k - l) [-β_k]₊` (including their distinctness on nonzero columns),
the exchange numerator `E_k` in the Laurent ring `LaurentRing R {i : I // i ≠ row k}`, reindexing
along index equivalences, and coefficientwise pushforward along `MonoidWithZeroHom`s and
`CoefficientSystem.Hom`s.

## Main definitions

* `TauCeti.ExchangeData 𝕂 row`: an extended exchange matrix with exchange polynomials whose degrees
  divide the columns.
* `TauCeti.ExchangeData.dividedColumn`: the divided column `β_k = b_{•k} / r_k`.
* `TauCeti.ExchangeData.IsNormalized`, `TauCeti.ExchangeData.IsBinary`,
  `TauCeti.ExchangeData.IsEndpointOne`: structural predicates on exchange data.
* `TauCeti.ExchangeData.ofBinary`: binary exchange data built from an exchange matrix.
* `TauCeti.ExchangeData.valueAtOne`: the scalar value `H_k(1) = ∑_l φ(h_{k,l})`.
* `TauCeti.ExchangeData.exchangeExponent`: the exponent `-e_k + l [β_k]₊ + (r_k - l) [-β_k]₊`.
* `TauCeti.ExchangeData.exchangeNumerator`: the exchange numerator `E_k` in the Laurent ring
  `LaurentRing R {i : I // i ≠ row k}`.
* `TauCeti.ExchangeData.reindex`: reindexing along compatible equivalences of `I` and `K`.
* `TauCeti.ExchangeData.map`: coefficientwise pushforward along a `MonoidWithZeroHom`.

## Main results

* `TauCeti.ExchangeData.exchangeExponent_injOn`: on a nonzero column, the exchange exponents for
  `0 ≤ l ≤ r_k` are pairwise distinct.
* `TauCeti.ExchangeData.exchangeNumerator_eq_sum_pow`,
  `TauCeti.ExchangeData.exchangeNumerator_eq_sum_prod`: monomial-power and variable-product
  descriptions of the exchange numerator.
* `TauCeti.ExchangeData.inv_unitX_mul_rename_exchangeNumerator`: dividing the embedded exchange
  numerator by `X (row k)` yields the sum over `exchangeExponent`.

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. (2014), §2.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2.
-/

public section

namespace TauCeti

/-- *Exchange data* over a commutative monoid with zero `𝕂` along an embedding `row : K ↪ I` of
mutable indices: an extended exchange matrix and an exchange polynomial in each mutable direction
whose degree divides every entry of the corresponding column. -/
@[ext]
structure ExchangeData (𝕂 : Type*) [CommMonoidWithZero 𝕂] {I K : Type*} (row : K ↪ I) where
  /-- The underlying extended exchange matrix. -/
  exchange : ExchangeMatrix row
  /-- The exchange polynomial in each mutable direction. -/
  polynomial : K → ExchangePolynomial 𝕂
  /-- The degree of each exchange polynomial divides every entry in its column. -/
  degree_dvd : ∀ i k, ((polynomial k).degree : ℤ) ∣ exchange.matrix i k

namespace ExchangeData

variable {𝕂 𝕂' 𝕂'' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  [CommMonoidWithZero 𝕂''] {R S : Type*} [CommSemiring R] [CommSemiring S]
  {I I' I'' K K' K'' : Type*} {row : K ↪ I} {row' : K' ↪ I'} {row'' : K'' ↪ I''}

/-! ### Divided columns -/

/-- The divided column `β_k = b_{•k} / r_k` in direction `k`. Division is exact by `degree_dvd`. -/
def dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) : ℤ :=
  d.exchange.matrix i k / ((d.polynomial k).degree : ℤ)

theorem dividedColumn_def (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = d.exchange.matrix i k / ((d.polynomial k).degree : ℤ) :=
  (rfl)

/-- Multiplying a divided column entry by its degree recovers the exchange matrix entry. -/
theorem degree_mul_dividedColumn (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    ((d.polynomial k).degree : ℤ) * d.dividedColumn k i = d.exchange.matrix i k :=
  Int.mul_ediv_cancel' (d.degree_dvd i k)

/-- The diagonal entry of a divided column vanishes. -/
@[simp]
theorem dividedColumn_row_self (d : ExchangeData 𝕂 row) (k : K) :
    d.dividedColumn k (row k) = 0 := by
  simp [dividedColumn]

/-- A divided column entry vanishes if and only if the matrix entry vanishes. -/
theorem dividedColumn_eq_zero_iff (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    d.dividedColumn k i = 0 ↔ d.exchange.matrix i k = 0 := by
  constructor
  · intro h
    rw [← d.degree_mul_dividedColumn k i, h, mul_zero]
  · intro h
    simp [dividedColumn, h]

/-- When a direction has degree `1`, its divided column coincides with the matrix column. -/
theorem dividedColumn_of_degree_eq_one (d : ExchangeData 𝕂 row) {k : K}
    (h : (d.polynomial k).degree = 1) (i : I) :
    d.dividedColumn k i = d.exchange.matrix i k := by
  simp [dividedColumn, h]

/-! ### Predicates and binary data -/

/-- All exchange polynomials of `d` are normalized in the coefficient system `c`. -/
def IsNormalized (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, c.IsNormalized (d.polynomial k)

theorem isNormalized_iff (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) :
    d.IsNormalized c ↔ ∀ k, c.IsNormalized (d.polynomial k) :=
  Iff.rfl

/-- All exchange polynomials of `d` are equal to the binary polynomial `1 + T`. -/
def IsBinary (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, d.polynomial k = ExchangePolynomial.binary

theorem isBinary_iff (d : ExchangeData 𝕂 row) :
    d.IsBinary ↔ ∀ k, d.polynomial k = ExchangePolynomial.binary :=
  Iff.rfl

/-- All exchange polynomials of `d` have endpoint coefficients equal to `1`. -/
def IsEndpointOne (d : ExchangeData 𝕂 row) : Prop :=
  ∀ k, (d.polynomial k).IsEndpointOne

theorem isEndpointOne_iff (d : ExchangeData 𝕂 row) :
    d.IsEndpointOne ↔ ∀ k, (d.polynomial k).IsEndpointOne :=
  Iff.rfl

/-- Binary data have endpoint coefficients equal to `1`. -/
theorem IsBinary.isEndpointOne {d : ExchangeData 𝕂 row} (hd : d.IsBinary) : d.IsEndpointOne :=
  fun k ↦ hd k ▸ ExchangePolynomial.isEndpointOne_binary

/-- Build binary exchange data from an exchange matrix by attaching `1 + T` to every direction. -/
def ofBinary (B : ExchangeMatrix row) : ExchangeData 𝕂 row where
  exchange := B
  polynomial _ := ExchangePolynomial.binary
  degree_dvd _ _ := by simp

@[simp]
theorem ofBinary_exchange (B : ExchangeMatrix row) : (ofBinary (𝕂 := 𝕂) B).exchange = B :=
  (rfl)

@[simp]
theorem ofBinary_polynomial (B : ExchangeMatrix row) (k : K) :
    (ofBinary (𝕂 := 𝕂) B).polynomial k = ExchangePolynomial.binary :=
  (rfl)

@[simp]
theorem ofBinary_dividedColumn (B : ExchangeMatrix row) (k : K) (i : I) :
    (ofBinary (𝕂 := 𝕂) B).dividedColumn k i = B.matrix i k := by
  simp [dividedColumn]

@[simp]
theorem isBinary_ofBinary (B : ExchangeMatrix row) : (ofBinary (𝕂 := 𝕂) B).IsBinary :=
  fun _ ↦ rfl

theorem IsBinary.eq_ofBinary {d : ExchangeData 𝕂 row} (hd : d.IsBinary) :
    d = ofBinary d.exchange := by
  ext : 1
  · rfl
  · funext k
    exact hd k

/-! ### Scalar value at `1`, exchange exponents, and exchange numerators -/

/-- The scalar value `H_k(1) = ∑_{l=0}^{r_k} φ(h_{k,l}) ∈ R`. -/
def valueAtOne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) : R :=
  ∑ l ∈ Finset.range ((d.polynomial k).degree + 1), c.toScalar ((d.polynomial k).coeff l)

theorem valueAtOne_def (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.valueAtOne c k =
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1), c.toScalar ((d.polynomial k).coeff l) :=
  (rfl)

/-- For binary data, `H_k(1) = 2` in every direction. -/
theorem valueAtOne_of_isBinary (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row}
    (hd : d.IsBinary) (k : K) : d.valueAtOne c k = 2 := by
  rw [valueAtOne, hd k, ExchangePolynomial.binary_degree, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [one_add_one_eq_two]

/-- Pushing forward the scalar map applies it to `valueAtOne`. -/
@[simp]
theorem valueAtOne_mapScalar (c : CoefficientSystem 𝕂 R) (f : R →+* S)
    (d : ExchangeData 𝕂 row) (k : K) :
    d.valueAtOne (c.mapScalar f) k = f (d.valueAtOne c k) := by
  simp [valueAtOne, map_sum]

/-- The exponent `-e_k + l [β_k]₊ + (r_k - l) [-β_k]₊` of the `l`-th exchange summand. -/
noncomputable def exchangeExponent [Finite I] (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    I →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦
    (l : ℤ) * (d.dividedColumn k i)⁺ +
      (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i)⁻) -
    Finsupp.single (row k) 1

/-- The `row k`-coordinate of every exchange exponent in direction `k` is `-1`. -/
@[simp]
theorem exchangeExponent_apply_row_self [Finite I] (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    d.exchangeExponent k l (row k) = -1 := by
  simp [exchangeExponent]

/-- Away from `row k`, the `i`-coordinate of the `l`-th exchange exponent is
`l [β_{ik}]₊ + (r_k - l) [-β_{ik}]₊`. -/
theorem exchangeExponent_apply_of_ne [Finite I] (d : ExchangeData 𝕂 row) (k : K) (l : ℕ)
    {i : I} (hi : i ≠ row k) :
    d.exchangeExponent k l i =
      (l : ℤ) * (d.dividedColumn k i)⁺ +
        (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i)⁻ := by
  simp [exchangeExponent, Finsupp.single_eq_of_ne hi]

/-- On a zero column, every exchange exponent equals `-e_k`. -/
theorem exchangeExponent_of_col_eq_zero [Finite I] (d : ExchangeData 𝕂 row) (k : K)
    (hzero : ∀ i, d.exchange.matrix i k = 0) (l : ℕ) :
    d.exchangeExponent k l = -Finsupp.single (row k) 1 := by
  ext i
  by_cases hi : i = row k
  · subst hi
    simp
  · have hdiv : d.dividedColumn k i = 0 := (d.dividedColumn_eq_zero_iff k i).mpr (hzero i)
    simp [exchangeExponent_apply_of_ne d k l hi, hdiv, Finsupp.single_eq_of_ne hi]

/-- On a nonzero column, the exchange exponents for `0 ≤ l ≤ r_k` are pairwise distinct. -/
theorem exchangeExponent_injOn [Finite I] (d : ExchangeData 𝕂 row) (k : K)
    (hcol : ∃ i, d.exchange.matrix i k ≠ 0) :
    Set.InjOn (d.exchangeExponent k) {l | l ≤ (d.polynomial k).degree} := by
  intro l₁ hl₁ l₂ hl₂ heq
  obtain ⟨i, hi⟩ := hcol
  have hdiv : d.dividedColumn k i ≠ 0 := by
    rwa [ne_eq, d.dividedColumn_eq_zero_iff]
  have hne : i ≠ row k := by
    rintro rfl
    exact hdiv (d.dividedColumn_row_self k)
  have hcoord := congrArg (fun f : I →₀ ℤ ↦ f i) heq
  rw [d.exchangeExponent_apply_of_ne k l₁ hne, d.exchangeExponent_apply_of_ne k l₂ hne] at hcoord
  rcases lt_or_gt_of_ne hdiv with hlt | hgt
  · have hp : (d.dividedColumn k i)⁺ = 0 := posPart_eq_zero.mpr hlt.le
    have hn : (d.dividedColumn k i)⁻ = -d.dividedColumn k i := negPart_eq_neg.mpr hlt.le
    rw [hp, hn, mul_zero, mul_zero, zero_add, zero_add] at hcoord
    have hsub : ((d.polynomial k).degree - l₁ : ℕ) = (d.polynomial k).degree - l₂ :=
      Int.ofNat.inj (mul_right_cancel₀ (neg_ne_zero.mpr hdiv) hcoord)
    have hl₁' : l₁ ≤ (d.polynomial k).degree := hl₁
    have hl₂' : l₂ ≤ (d.polynomial k).degree := hl₂
    omega
  · have hp : (d.dividedColumn k i)⁺ = d.dividedColumn k i := posPart_eq_self.mpr hgt.le
    have hn : (d.dividedColumn k i)⁻ = 0 := negPart_eq_zero.mpr hgt.le
    rw [hp, hn, mul_zero, mul_zero, add_zero, add_zero] at hcoord
    exact Int.ofNat.inj (mul_right_cancel₀ hdiv hcoord)

/-- The *exchange numerator* `E_k ∈ LaurentRing R {i : I // i ≠ row k}` in direction `k`:
`∑_{l=0}^{r_k} φ(h_{k,l}) m_{k,+}^l m_{k,-}^{r_k - l}`. -/
noncomputable def exchangeNumerator [Finite I] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) : LaurentRing R {i : I // i ≠ row k} :=
  ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
    AddMonoidAlgebra.single
      (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
        (l : ℤ) * (d.dividedColumn k i.1)⁺ +
          (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i.1)⁻)
      (c.toScalar ((d.polynomial k).coeff l))

theorem exchangeNumerator_def [Finite I] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator c k =
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
        AddMonoidAlgebra.single
          (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
            (l : ℤ) * (d.dividedColumn k i.1)⁺ +
              (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i.1)⁻)
          (c.toScalar ((d.polynomial k).coeff l)) :=
  (rfl)

/-- The exchange numerator as a sum of products of powers of the positive and negative exchange
monomials `m_{k,+}` and `m_{k,-}`. -/
theorem exchangeNumerator_eq_sum_pow [Finite I] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator c k =
      let mPos : LaurentRing R {i : I // i ≠ row k} :=
        AddMonoidAlgebra.single
          (Finsupp.equivFunOnFinite.symm fun i ↦ (d.dividedColumn k i.1)⁺) 1
      let mNeg : LaurentRing R {i : I // i ≠ row k} :=
        AddMonoidAlgebra.single
          (Finsupp.equivFunOnFinite.symm fun i ↦ (d.dividedColumn k i.1)⁻) 1
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
        c.toScalar ((d.polynomial k).coeff l) •
          (mPos ^ l * mNeg ^ ((d.polynomial k).degree - l)) := by
  dsimp only [exchangeNumerator]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow, one_pow, one_pow,
    AddMonoidAlgebra.single_mul_single, one_mul, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  congr 1
  ext i
  simp

/-- The exchange numerator with its positive and negative monomials written explicitly as finite
products of integer powers of the variables `X_i` (`i ≠ row k`). -/
theorem exchangeNumerator_eq_sum_prod [Finite I] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) [Fintype {i : I // i ≠ row k}] :
    d.exchangeNumerator c k =
      let mPos : LaurentRing R {i : I // i ≠ row k} :=
        ∏ i : {i : I // i ≠ row k},
          ((LaurentRing.unitX i ^ (d.dividedColumn k i.1)⁺ :
            (LaurentRing R {i : I // i ≠ row k})ˣ) : LaurentRing R {i : I // i ≠ row k})
      let mNeg : LaurentRing R {i : I // i ≠ row k} :=
        ∏ i : {i : I // i ≠ row k},
          ((LaurentRing.unitX i ^ (d.dividedColumn k i.1)⁻ :
            (LaurentRing R {i : I // i ≠ row k})ˣ) : LaurentRing R {i : I // i ≠ row k})
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
        c.toScalar ((d.polynomial k).coeff l) •
          (mPos ^ l * mNeg ^ ((d.polynomial k).degree - l)) := by
  have hprod (f : {i : I // i ≠ row k} → ℤ) :
      (AddMonoidAlgebra.single (Finsupp.equivFunOnFinite.symm f) (1 : R) :
          LaurentRing R {i : I // i ≠ row k}) =
        ∏ i : {i : I // i ≠ row k},
          ((LaurentRing.unitX i ^ f i :
            (LaurentRing R {i : I // i ≠ row k})ˣ) : LaurentRing R {i : I // i ≠ row k}) := by
    rw [LaurentRing.single_eq_smul_prod, one_smul]
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ ↦ by simp)]
    simp
  rw [d.exchangeNumerator_eq_sum_pow c k]
  simp only [hprod]

/-- On a zero column, the exchange numerator is the constant `H_k(1)`. -/
theorem exchangeNumerator_of_col_eq_zero [Finite I] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) (hzero : ∀ i, d.exchange.matrix i k = 0) :
    d.exchangeNumerator c k = AddMonoidAlgebra.single 0 (d.valueAtOne c k) := by
  have hexp (l : ℕ) :
      (Finsupp.equivFunOnFinite.symm fun i : {i : I // i ≠ row k} ↦
        (l : ℤ) * (d.dividedColumn k i.1)⁺ +
          (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i.1)⁻) = 0 := by
    ext i
    have hdiv : d.dividedColumn k i.1 = 0 := (d.dividedColumn_eq_zero_iff k i.1).mpr (hzero i.1)
    simp [hdiv]
  simp only [exchangeNumerator, valueAtOne, hexp]
  exact (map_sum (AddMonoidAlgebra.singleZeroRingHom :
    R →+* LaurentRing R {i : I // i ≠ row k}) _ _).symm

/-- Pushing forward the scalar map applies `AddMonoidAlgebra.mapRingHom` to the exchange
numerator. -/
@[simp]
theorem exchangeNumerator_mapScalar [Finite I] (c : CoefficientSystem 𝕂 R) (f : R →+* S)
    (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator (c.mapScalar f) k =
      AddMonoidAlgebra.mapRingHom _ f (d.exchangeNumerator c k) := by
  simp [exchangeNumerator, map_sum]

/-- Multiplying the embedded exchange numerator by `X (row k)⁻¹` recovers the sum over
`exchangeExponent`. -/
theorem inv_unitX_mul_rename_exchangeNumerator [Finite I] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (((LaurentRing.unitX (row k))⁻¹ : (LaurentRing R I)ˣ) : LaurentRing R I) *
        LaurentRing.rename Subtype.val (d.exchangeNumerator c k) =
      ∑ l ∈ Finset.range ((d.polynomial k).degree + 1),
        AddMonoidAlgebra.single (d.exchangeExponent k l)
          (c.toScalar ((d.polynomial k).coeff l)) := by
  classical
  simp only [exchangeNumerator, map_sum, Finset.mul_sum, LaurentRing.rename_single,
    LaurentRing.val_inv_unitX, AddMonoidAlgebra.single_mul_single, one_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  ext i
  by_cases hi : i = row k
  · subst hi
    have hnot : (Finsupp.mapDomain Subtype.val
        (Finsupp.equivFunOnFinite.symm fun j : {j : I // j ≠ row k} ↦
          (l : ℤ) * (d.dividedColumn k j.1)⁺ +
            (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k j.1)⁻)) (row k) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)
    simp [hnot]
  · have hval : (Finsupp.mapDomain Subtype.val
        (Finsupp.equivFunOnFinite.symm fun j : {j : I // j ≠ row k} ↦
          (l : ℤ) * (d.dividedColumn k j.1)⁺ +
            (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k j.1)⁻)) i =
        (l : ℤ) * (d.dividedColumn k i)⁺ +
          (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i)⁻ := by
      have hsub := Finsupp.mapDomain_apply_of_injective Subtype.val_injective
        (Finsupp.equivFunOnFinite.symm fun j : {j : I // j ≠ row k} ↦
          (l : ℤ) * (d.dividedColumn k j.1)⁺ +
            (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k j.1)⁻)
        ⟨i, hi⟩
      simpa using hsub
    have h0 : (Finsupp.single (row k) (1 : ℤ)) i = 0 := Finsupp.single_eq_of_ne hi
    simp [exchangeExponent_apply_of_ne d k l hi, hval, h0]

/-! ### Reindexing -/

/-- Reindex exchange data along equivalences of the row and column index types that commute with
the mutable embeddings. -/
def reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    ExchangeData 𝕂 row ≃ ExchangeData 𝕂 row' where
  toFun d :=
    { exchange := ExchangeMatrix.reindex eI eK h d.exchange
      polynomial := d.polynomial ∘ eK.symm
      degree_dvd := fun i k ↦ by simpa using d.degree_dvd (eI.symm i) (eK.symm k) }
  invFun d :=
    { exchange := (ExchangeMatrix.reindex eI eK h).symm d.exchange
      polynomial := d.polynomial ∘ eK
      degree_dvd := fun i k ↦ by simpa using d.degree_dvd (eI i) (eK k) }
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
    (d : ExchangeData 𝕂 row) (k : K') :
    (reindex eI eK h d).polynomial k = d.polynomial (eK.symm k) :=
  (rfl)

@[simp]
theorem reindex_dividedColumn (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k : K') (i : I') :
    (reindex eI eK h d).dividedColumn k i = d.dividedColumn (eK.symm k) (eI.symm i) := by
  simp [dividedColumn]

@[simp]
theorem reindex_symm (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) :
    (reindex (𝕂 := 𝕂) eI eK h).symm =
      reindex eI.symm eK.symm (fun k ↦ by rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]) := by
  ext d : 2
  · ext i j <;> simp [reindex]
  · funext k
    rfl

@[simp]
theorem reindex_refl (h : ∀ k, Equiv.refl I (row k) = row (Equiv.refl K k)) :
    reindex (𝕂 := 𝕂) (Equiv.refl I) (Equiv.refl K) h = Equiv.refl (ExchangeData 𝕂 row) := by
  ext d : 2
  · simp only [reindex_exchange, ExchangeMatrix.reindex_refl, Equiv.refl_apply]
  · funext k
    rfl

@[simp]
theorem reindex_trans (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k)) :
    (reindex (𝕂 := 𝕂) eI eK h).trans (reindex eI' eK' h') =
      reindex (eI.trans eI') (eK.trans eK') fun k ↦ by
        rw [Equiv.trans_apply, Equiv.trans_apply, h, h'] := by
  ext d : 2
  · simp only [Equiv.trans_apply, reindex_exchange, ExchangeMatrix.reindex_reindex]
  · funext k
    rfl

@[simp]
theorem reindex_reindex (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (eI' : I' ≃ I'') (eK' : K' ≃ K'') (h' : ∀ k, eI' (row' k) = row'' (eK' k))
    (d : ExchangeData 𝕂 row) :
    reindex eI' eK' h' (reindex eI eK h d) =
      reindex (eI.trans eI') (eK.trans eK') (fun k ↦ by
        rw [Equiv.trans_apply, Equiv.trans_apply, h, h']) d := by
  simpa only [Equiv.trans_apply] using
    congrArg (fun e : ExchangeData 𝕂 row ≃ ExchangeData 𝕂 row'' ↦ e d)
      (reindex_trans eI eK h eI' eK' h')

@[simp]
theorem isNormalized_reindex_iff (c : CoefficientSystem 𝕂 R) (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).IsNormalized c ↔ d.IsNormalized c :=
  ⟨fun hd k ↦ by simpa using hd (eK k), fun hd k ↦ hd (eK.symm k)⟩

@[simp]
theorem isBinary_reindex_iff (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).IsBinary ↔ d.IsBinary :=
  ⟨fun hd k ↦ by simpa using hd (eK k), fun hd k ↦ hd (eK.symm k)⟩

@[simp]
theorem valueAtOne_reindex (c : CoefficientSystem 𝕂 R) (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) (k : K) :
    (reindex eI eK h d).valueAtOne c (eK k) = d.valueAtOne c k := by
  simp [valueAtOne]

/-- Reindexing pushes forward exchange exponents along `eI`. -/
theorem exchangeExponent_reindex [Finite I] [Finite I'] (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    (reindex eI eK h d).exchangeExponent (eK k) l =
      (d.exchangeExponent k l).mapDomain eI := by
  ext i
  rw [← eI.apply_symm_apply i, Finsupp.mapDomain_apply_of_injective eI.injective,
    eI.apply_symm_apply]
  by_cases hi : eI.symm i = row k
  · have hi' : i = row' (eK k) := by rw [← h k, ← hi, eI.apply_symm_apply]
    rw [hi, hi']
    simp
  · have hi' : i ≠ row' (eK k) :=
      fun heq ↦ hi (eI.injective (by rw [eI.apply_symm_apply, heq, h k]))
    simp [exchangeExponent_apply_of_ne _ _ _ hi, exchangeExponent_apply_of_ne _ _ _ hi']

/-- Reindexing transports the exchange numerator along the induced renaming of the non-mutated
variables. -/
theorem exchangeNumerator_reindex [Finite I] [Finite I'] (c : CoefficientSystem 𝕂 R)
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k : K) :
    LaurentRing.renameEquiv R
        (Equiv.subtypeEquiv eI fun i ↦ by
          rw [← h k]
          exact eI.injective.ne_iff.symm)
        (d.exchangeNumerator c k) =
      (reindex eI eK h d).exchangeNumerator c (eK k) := by
  set eSub : {j : I // j ≠ row k} ≃ {j : I' // j ≠ row' (eK k)} :=
    Equiv.subtypeEquiv eI fun j ↦ by
      rw [← h k]
      exact eI.injective.ne_iff.symm
  simp only [exchangeNumerator, map_sum, LaurentRing.renameEquiv_apply, LaurentRing.rename_single,
    reindex_polynomial, Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  ext ⟨i, hi⟩
  have hi' : eI.symm i ≠ row k := fun heq ↦ hi (by rw [← h k, ← heq, eI.apply_symm_apply])
  have hsub := Finsupp.mapDomain_apply_of_injective eSub.injective
    (Finsupp.equivFunOnFinite.symm fun j : {j : I // j ≠ row k} ↦
      (l : ℤ) * (d.dividedColumn k j.1)⁺ +
        (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k j.1)⁻)
    ⟨eI.symm i, hi'⟩
  simpa [eSub] using hsub

/-! ### Coefficientwise pushforward -/

/-- Push forward exchange data coefficientwise along a `MonoidWithZeroHom`, keeping the underlying
exchange matrix unchanged. -/
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
theorem map_dividedColumn (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) (i : I) :
    (d.map ψ).dividedColumn k i = d.dividedColumn k i := by
  simp [dividedColumn]

@[simp]
theorem map_id (d : ExchangeData 𝕂 row) : d.map (MonoidWithZeroHom.id 𝕂) = d := by
  ext : 1
  · rfl
  · funext k
    simp

@[simp]
theorem map_comp (ψ₂ : 𝕂' →*₀ 𝕂'') (ψ₁ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) :
    d.map (ψ₂.comp ψ₁) = (d.map ψ₁).map ψ₂ := by
  ext : 1
  · rfl
  · funext k
    simp

@[simp]
theorem map_reindex (ψ : 𝕂 →*₀ 𝕂') (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) :
    (reindex eI eK h d).map ψ = reindex eI eK h (d.map ψ) := by
  ext : 1
  · rfl
  · funext k
    rfl

@[simp]
theorem map_exchangeExponent [Finite I] (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    (d.map ψ).exchangeExponent k l = d.exchangeExponent k l := by
  simp [exchangeExponent]

/-- A homomorphism of coefficient systems preserves normalized exchange data. -/
theorem IsNormalized.map {c₁ : CoefficientSystem 𝕂 R} {c₂ : CoefficientSystem 𝕂' R}
    (ψ : c₁.Hom c₂) {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c₁) :
    (d.map ψ.toMonoidWithZeroHom).IsNormalized c₂ :=
  fun k ↦ ψ.isNormalized_map (hd k)

/-- A homomorphism of coefficient systems preserves `valueAtOne`. -/
@[simp]
theorem valueAtOne_map {c₁ : CoefficientSystem 𝕂 R} {c₂ : CoefficientSystem 𝕂' R}
    (ψ : c₁.Hom c₂) (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ.toMonoidWithZeroHom).valueAtOne c₂ k = d.valueAtOne c₁ k := by
  simp [valueAtOne]

/-- A homomorphism of coefficient systems preserves the exchange numerator. -/
@[simp]
theorem exchangeNumerator_map [Finite I] {c₁ : CoefficientSystem 𝕂 R} {c₂ : CoefficientSystem 𝕂' R}
    (ψ : c₁.Hom c₂) (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ.toMonoidWithZeroHom).exchangeNumerator c₂ k = d.exchangeNumerator c₁ k := by
  simp [exchangeNumerator]

end ExchangeData

end TauCeti
