/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeData.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# Formal exchange exponents and numerators

From exchange data `d : ExchangeData 𝕂 row` and a coefficient system `c : CoefficientSystem 𝕂 R`,
each mutable direction `k : K` determines two formal Laurent objects prior to any choice of ambient
field or cluster chart:

* the formal Laurent exponents `d.exchangeExponent k l : I →₀ ℤ` (`0 ≤ l ≤ r_k`), equal to `-1` at
  `row k` and to `l * (β_k i)⁺ + (r_k - l) * (β_k i)⁻` at every `i ≠ row k`, where
  `β_k i = b_{ik} / r_k` is the divided column;
* the formal exchange numerator `d.exchangeNumerator c k` in the Laurent ring
  `LaurentRing R {i : I // i ≠ row k}` on the remaining indices, built from the positive-part and
  negative-part monomials `d.posMonomial R k` and `d.negMonomial R k`:
  $$P_k = \sum_{l = 0}^{r_k} \varphi(h_{k,l}) (M_k^+)^l (M_k^-)^{r_k - l}.$$

Under mutation at `k`, the exchange polynomial `H_k` is reversed while the divided column `β_k` is
negated, swapping `M_k^+` and `M_k^-`. Consequently `d.exchangeNumerator c k` is invariant under
`d.mutation c k` (`exchangeNumerator_mutation_self`). Embedding `LaurentRing R {i : I // i ≠ row k}`
into `LaurentRing R I` and multiplying by `(unitX (row k))⁻¹` recovers the formal sum of the
monomials `single (d.exchangeExponent k l) (φ(h_{k,l}))`
(`rename_exchangeNumerator_mul_inv_unitX`).

This formal layer also separates the two regimes of cluster exchange:
* when column `k` has a nonzero entry, `d.exchangeExponent k` is injective on `{0, …, r_k}`
  (`injOn_exchangeExponent_of_ne_zero`), so no two terms of the exchange relation share a Laurent
  monomial and `d.exchangeNumerator c k ≠ 0` over any nontrivial `R`
  (`exchangeNumerator_ne_zero_of_ne_zero`);
* when column `k` is identically zero, `d.exchangeNumerator c k` collapses to the constant scalar
  `algebraMap R _ (d.valueAtOne c k)` (`exchangeNumerator_of_column_eq_zero`), which is a unit in
  the Laurent ring if and only if `d.valueAtOne c k` is a unit in `R`
  (`isUnit_exchangeNumerator_of_column_eq_zero_iff`).

## Main definitions

* `TauCeti.ExchangeData.exchangeExponent`: formal Laurent exponent `α_{k,l} ∈ I →₀ ℤ`.
* `TauCeti.ExchangeData.posExponent`, `TauCeti.ExchangeData.negExponent`: positive-part and
  negative-part divided-column exponents on `{i : I // i ≠ row k}`.
* `TauCeti.ExchangeData.posMonomial`, `TauCeti.ExchangeData.negMonomial`: the corresponding formal
  monomials in `LaurentRing R {i : I // i ≠ row k}`.
* `TauCeti.ExchangeData.exchangeNumerator`: the formal exchange numerator in
  `LaurentRing R {i : I // i ≠ row k}`.

## Main results

* `TauCeti.ExchangeData.injOn_exchangeExponent_of_ne_zero`: when column `k` is nonzero, the formal
  exponents `d.exchangeExponent k l` for `l ≤ r_k` are pairwise distinct.
* `TauCeti.ExchangeData.exchangeNumerator_mutation_self`: `d.exchangeNumerator c k` is invariant
  under `d.mutation c k`.
* `TauCeti.ExchangeData.rename_exchangeNumerator_mul_inv_unitX`: multiplying the embedded exchange
  numerator by `(unitX (row k))⁻¹` yields `∑ l, single (d.exchangeExponent k l) (φ(h_{k,l}))`.
* `TauCeti.ExchangeData.exchangeNumerator_ne_zero_of_ne_zero`: a nonzero column has nonzero formal
  exchange numerator over any nontrivial commutative semiring.
* `TauCeti.ExchangeData.exchangeNumerator_of_column_eq_zero` and
  `TauCeti.ExchangeData.isUnit_exchangeNumerator_of_column_eq_zero_iff`: on a zero column, the
  formal exchange numerator is the scalar `H_k(1)`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §2 and §4.
* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
* M. Gekhtman, M. Shapiro and A. Vainshtein, *Generalized cluster structure on the Drinfeld double
  of $\mathrm{GL}_n$*, C. R. Math. Acad. Sci. Paris 354 (2016), 345–349.
-/

public section

namespace TauCeti

namespace ExchangeData

section Exponents

variable {𝕂 𝕂' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  {R : Type*} [CommSemiring R] {I I' K K' : Type*} {row : K ↪ I}

/-- The formal Laurent exponent `α_{k,l} ∈ I →₀ ℤ` of the `l`-th term of the exchange relation in
direction `k`: `-1` at `row k`, and `l * (β_k i)⁺ + (r_k - l) * (β_k i)⁻` at every `i ≠ row k`,
where `β_k i = b_{ik} / r_k` is the divided column. -/
noncomputable def exchangeExponent [Finite I] [DecidableEq I] (d : ExchangeData 𝕂 row)
    (k : K) (l : ℕ) : I →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i ↦
    if i = row k then -1
    else l * (d.dividedColumn k i)⁺ + ((d.polynomial k).degree - l : ℕ) * (d.dividedColumn k i)⁻

theorem exchangeExponent_apply [Finite I] [DecidableEq I] (d : ExchangeData 𝕂 row)
    (k : K) (l : ℕ) (i : I) :
    d.exchangeExponent k l i =
      if i = row k then -1
      else l * (d.dividedColumn k i)⁺ +
        ((d.polynomial k).degree - l : ℕ) * (d.dividedColumn k i)⁻ :=
  (rfl)

@[simp]
theorem exchangeExponent_apply_row_self [Finite I] [DecidableEq I] (d : ExchangeData 𝕂 row)
    (k : K) (l : ℕ) :
    d.exchangeExponent k l (row k) = -1 := by
  simp [exchangeExponent_apply]

theorem exchangeExponent_apply_of_ne [Finite I] [DecidableEq I] (d : ExchangeData 𝕂 row)
    (k : K) (l : ℕ) {i : I} (hi : i ≠ row k) :
    d.exchangeExponent k l i =
      l * (d.dividedColumn k i)⁺ + ((d.polynomial k).degree - l : ℕ) * (d.dividedColumn k i)⁻ := by
  simp [exchangeExponent_apply, hi]

theorem exchangeExponent_of_column_eq_zero [Finite I] [DecidableEq I] (d : ExchangeData 𝕂 row)
    {k : K} (h0 : ∀ i, d.exchange.matrix i k = 0) (l : ℕ) :
    d.exchangeExponent k l = Finsupp.single (row k) (-1) := by
  ext i
  by_cases hi : i = row k
  · subst hi
    simp
  · have hb : d.dividedColumn k i = 0 := (d.dividedColumn_eq_zero_iff k i).mpr (h0 i)
    simp [exchangeExponent_apply_of_ne d k l hi, hb, hi]

/-- When column `k` has a nonzero entry, the formal Laurent exponents `d.exchangeExponent k l` for
`0 ≤ l ≤ r_k` are pairwise distinct. -/
theorem injOn_exchangeExponent_of_ne_zero [Finite I] [DecidableEq I] (d : ExchangeData 𝕂 row)
    {k : K} {i : I} (hi : d.exchange.matrix i k ≠ 0) :
    Set.InjOn (d.exchangeExponent k) {l | l ≤ (d.polynomial k).degree} := by
  intro l₁ hl₁ l₂ hl₂ h
  have hβ : d.dividedColumn k i ≠ 0 := (d.dividedColumn_eq_zero_iff k i).not.mpr hi
  have hi' : i ≠ row k := fun heq ↦ hβ (heq ▸ d.dividedColumn_row_self k)
  have eval_i := DFunLike.congr_fun h i
  rw [exchangeExponent_apply_of_ne d k l₁ hi', exchangeExponent_apply_of_ne d k l₂ hi',
    Nat.cast_sub hl₁, Nat.cast_sub hl₂] at eval_i
  have hsub : ((l₁ : ℤ) - l₂) * ((d.dividedColumn k i)⁺ - (d.dividedColumn k i)⁻) = 0 := by
    linear_combination eval_i
  rw [posPart_sub_negPart] at hsub
  rcases mul_eq_zero.mp hsub with hl | hβ0
  · omega
  · exact absurd hβ0 hβ

theorem exchangeExponent_val_injective_of_ne_zero [Finite I] [DecidableEq I]
    (d : ExchangeData 𝕂 row) {k : K} {i : I} (hi : d.exchange.matrix i k ≠ 0) :
    Function.Injective (fun l : Fin ((d.polynomial k).degree + 1) ↦
      d.exchangeExponent k l.val) := by
  intro l₁ l₂ h
  ext
  exact d.injOn_exchangeExponent_of_ne_zero hi (Nat.lt_succ_iff.mp l₁.isLt)
    (Nat.lt_succ_iff.mp l₂.isLt) h

/-- Mutating at `k` reverses the order of the formal exchange exponents `α_{k,0}, …, α_{k,r_k}`. -/
theorem exchangeExponent_mutation_self [Finite I] [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) {l : ℕ}
    (hl : l ≤ (d.polynomial k).degree) :
    (d.mutation c k).exchangeExponent k ((d.polynomial k).degree - l) =
      d.exchangeExponent k l := by
  ext i
  by_cases hi : i = row k
  · simp [hi]
  · simp [exchangeExponent_apply_of_ne _ k _ hi, posPart_neg, negPart_neg,
      Nat.sub_sub_self hl, add_comm]

@[simp]
theorem exchangeExponent_map [Finite I] [DecidableEq I] (ψ : 𝕂 →*₀ 𝕂')
    (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    (d.map ψ).exchangeExponent k l = d.exchangeExponent k l := by
  ext i
  simp [exchangeExponent_apply]

theorem exchangeExponent_reindex [Finite I] [Finite I'] [DecidableEq I] [DecidableEq I']
    {row' : K' ↪ I'} (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    (reindex eI eK h d).exchangeExponent (eK k) l =
      Finsupp.domCongr eI (d.exchangeExponent k l) := by
  ext i'
  have hi : (i' = row' (eK k)) ↔ (eI.symm i' = row k) := by
    rw [← h k, ← Equiv.symm_apply_eq]
  simp [exchangeExponent_apply, hi]

end Exponents

/-! ### Formal exchange monomials and numerators -/

section Numerator

variable {𝕂 𝕂' : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂']
  {I K : Type*} {row : K ↪ I}

/-- The positive-part divided-column exponent `i ↦ (β_k i)⁺` on `{i : I // i ≠ row k}`. -/
noncomputable def posExponent [Finite I] (d : ExchangeData 𝕂 row) (k : K) :
    {i : I // i ≠ row k} →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (d.dividedColumn k i.val)⁺

/-- The negative-part divided-column exponent `i ↦ (β_k i)⁻` on `{i : I // i ≠ row k}`. -/
noncomputable def negExponent [Finite I] (d : ExchangeData 𝕂 row) (k : K) :
    {i : I // i ≠ row k} →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (d.dividedColumn k i.val)⁻

@[simp]
theorem posExponent_apply [Finite I] (d : ExchangeData 𝕂 row) (k : K)
    (i : {i : I // i ≠ row k}) :
    d.posExponent k i = (d.dividedColumn k i.val)⁺ :=
  (rfl)

@[simp]
theorem negExponent_apply [Finite I] (d : ExchangeData 𝕂 row) (k : K)
    (i : {i : I // i ≠ row k}) :
    d.negExponent k i = (d.dividedColumn k i.val)⁻ :=
  (rfl)

@[simp]
theorem posExponent_mutation_self {R : Type*} [CommSemiring R] [Finite I] [DecidableEq I]
    [DecidableEq K] (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).posExponent k = d.negExponent k := by
  ext i
  simp [posPart_neg]

@[simp]
theorem negExponent_mutation_self {R : Type*} [CommSemiring R] [Finite I] [DecidableEq I]
    [DecidableEq K] (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).negExponent k = d.posExponent k := by
  ext i
  simp [negPart_neg]

@[simp]
theorem posExponent_map [Finite I] (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ).posExponent k = d.posExponent k := by
  ext i
  simp

@[simp]
theorem negExponent_map [Finite I] (ψ : 𝕂 →*₀ 𝕂') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ).negExponent k = d.negExponent k := by
  ext i
  simp

theorem posExponent_of_column_eq_zero [Finite I] (d : ExchangeData 𝕂 row) {k : K}
    (h0 : ∀ i, d.exchange.matrix i k = 0) :
    d.posExponent k = 0 := by
  ext i
  have hb : d.dividedColumn k i.val = 0 := (d.dividedColumn_eq_zero_iff k i.val).mpr (h0 i.val)
  simp [hb]

theorem negExponent_of_column_eq_zero [Finite I] (d : ExchangeData 𝕂 row) {k : K}
    (h0 : ∀ i, d.exchange.matrix i k = 0) :
    d.negExponent k = 0 := by
  ext i
  have hb : d.dividedColumn k i.val = 0 := (d.dividedColumn_eq_zero_iff k i.val).mpr (h0 i.val)
  simp [hb]

/-- Pushing `l • posExponent + (r_k - l) • negExponent` forward to `I →₀ ℤ` and subtracting the
`row k` basis vector recovers `d.exchangeExponent k l`. -/
theorem mapDomain_posExponent_add_negExponent [Finite I] [DecidableEq I]
    (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    Finsupp.mapDomain (Subtype.val : {i : I // i ≠ row k} → I)
        (l • d.posExponent k + ((d.polynomial k).degree - l) • d.negExponent k) +
      Finsupp.single (row k) (-1) = d.exchangeExponent k l := by
  ext i
  by_cases hi : i = row k
  · subst hi
    have hnot : row k ∉ Set.range (Subtype.val : {j : I // j ≠ row k} → I) := by
      rintro ⟨⟨j, hj⟩, rfl⟩
      exact hj rfl
    simp [Finsupp.mapDomain_of_notMem_range _ _ hnot]
  · have hmap : Finsupp.mapDomain (Subtype.val : {j : I // j ≠ row k} → I)
        (l • d.posExponent k + ((d.polynomial k).degree - l) • d.negExponent k) i =
        (l • d.posExponent k + ((d.polynomial k).degree - l) • d.negExponent k) ⟨i, hi⟩ :=
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨i, hi⟩
    simp [hmap, exchangeExponent_apply_of_ne d k l hi, hi, nsmul_eq_mul]

/-- The positive-part monomial `M_k^+ = ∏_{i ≠ row k} X_i^{(β_k i)⁺}` in
`LaurentRing R {i : I // i ≠ row k}`. -/
noncomputable def posMonomial (R : Type*) [Semiring R] [Finite I] (d : ExchangeData 𝕂 row)
    (k : K) : LaurentRing R {i : I // i ≠ row k} :=
  AddMonoidAlgebra.single (d.posExponent k) 1

/-- The negative-part monomial `M_k^- = ∏_{i ≠ row k} X_i^{(β_k i)⁻}` in
`LaurentRing R {i : I // i ≠ row k}`. -/
noncomputable def negMonomial (R : Type*) [Semiring R] [Finite I] (d : ExchangeData 𝕂 row)
    (k : K) : LaurentRing R {i : I // i ≠ row k} :=
  AddMonoidAlgebra.single (d.negExponent k) 1

theorem posMonomial_def (R : Type*) [Semiring R] [Finite I] (d : ExchangeData 𝕂 row) (k : K) :
    d.posMonomial R k = AddMonoidAlgebra.single (d.posExponent k) 1 :=
  (rfl)

theorem negMonomial_def (R : Type*) [Semiring R] [Finite I] (d : ExchangeData 𝕂 row) (k : K) :
    d.negMonomial R k = AddMonoidAlgebra.single (d.negExponent k) 1 :=
  (rfl)

@[simp]
theorem posMonomial_mutation_self (R R₀ : Type*) [Semiring R] [CommSemiring R₀] [Finite I]
    [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R₀) (d : ExchangeData 𝕂 row)
    (k : K) :
    (d.mutation c k).posMonomial R k = d.negMonomial R k := by
  simp [posMonomial_def, negMonomial_def]

@[simp]
theorem negMonomial_mutation_self (R R₀ : Type*) [Semiring R] [CommSemiring R₀] [Finite I]
    [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R₀) (d : ExchangeData 𝕂 row)
    (k : K) :
    (d.mutation c k).negMonomial R k = d.posMonomial R k := by
  simp [posMonomial_def, negMonomial_def]

@[simp]
theorem posMonomial_map (R : Type*) [Semiring R] [Finite I] (ψ : 𝕂 →*₀ 𝕂')
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ).posMonomial R k = d.posMonomial R k := by
  simp [posMonomial_def]

@[simp]
theorem negMonomial_map (R : Type*) [Semiring R] [Finite I] (ψ : 𝕂 →*₀ 𝕂')
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.map ψ).negMonomial R k = d.negMonomial R k := by
  simp [negMonomial_def]

theorem posMonomial_of_column_eq_zero (R : Type*) [Semiring R] [Finite I]
    (d : ExchangeData 𝕂 row) {k : K} (h0 : ∀ i, d.exchange.matrix i k = 0) :
    d.posMonomial R k = 1 := by
  rw [posMonomial_def, posExponent_of_column_eq_zero d h0, ← AddMonoidAlgebra.one_def]

theorem negMonomial_of_column_eq_zero (R : Type*) [Semiring R] [Finite I]
    (d : ExchangeData 𝕂 row) {k : K} (h0 : ∀ i, d.exchange.matrix i k = 0) :
    d.negMonomial R k = 1 := by
  rw [negMonomial_def, negExponent_of_column_eq_zero d h0, ← AddMonoidAlgebra.one_def]

/-- The formal exchange numerator
`P_k = ∑_{l=0}^{r_k} φ(h_{k,l}) (M_k^+)^l (M_k^-)^{r_k - l}` in
`LaurentRing R {i : I // i ≠ row k}`. -/
noncomputable def exchangeNumerator {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    LaurentRing R {i : I // i ≠ row k} :=
  ∑ l : Fin ((d.polynomial k).degree + 1),
    c.toScalar ((d.polynomial k).coeff l) •
      (d.posMonomial R k ^ l.val * d.negMonomial R k ^ ((d.polynomial k).degree - l.val))

theorem exchangeNumerator_def {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator c k =
      ∑ l : Fin ((d.polynomial k).degree + 1),
        c.toScalar ((d.polynomial k).coeff l) •
          (d.posMonomial R k ^ l.val * d.negMonomial R k ^ ((d.polynomial k).degree - l.val)) :=
  (rfl)

theorem exchangeNumerator_eq_sum_single {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator c k =
      ∑ l : Fin ((d.polynomial k).degree + 1),
        AddMonoidAlgebra.single
          (l.val • d.posExponent k + ((d.polynomial k).degree - l.val) • d.negExponent k)
          (c.toScalar ((d.polynomial k).coeff l)) := by
  rw [exchangeNumerator_def]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp [posMonomial_def, negMonomial_def]

/-- The formal exchange numerator in direction `k` is invariant under state mutation at `k`. -/
@[simp]
theorem exchangeNumerator_mutation_self {R : Type*} [CommSemiring R] [Finite I] [DecidableEq I]
    [DecidableEq K] (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchangeNumerator c k = d.exchangeNumerator c k := by
  rw [exchangeNumerator_def, exchangeNumerator_def]
  let e : Fin (((d.mutation c k).polynomial k).degree + 1) ≃
      Fin ((d.polynomial k).degree + 1) :=
    (finCongr (by simp)).trans Fin.revPerm
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hcoeff : ((d.mutation c k).polynomial k).coeff l =
      (d.polynomial k).coeff (e l) := by
    rw [ExchangePolynomial.coeff_eq_of_eq (congrFun (d.mutation_polynomial c k) k) l,
      coeff_mutatedPolynomial_self]
    rfl
  have hdeg : ((d.mutation c k).polynomial k).degree = (d.polynomial k).degree := by simp
  have hval : (e l).val = (d.polynomial k).degree - l.val := by
    simp [e, Fin.val_rev]
  have hpow : ((d.mutation c k).polynomial k).degree - l.val = (e l).val := by
    omega
  have hsub : (d.polynomial k).degree - (e l).val = l.val := by
    omega
  rw [hcoeff, posMonomial_mutation_self, negMonomial_mutation_self, hpow, hsub, mul_comm]

/-- Embedding the formal exchange numerator into `LaurentRing R I` and multiplying by
`(unitX (row k))⁻¹` produces the formal sum of `single (d.exchangeExponent k l) (φ(h_{k,l}))`. -/
theorem rename_exchangeNumerator_mul_inv_unitX {R : Type*} [CommSemiring R] [Finite I]
    [DecidableEq I] (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    LaurentRing.rename Subtype.val (d.exchangeNumerator c k) *
      (((LaurentRing.unitX (row k))⁻¹ : (LaurentRing R I)ˣ) : LaurentRing R I) =
      ∑ l : Fin ((d.polynomial k).degree + 1),
        AddMonoidAlgebra.single (d.exchangeExponent k l.val)
          (c.toScalar ((d.polynomial k).coeff l)) := by
  rw [exchangeNumerator_eq_sum_single, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [LaurentRing.rename_single, LaurentRing.val_inv_unitX, AddMonoidAlgebra.single_mul_single,
    mul_one, mapDomain_posExponent_add_negExponent]

/-- When column `k` is nonzero, the `l`-th coefficient of the formal exchange right-hand side at
exponent `d.exchangeExponent k l` is `φ(h_{k,l})` with no cancellation between terms. -/
theorem coeff_rename_exchangeNumerator_mul_inv_unitX_of_ne_zero {R : Type*} [CommSemiring R]
    [Finite I] [DecidableEq I] (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    {k : K} {i : I} (hi : d.exchange.matrix i k ≠ 0)
    (l : Fin ((d.polynomial k).degree + 1)) :
    (LaurentRing.rename Subtype.val (d.exchangeNumerator c k) *
        (((LaurentRing.unitX (row k))⁻¹ : (LaurentRing R I)ˣ) : LaurentRing R I)).coeff
      (d.exchangeExponent k l.val) = c.toScalar ((d.polynomial k).coeff l) := by
  rw [rename_exchangeNumerator_mul_inv_unitX, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Finset.sum_eq_single l]
  · simp
  · intro m _ hml
    have hne : d.exchangeExponent k m.val ≠ d.exchangeExponent k l.val :=
      (d.exchangeExponent_val_injective_of_ne_zero hi).ne hml
    simp [hne]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- Over any nontrivial commutative semiring `R`, a nonzero column has nonzero formal exchange
numerator. -/
theorem exchangeNumerator_ne_zero_of_ne_zero {R : Type*} [CommSemiring R] [Nontrivial R]
    [Finite I] (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    {k : K} {i : I} (hi : d.exchange.matrix i k ≠ 0) :
    d.exchangeNumerator c k ≠ 0 := by
  classical
  intro hzero
  have hc := d.coeff_rename_exchangeNumerator_mul_inv_unitX_of_ne_zero c hi 0
  simp [hzero] at hc
  exact ((d.polynomial k).isUnit_coeff_zero.map c.toScalar).ne_zero hc.symm

/-- On a zero column, the formal exchange numerator collapses to the scalar `H_k(1)`. -/
theorem exchangeNumerator_of_column_eq_zero {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) {k : K}
    (h0 : ∀ i, d.exchange.matrix i k = 0) :
    d.exchangeNumerator c k =
      algebraMap R (LaurentRing R {i : I // i ≠ row k}) (d.valueAtOne c k) := by
  simp [exchangeNumerator_def, posMonomial_of_column_eq_zero R d h0,
    negMonomial_of_column_eq_zero R d h0, ← Algebra.algebraMap_eq_smul_one, valueAtOne_def]

/-- On a zero column, the formal exchange numerator is a unit in the Laurent ring if and only if
`d.valueAtOne c k` is a unit in `R`. -/
theorem isUnit_exchangeNumerator_of_column_eq_zero_iff {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) {k : K}
    (h0 : ∀ i, d.exchange.matrix i k = 0) :
    IsUnit (d.exchangeNumerator c k) ↔ IsUnit (d.valueAtOne c k) := by
  rw [exchangeNumerator_of_column_eq_zero c d h0]
  refine ⟨fun hu ↦ ?_, IsUnit.map (algebraMap R _)⟩
  let ev : LaurentRing R {i : I // i ≠ row k} →ₐ[R] R :=
    LaurentRing.aeval fun _ ↦ (1 : Rˣ)
  have hev : ev (algebraMap R _ (d.valueAtOne c k)) = d.valueAtOne c k := by
    simpa using ev.commutes (d.valueAtOne c k)
  exact hev ▸ hu.map ev.toMonoidHom

/-- For a binomial exchange polynomial `1 + y T`, the formal exchange numerator reduces to the
classical Fomin–Zelevinsky binomial `M_k^- + φ(y) • M_k^+`. -/
theorem exchangeNumerator_of_binomial {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) {k : K} (y : 𝕂ˣ)
    (hk : d.polynomial k = ExchangePolynomial.binomial y) :
    d.exchangeNumerator c k =
      d.negMonomial R k + c.toScalar (y : 𝕂) • d.posMonomial R k := by
  rw [exchangeNumerator_def]
  let e : Fin ((d.polynomial k).degree + 1) ≃ Fin 2 := finCongr (by simp [hk])
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_two]
  have hc0 : (d.polynomial k).coeff (e.symm 0) = 1 := by
    rw [ExchangePolynomial.coeff_eq_of_eq hk (e.symm 0)]
    simp [e]
  have hc1 : (d.polynomial k).coeff (e.symm 1) = (y : 𝕂) := by
    rw [ExchangePolynomial.coeff_eq_of_eq hk (e.symm 1)]
    simp [e]
  have hd : (d.polynomial k).degree = 1 := by simp [hk]
  rw [hc0, hc1]
  simp [e, hd]

/-- For a binary exchange polynomial `1 + T`, the formal exchange numerator is
`M_k^- + M_k^+`. -/
theorem exchangeNumerator_of_binary {R : Type*} [CommSemiring R] [Finite I]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) {k : K}
    (hk : d.polynomial k = ExchangePolynomial.binary) :
    d.exchangeNumerator c k = d.negMonomial R k + d.posMonomial R k := by
  simpa using d.exchangeNumerator_of_binomial c 1
    (hk.trans ExchangePolynomial.binomial_one.symm)

/-- Coefficient-system homomorphisms preserve the formal exchange numerator. -/
@[simp]
theorem exchangeNumerator_map {R : Type*} [CommSemiring R] [Finite I]
    {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R} (f : c.Hom c')
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.map f.toMonoidWithZeroHom).exchangeNumerator c' k = d.exchangeNumerator c k := by
  rw [exchangeNumerator_eq_sum_single, exchangeNumerator_eq_sum_single]
  let e : Fin (((d.map f.toMonoidWithZeroHom).polynomial k).degree + 1) ≃
      Fin ((d.polynomial k).degree + 1) :=
    finCongr (by simp)
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hc : ((d.map f.toMonoidWithZeroHom).polynomial k).coeff l =
      f ((d.polynomial k).coeff (e l)) := by
    rw [ExchangePolynomial.coeff_eq_of_eq (d.map_polynomial f.toMonoidWithZeroHom k) l]
    simp [e]
  simp [e, hc, f.toScalar_apply]

end Numerator

end ExchangeData

end TauCeti
