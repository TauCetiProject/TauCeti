/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeData.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Scalar evaluations, exchange exponents, and exchange numerators

Given a coefficient system `c : CoefficientSystem 𝕂 R` and exchange data `d : ExchangeData 𝕂 row`
along `row : K ↪ I`, each mutable index `k : K` determines three algebraic invariants over `R`:

* the scalar evaluation `valueAtOne c d k = ∑ l, c.toScalar ((d.polynomial k).coeff l) ∈ R`, equal
  to `H_k(1)`;
* when `I` is finite, the summand exponents
  `exchangeExponent d k l = -e_{row k} + l (β_k)⁺ + (deg(H_k) - l) (β_k)⁻ : I →₀ ℤ`;
* when `I` is finite, the *exchange numerator*
  `exchangeNumerator c d k ∈ LaurentRing R {i : I // i ≠ row k}` built from the positive and
  negative column monomials `posMonomial` and `negMonomial`.

Reversing `H_k` preserves `valueAtOne`; consequently, on normalized exchange data, `valueAtOne` on a
zero column is invariant under every single-step mutation and every finite mutation word. When
column `k` is nonzero, the summand exponents `l ↦ d.exchangeExponent k l` are pairwise distinct.
Finally, mutating `d` at `k` swaps `posMonomial` with `negMonomial` while reversing `H_k`, leaving
`exchangeNumerator c d k` unchanged (`exchangeNumerator_mutation`).

## Main definitions

* `TauCeti.ExchangeData.valueAtOne`: the scalar sum `H_k(1) ∈ R` of the coefficients of `H_k`.
* `TauCeti.ExchangeData.exchangeExponent`: the exponent `-e_{row k} + l (β_k)⁺ + (r_k - l) (β_k)⁻`
  in `I →₀ ℤ` of the `l`-th exchange summand.
* `TauCeti.ExchangeData.posExponent`, `TauCeti.ExchangeData.negExponent`,
  `TauCeti.ExchangeData.posMonomial`, and `TauCeti.ExchangeData.negMonomial`: the positive and
  negative column exponents and monomials in `LaurentRing R {i : I // i ≠ row k}`.
* `TauCeti.ExchangeData.exchangeNumerator`: the exchange numerator
  `E_k ∈ LaurentRing R {i : I // i ≠ row k}`.

## Main results

* `TauCeti.ExchangeData.IsNormalized.valueAtOne_mutation_of_column_eq_zero` and
  `TauCeti.ExchangeData.IsNormalized.valueAtOne_mutationWord_of_column_eq_zero`: on normalized
  exchange data, `H_j(1)` on a zero column `j` is invariant under arbitrary mutations and mutation
  words.
* `TauCeti.ExchangeData.exchangeExponent_injective_of_exists_ne_zero`: on a nonzero column `k`, the
  summand exponents `l ↦ d.exchangeExponent k l` for `0 ≤ l ≤ deg(H_k)` are pairwise distinct.
* `TauCeti.ExchangeData.exchangeNumerator_mutation`: `E_k(μ_k(d)) = E_k(d)`.
* `TauCeti.ExchangeData.exchangeNumerator_mem_range_toLaurent`: `E_k` lies in the polynomial
  subalgebra `(MvPolynomial.toLaurent).range`.
* `TauCeti.ExchangeData.val_inv_unitX_mul_rename_exchangeNumerator`: multiplying the embedded
  exchange numerator in `LaurentRing R I` by `X_{row k}⁻¹` produces the Laurent sum over
  `exchangeExponent`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2.
* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014, §2.
-/

public section

namespace TauCeti

namespace ExchangeData

variable {𝕂 𝕂' R : Type*} [CommMonoidWithZero 𝕂] [CommMonoidWithZero 𝕂'] [CommSemiring R]
  {I K I' K' : Type*} {row : K ↪ I} {row' : K' ↪ I'}

/-! ### Value at `1` -/

/-- The scalar value `H_k(1) = ∑ l, c.toScalar ((d.polynomial k).coeff l)` in `R`. -/
def valueAtOne (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) : R :=
  c.valueAtOne (d.polynomial k)

theorem valueAtOne_def (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.valueAtOne c k = ∑ l, c.toScalar ((d.polynomial k).coeff l) :=
  c.valueAtOne_def (d.polynomial k)

@[simp]
theorem valueAtOne_submatrix (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (f : I' → I) (g : K' → K) (h : ∀ k, f (row' k) = row (g k)) (k : K') :
    (d.submatrix f g h).valueAtOne c k = d.valueAtOne c (g k) := by
  simp [valueAtOne]

@[simp]
theorem valueAtOne_principal (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.principal.valueAtOne c k = d.valueAtOne c k := by
  simp [valueAtOne]

@[simp]
theorem valueAtOne_reindex (c : CoefficientSystem 𝕂 R) (eI : I ≃ I') (eK : K ≃ K')
    (h : ∀ k, eI (row k) = row' (eK k)) (d : ExchangeData 𝕂 row) (k : K') :
    (reindex eI eK h d).valueAtOne c k = d.valueAtOne c (eK.symm k) := by
  simp [valueAtOne]

/-- Homomorphisms of coefficient systems preserve `valueAtOne`. -/
@[simp]
theorem valueAtOne_map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : CoefficientSystemHom c c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map f).valueAtOne c' k = d.valueAtOne c k := by
  simp [valueAtOne]

@[simp]
theorem valueAtOne_of_isBinary (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row}
    (hd : d.IsBinary) (k : K) :
    d.valueAtOne c k = 2 := by
  simp [valueAtOne, hd.polynomial_eq k]

/-- Mutating at `k` reverses `H_k` and therefore preserves `valueAtOne c d k`. -/
@[simp]
theorem valueAtOne_mutation_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).valueAtOne c k = d.valueAtOne c k := by
  simp [valueAtOne]

/-- On normalized exchange data, `valueAtOne` on a zero column `j` is unchanged by mutation in any
direction `k`. -/
theorem IsNormalized.valueAtOne_mutation_of_column_eq_zero [DecidableEq I] [DecidableEq K]
    {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (k : K) {j : K}
    (hz : ∀ i, d.exchange.matrix i j = 0) :
    (d.mutation c k).valueAtOne c j = d.valueAtOne c j := by
  obtain rfl | hj := eq_or_ne j k
  · exact d.valueAtOne_mutation_self c j
  · rw [valueAtOne, hd.mutation_polynomial_of_matrix_row_eq_zero hj (hz (row k)), ← valueAtOne]

/-- On normalized exchange data, `valueAtOne` on a zero column `j` is invariant along every finite
mutation word. -/
theorem IsNormalized.valueAtOne_mutationWord_of_column_eq_zero [DecidableEq I] [DecidableEq K]
    {c : CoefficientSystem 𝕂 R} {d : ExchangeData 𝕂 row} (hd : d.IsNormalized c) (w : List K)
    {j : K} (hz : ∀ i, d.exchange.matrix i j = 0) :
    (d.mutationWord c w).valueAtOne c j = d.valueAtOne c j := by
  induction w generalizing d with
  | nil => simp
  | cons k _w ih =>
    have hz' : ∀ i, (d.mutation c k).exchange.matrix i j = 0 :=
      (d.mutation_column_eq_zero_iff c k j).mpr hz
    rw [mutationWord_cons, ih (hd.mutation k) hz', hd.valueAtOne_mutation_of_column_eq_zero k hz]

/-! ### Exchange exponents and exchange numerators -/

section FiniteIndex

variable [Fintype I]

/-- The exponent `-e_{row k} + l (β_k)⁺ + (deg(H_k) - l) (β_k)⁻ : I →₀ ℤ` of the `l`-th exchange
summand in direction `k`. -/
noncomputable def exchangeExponent (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) : I →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦
    (l : ℤ) * (d.dividedColumn k i)⁺ +
      (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i)⁻) -
    Finsupp.single (row k) 1

theorem exchangeExponent_apply (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) (i : I) :
    d.exchangeExponent k l i =
      (l : ℤ) * (d.dividedColumn k i)⁺ +
        (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i)⁻ -
        Finsupp.single (row k) 1 i :=
  (rfl)

@[simp]
theorem exchangeExponent_apply_row (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    d.exchangeExponent k l (row k) = -1 := by
  simp [exchangeExponent_apply]

theorem exchangeExponent_apply_of_ne (d : ExchangeData 𝕂 row) (k : K) (l : ℕ)
    {i : I} (hi : i ≠ row k) :
    d.exchangeExponent k l i =
      (l : ℤ) * (d.dividedColumn k i)⁺ +
        (((d.polynomial k).degree - l : ℕ) : ℤ) * (d.dividedColumn k i)⁻ := by
  rw [exchangeExponent_apply, Finsupp.single_eq_of_ne hi, sub_zero]

@[simp]
theorem exchangeExponent_map {F : Type*} [FunLike F 𝕂 𝕂'] [MonoidWithZeroHomClass F 𝕂 𝕂']
    (ψ : F) (d : ExchangeData 𝕂 row) (k : K) (l : ℕ) :
    (d.map ψ).exchangeExponent k l = d.exchangeExponent k l := by
  ext i
  simp [exchangeExponent_apply]

/-- On a zero column `k`, every exchange summand has exponent `-e_{row k}`. -/
theorem exchangeExponent_of_forall_eq_zero (d : ExchangeData 𝕂 row) {k : K}
    (hz : ∀ i, d.exchange.matrix i k = 0) (l : ℕ) :
    d.exchangeExponent k l = -Finsupp.single (row k) 1 := by
  ext i
  have hdiv : d.dividedColumn k i = 0 := (d.dividedColumn_eq_zero_iff k i).mpr (hz i)
  simp [exchangeExponent_apply, hdiv]

/-- Mutating at `k` reverses the indexing of the exchange exponents for `l ≤ deg(H_k)`. -/
theorem exchangeExponent_mutation_self [DecidableEq I] [DecidableEq K]
    (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) {l : ℕ}
    (hl : l ≤ (d.polynomial k).degree) :
    (d.mutation c k).exchangeExponent k l =
      d.exchangeExponent k ((d.polynomial k).degree - l) := by
  ext i
  have hsub : (d.polynomial k).degree - ((d.polynomial k).degree - l) = l := Nat.sub_sub_self hl
  simp [exchangeExponent_apply, hsub, add_comm]

/-- For a nonzero column `k`, the summand exponents `l ↦ d.exchangeExponent k l` for
`l : Fin ((d.polynomial k).degree + 1)` are pairwise distinct. -/
theorem exchangeExponent_injective_of_exists_ne_zero (d : ExchangeData 𝕂 row) {k : K}
    (hne : ∃ i, d.exchange.matrix i k ≠ 0) :
    Function.Injective fun l : Fin ((d.polynomial k).degree + 1) ↦ d.exchangeExponent k l := by
  obtain ⟨i, hi_ne⟩ := hne
  have hi_row : i ≠ row k := fun h ↦ hi_ne (h ▸ d.exchange.matrix_row_self k)
  have hb : d.dividedColumn k i ≠ 0 := mt (d.dividedColumn_eq_zero_iff k i).mp hi_ne
  intro l₁ l₂ heq
  have eval_i := DFunLike.congr_fun heq i
  rw [d.exchangeExponent_apply_of_ne k l₁ hi_row,
    d.exchangeExponent_apply_of_ne k l₂ hi_row] at eval_i
  have hl₁ : (l₁ : ℕ) ≤ (d.polynomial k).degree := Nat.lt_succ_iff.mp l₁.isLt
  have hl₂ : (l₂ : ℕ) ≤ (d.polynomial k).degree := Nat.lt_succ_iff.mp l₂.isLt
  rcases lt_trichotomy (d.dividedColumn k i) 0 with hneg | hzero | hpos
  · rw [posPart_eq_zero.mpr hneg.le, negPart_eq_neg.mpr hneg.le, mul_zero, mul_zero, zero_add,
      zero_add] at eval_i
    have hsub : (((d.polynomial k).degree - (l₁ : ℕ) : ℕ) : ℤ) =
        (((d.polynomial k).degree - (l₂ : ℕ) : ℕ) : ℤ) :=
      mul_right_cancel₀ (neg_ne_zero.mpr hb) eval_i
    have := Int.ofNat.inj hsub
    exact Fin.ext (by omega)
  · exact absurd hzero hb
  · rw [posPart_eq_self.mpr hpos.le, negPart_eq_zero.mpr hpos.le, mul_zero, mul_zero, add_zero,
      add_zero] at eval_i
    have hval : ((l₁ : ℕ) : ℤ) = ((l₂ : ℕ) : ℤ) := mul_right_cancel₀ hb eval_i
    exact Fin.ext (Int.ofNat.inj hval)

/-- The positive exponent vector `i ↦ (β_k(i))⁺` on `{i : I // i ≠ row k}`. -/
noncomputable def posExponent (d : ExchangeData 𝕂 row) (k : K) :
    {i : I // i ≠ row k} →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (d.dividedColumn k i.1)⁺

/-- The negative exponent vector `i ↦ (β_k(i))⁻` on `{i : I // i ≠ row k}`. -/
noncomputable def negExponent (d : ExchangeData 𝕂 row) (k : K) :
    {i : I // i ≠ row k} →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (d.dividedColumn k i.1)⁻

@[simp]
theorem posExponent_apply (d : ExchangeData 𝕂 row) (k : K) (i : {i : I // i ≠ row k}) :
    d.posExponent k i = (d.dividedColumn k i.1)⁺ :=
  (rfl)

@[simp]
theorem negExponent_apply (d : ExchangeData 𝕂 row) (k : K) (i : {i : I // i ≠ row k}) :
    d.negExponent k i = (d.dividedColumn k i.1)⁻ :=
  (rfl)

@[simp]
theorem posExponent_mutation_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).posExponent k = d.negExponent k := by
  ext i
  simp [posExponent, negExponent]

@[simp]
theorem negExponent_mutation_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).negExponent k = d.posExponent k := by
  ext i
  simp [posExponent, negExponent]

/-- The positive column monomial `m_{k, +} = ∏_{i ≠ row k} X_i^{(β_k(i))⁺}` in
`LaurentRing R {i : I // i ≠ row k}`. -/
noncomputable def posMonomial (R : Type*) [Semiring R] (d : ExchangeData 𝕂 row) (k : K) :
    LaurentRing R {i : I // i ≠ row k} :=
  AddMonoidAlgebra.single (d.posExponent k) 1

/-- The negative column monomial `m_{k, -} = ∏_{i ≠ row k} X_i^{(β_k(i))⁻}` in
`LaurentRing R {i : I // i ≠ row k}`. -/
noncomputable def negMonomial (R : Type*) [Semiring R] (d : ExchangeData 𝕂 row) (k : K) :
    LaurentRing R {i : I // i ≠ row k} :=
  AddMonoidAlgebra.single (d.negExponent k) 1

@[simp]
theorem posMonomial_mutation_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).posMonomial R k = d.negMonomial R k := by
  simp [posMonomial, negMonomial]

@[simp]
theorem negMonomial_mutation_self [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).negMonomial R k = d.posMonomial R k := by
  simp [posMonomial, negMonomial]

/-- The *exchange numerator* `E_k = ∑_{l = 0}^{deg(H_k)} φ(h_{k, l}) m_{k, +}^l m_{k, -}^{r_k - l}`
in `LaurentRing R {i : I // i ≠ row k}`. -/
noncomputable def exchangeNumerator (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) : LaurentRing R {i : I // i ≠ row k} :=
  (d.polynomial k).evalHomogeneous c.toScalar (d.posMonomial R k) (d.negMonomial R k)

theorem exchangeNumerator_def (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator c k =
      ∑ l : Fin ((d.polynomial k).degree + 1),
        c.toScalar ((d.polynomial k).coeff l) •
          (d.posMonomial R k ^ (l : ℕ) *
            d.negMonomial R k ^ ((d.polynomial k).degree - (l : ℕ))) :=
  ExchangePolynomial.evalHomogeneous_def _ _ _ _

/-- Expansion of `exchangeNumerator` as a sum of `AddMonoidAlgebra.single` monomials. -/
theorem exchangeNumerator_eq_sum_single (c : CoefficientSystem 𝕂 R) (d : ExchangeData 𝕂 row)
    (k : K) :
    d.exchangeNumerator c k =
      ∑ l : Fin ((d.polynomial k).degree + 1),
        AddMonoidAlgebra.single
          ((l : ℕ) • d.posExponent k +
            ((d.polynomial k).degree - (l : ℕ)) • d.negExponent k)
          (c.toScalar ((d.polynomial k).coeff l)) := by
  simp [exchangeNumerator_def, posMonomial, negMonomial]

/-- **Invariance of the exchange numerator under mutation at `k`**: `E_k(μ_k(d)) = E_k(d)`. -/
@[simp]
theorem exchangeNumerator_mutation [DecidableEq I] [DecidableEq K] (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (d.mutation c k).exchangeNumerator c k = d.exchangeNumerator c k := by
  simp [exchangeNumerator]

/-- Homomorphisms of coefficient systems preserve `exchangeNumerator`. -/
@[simp]
theorem exchangeNumerator_map {c : CoefficientSystem 𝕂 R} {c' : CoefficientSystem 𝕂' R}
    (f : CoefficientSystemHom c c') (d : ExchangeData 𝕂 row) (k : K) :
    (d.map f).exchangeNumerator c' k = d.exchangeNumerator c k := by
  have hpos : (d.map f).posMonomial R k = d.posMonomial R k := by
    simp only [posMonomial]
    congr 1
    ext i
    simp
  have hneg : (d.map f).negMonomial R k = d.negMonomial R k := by
    simp only [negMonomial]
    congr 1
    ext i
    simp
  have hcomp : (c'.toScalar ∘ f : 𝕂 → R) = c.toScalar := funext f.toScalar_apply
  simp [exchangeNumerator, hpos, hneg, hcomp]

/-- For binary exchange data, the exchange numerator is `m_{k, -} + m_{k, +}`. -/
theorem exchangeNumerator_of_isBinary (c : CoefficientSystem 𝕂 R) {d : ExchangeData 𝕂 row}
    (hd : d.IsBinary) (k : K) :
    d.exchangeNumerator c k = d.negMonomial R k + d.posMonomial R k := by
  simp [exchangeNumerator, hd.polynomial_eq k]

/-- On a zero column `k`, the exchange numerator reduces to the constant Laurent polynomial
`algebraMap R _ (d.valueAtOne c k)`. -/
theorem exchangeNumerator_of_forall_eq_zero (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) {k : K} (hz : ∀ i, d.exchange.matrix i k = 0) :
    d.exchangeNumerator c k =
      algebraMap R (LaurentRing R {i : I // i ≠ row k}) (d.valueAtOne c k) := by
  have hp : d.posExponent k = 0 := by
    ext i
    simp [(d.dividedColumn_eq_zero_iff k i.1).mpr (hz i.1)]
  have hn : d.negExponent k = 0 := by
    ext i
    simp [(d.dividedColumn_eq_zero_iff k i.1).mpr (hz i.1)]
  rw [exchangeNumerator_eq_sum_single, hp, hn, valueAtOne_def, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp [Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.one_def]

/-- Every exponent occurring in `exchangeNumerator` is nonnegative, so `exchangeNumerator` lies in
the polynomial subalgebra `(MvPolynomial.toLaurent).range`. -/
theorem exchangeNumerator_mem_range_toLaurent (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    d.exchangeNumerator c k ∈
      (MvPolynomial.toLaurent :
        MvPolynomial {i : I // i ≠ row k} R →ₐ[R] LaurentRing R {i : I // i ≠ row k}).range := by
  have hp :
      d.posMonomial R k ∈
        (MvPolynomial.toLaurent :
          MvPolynomial {i : I // i ≠ row k} R →ₐ[R] LaurentRing R {i : I // i ≠ row k}).range := by
    rw [MvPolynomial.mem_range_toLaurent_iff]
    intro m hm i
    rw [posMonomial, AddMonoidAlgebra.coeff_single] at hm
    have hmem : m = d.posExponent k := by
      by_contra hne
      simp [hne] at hm
    subst hmem
    exact posPart_nonneg _
  have hn :
      d.negMonomial R k ∈
        (MvPolynomial.toLaurent :
          MvPolynomial {i : I // i ≠ row k} R →ₐ[R] LaurentRing R {i : I // i ≠ row k}).range := by
    rw [MvPolynomial.mem_range_toLaurent_iff]
    intro m hm i
    rw [negMonomial, AddMonoidAlgebra.coeff_single] at hm
    have hmem : m = d.negExponent k := by
      by_contra hne
      simp [hne] at hm
    subst hmem
    exact negPart_nonneg _
  rw [exchangeNumerator_def]
  refine Subalgebra.sum_mem _ fun l _ ↦ Subalgebra.smul_mem _ ?_ _
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hp _) (Subalgebra.pow_mem _ hn _)

/-- Embedding `exchangeNumerator c d k` into `LaurentRing R I` and multiplying by `X_{row k}⁻¹`
yields the Laurent sum indexed by `d.exchangeExponent k l`. -/
theorem val_inv_unitX_mul_rename_exchangeNumerator (c : CoefficientSystem 𝕂 R)
    (d : ExchangeData 𝕂 row) (k : K) :
    (((LaurentRing.unitX (row k))⁻¹ : (LaurentRing R I)ˣ) : LaurentRing R I) *
        LaurentRing.rename Subtype.val (d.exchangeNumerator c k) =
      ∑ l : Fin ((d.polynomial k).degree + 1),
        AddMonoidAlgebra.single (d.exchangeExponent k l)
          (c.toScalar ((d.polynomial k).coeff l)) := by
  classical
  rw [exchangeNumerator_eq_sum_single, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [LaurentRing.val_inv_unitX, LaurentRing.rename_single, AddMonoidAlgebra.single_mul_single,
    one_mul]
  congr 1
  ext i
  obtain rfl | hi := eq_or_ne i (row k)
  · have hnotin : row k ∉ Set.range (Subtype.val : {j : I // j ≠ row k} → I) := by
      rintro ⟨⟨j, hj⟩, rfl⟩
      exact hj rfl
    simp [Finsupp.mapDomain_of_notMem_range _ _ hnotin]
  · let j : {x : I // x ≠ row k} := ⟨i, hi⟩
    have heq :
        ((l : ℕ) • d.posExponent k +
            ((d.polynomial k).degree - (l : ℕ)) • d.negExponent k).mapDomain Subtype.val j.1 =
          ((l : ℕ) • d.posExponent k +
            ((d.polynomial k).degree - (l : ℕ)) • d.negExponent k) j :=
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ j
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hi, zero_add]
    exact heq.trans (by simp [j, d.exchangeExponent_apply_of_ne k l hi])

end FiniteIndex

/-! ### Checks -/

/-- Over `ZMod 3`, the exchange polynomial `H(T) = 1 + T + T²` on a zero column has
`valueAtOne = 0`, which is not a unit. -/
example :
    let B : ExchangeMatrix (Function.Embedding.refl (Fin 1)) :=
      ⟨0, fun _ ↦ 1, ⟨fun _ ↦ Int.zero_lt_one, fun _ _ ↦ by simp⟩⟩
    let H : ExchangePolynomial (ZMod 3) :=
      ⟨2, by decide, fun _ ↦ 1, isUnit_one, isUnit_one⟩
    let d : ExchangeData (ZMod 3) (Function.Embedding.refl (Fin 1)) :=
      ⟨B, fun _ ↦ H, fun _ _ ↦ dvd_zero _⟩
    d.valueAtOne (CoefficientSystem.trivial (ZMod 3)) 0 = 0 ∧
      ¬ IsUnit (d.valueAtOne (CoefficientSystem.trivial (ZMod 3)) 0) := by
  intro B H d
  have hval : d.valueAtOne (CoefficientSystem.trivial (ZMod 3)) 0 = 0 := by
    rw [valueAtOne_def]
    simp only [d, H, CoefficientSystem.trivial_toScalar, MonoidWithZeroHom.id_apply]
    decide
  exact ⟨hval, hval ▸ not_isUnit_zero⟩

/-- For binary exchange data with extended matrix `B̃ = [[0], [1]]` (mutable row `0` and frozen row
`1`), the two exchange exponents at `0` are `-e_0` and `-e_0 + e_1`, and the exchange numerator in
`LaurentRing ℤ {i : Fin 2 // i ≠ 0}` is `1 + X_1`. -/
noncomputable example :
    let B : ExchangeMatrix (Fin.castSuccEmb (n := 1)) :=
      ⟨!![0; 1], fun _ ↦ 1, ⟨fun _ ↦ Int.zero_lt_one, by decide⟩⟩
    let d : ExchangeData ℤ (Fin.castSuccEmb (n := 1)) := ExchangeData.ofExchangeMatrix B
    d.exchangeExponent 0 0 = -Finsupp.single 0 1 ∧
      d.exchangeExponent 0 1 = Finsupp.single 1 1 - Finsupp.single 0 1 ∧
      d.exchangeNumerator (CoefficientSystem.trivial ℤ) 0 =
        1 + LaurentRing.X ⟨1, by decide⟩ := by
  intro B d
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [exchangeExponent_apply, d, B]
  · ext i
    fin_cases i <;> simp [exchangeExponent_apply, d, B]
  · rw [d.exchangeNumerator_of_isBinary _ (isBinary_ofExchangeMatrix B) 0, posMonomial, negMonomial,
      LaurentRing.X_def, AddMonoidAlgebra.one_def]
    have hdiv1 : d.dividedColumn 0 1 = 1 := by
      simp [d, B]
    let j₁ : {x : Fin 2 // x ≠ Fin.castSuccEmb 0} := ⟨1, by decide⟩
    have hj₁ : ∀ u : {x : Fin 2 // x ≠ Fin.castSuccEmb 0}, u = j₁ := fun ⟨i, hi⟩ ↦ by
      fin_cases i
      · exact absurd rfl hi
      · rfl
    have hp : d.posExponent 0 = Finsupp.single j₁ 1 := by
      ext u
      rw [hj₁ u, posExponent_apply, Finsupp.single_eq_same]
      simp [j₁, hdiv1]
    have hn : d.negExponent 0 = 0 := by
      ext u
      rw [hj₁ u, negExponent_apply, Finsupp.coe_zero, Pi.zero_apply]
      simp [j₁, hdiv1]
    rw [hp, hn]

end ExchangeData

end TauCeti
