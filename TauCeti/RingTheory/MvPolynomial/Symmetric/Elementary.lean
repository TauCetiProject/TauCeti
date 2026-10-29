/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Elementary symmetric polynomials

This file develops the elementary symmetric polynomials `e_n`.  It defines the integer-indexed
extension `TauCeti.esymmInt`, whose negative degrees vanish, and proves the generating functions
`∑ₙ eₙ tⁿ = ∏ᵢ (1 + xᵢ t)` and `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.  The integer indexing is the one
determinantal formulas such as the dual (transpose) Jacobi--Trudi identity use.

The file also gives explicit formulas for elementary symmetric polynomials in small finite
alphabets.  Such expansions support explicit computations of symmetric orbit products; in
particular the four-variable formula is used to express the quartic `D₄` resolvent's orbit
product in elementary symmetric polynomials.

## Main results

* `TauCeti.esymmInt`: the elementary symmetric polynomial `e_m` of an integer degree `m`, which
  is `0` for `m < 0`.
* `TauCeti.coeff_prod_one_add_C_mul_X`: the coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`, as a sum
  over the `n`-element subsets of the variables.
* `TauCeti.mk_esymm_eq_prod_one_add_X`: the generating function of the `eₙ`.
* `TauCeti.mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X`: its signed version
  `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.
* `TauCeti.esymm_fin_four`: the four elementary symmetric polynomials in four variables.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (2.2) and (2.6').
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, §7.6.
-/

public section

open Finset

namespace TauCeti

section esymmInt

variable (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R]

/-- The **elementary symmetric polynomial of integer degree** `m`: `e_m` for `m ≥ 0` and `0` for
`m < 0`.  This is the indexing determinantal formulas such as the dual Jacobi--Trudi identity
use. -/
noncomputable def esymmInt (m : ℤ) : MvPolynomial σ R :=
  if 0 ≤ m then MvPolynomial.esymm σ R m.toNat else 0

variable {σ R}

/-- In a nonnegative degree, `TauCeti.esymmInt` is `MvPolynomial.esymm`. -/
@[simp]
theorem esymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    esymmInt σ R m = MvPolynomial.esymm σ R m.toNat := by
  simp [esymmInt, hm]

/-- In a negative degree, `TauCeti.esymmInt` vanishes. -/
@[simp]
theorem esymmInt_of_neg {m : ℤ} (hm : m < 0) : esymmInt σ R m = 0 := by
  simp [esymmInt, not_le.mpr hm]

/-- In a natural-number degree, `TauCeti.esymmInt` is `MvPolynomial.esymm`. -/
theorem esymmInt_natCast (n : ℕ) : esymmInt σ R n = MvPolynomial.esymm σ R n := by
  simp [esymmInt]

/-- `e_0 = 1`. -/
theorem esymmInt_zero : esymmInt σ R 0 = 1 := by
  simp

/-- Changing the coefficients along a ring homomorphism preserves `TauCeti.esymmInt`. -/
@[simp]
theorem map_esymmInt {S : Type*} [CommSemiring S] (m : ℤ) (f : R →+* S) :
    MvPolynomial.map f (esymmInt σ R m) = esymmInt σ S m := by
  unfold esymmInt
  split_ifs <;> simp [MvPolynomial.map_esymm]

/-- Renaming the variables along a bijection preserves `TauCeti.esymmInt`. -/
@[simp]
theorem rename_esymmInt {τ : Type*} [Fintype τ] (m : ℤ) (e : σ ≃ τ) :
    MvPolynomial.rename e (esymmInt σ R m) = esymmInt τ R m := by
  unfold esymmInt
  split_ifs <;> simp [MvPolynomial.rename_esymm]

end esymmInt

section GeneratingFunction

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

omit [DecidableEq σ] in
/-- **The coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`**: the sum, over the `n`-element subsets `s` of
the variables, of the product of the variables in `s`. -/
theorem coeff_prod_one_add_C_mul_X (n : ℕ) :
    (∏ i, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) *
      PowerSeries.X)).coeff n =
      ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset σ), ∏ i ∈ s, MvPolynomial.X i := by
  classical
  rw [Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : ∏ i ∈ s, (PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) =
      PowerSeries.C (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial σ R)) *
        PowerSeries.X ^ s.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
  rw [h, PowerSeries.coeff_C_mul_X_pow]
  by_cases hs : s.card = n
  · subst hs
    simp
  · have hnt : n ≠ s.card := fun h => hs h.symm
    simp [hs, hnt]

omit [DecidableEq σ] in
/-- **The generating function of the elementary symmetric polynomials**:
`∑ₙ eₙ tⁿ = ∏ᵢ (1 + xᵢ t)`. -/
theorem mk_esymm_eq_prod_one_add_X :
    PowerSeries.mk (fun n => MvPolynomial.esymm σ R n) =
      ∏ i, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, coeff_prod_one_add_C_mul_X, MvPolynomial.esymm]

end GeneratingFunction

section SignedGeneratingFunction

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

omit [DecidableEq σ] in
/-- **The signed generating function of the elementary symmetric polynomials**:
`∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`. -/
theorem mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X :
    PowerSeries.mk (fun n => (-1 : MvPolynomial σ R) ^ n * MvPolynomial.esymm σ R n) =
      ∏ i, (1 - PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) := by
  rw [← PowerSeries.rescale_mk, mk_esymm_eq_prod_one_add_X (σ := σ) R, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_add, map_mul, map_neg, map_one, PowerSeries.rescale_X, PowerSeries.rescale_C]
  ring

end SignedGeneratingFunction

/-- The elementary symmetric polynomials in four variables, written out explicitly. -/
theorem esymm_fin_four {R : Type*} [CommSemiring R] :
    MvPolynomial.esymm (Fin 4) R 1 =
        MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 2 =
        MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 1 * MvPolynomial.X 3 + MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 3 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
          MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
          MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 4 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  have h1 : Finset.powersetCard 1 (Finset.univ : Finset (Fin 4)) = {{0}, {1}, {2}, {3}} := by
    decide
  have h2 : Finset.powersetCard 2 (Finset.univ : Finset (Fin 4)) =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by
    decide
  have h3 : Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by
    decide
  have h4 : Finset.powersetCard 4 (Finset.univ : Finset (Fin 4)) = {{0, 1, 2, 3}} := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp (config := { decide := true }) only [MvPolynomial.esymm, h1, h2, h3, h4,
        Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton, Finset.prod_singleton,
        Finset.mem_insert, Finset.mem_singleton, add_assoc, mul_assoc]

end TauCeti
