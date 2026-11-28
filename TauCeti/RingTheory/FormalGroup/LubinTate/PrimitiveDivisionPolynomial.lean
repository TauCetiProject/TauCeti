/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.Polynomial.IterateComp

/-!
# Iterates and primitive factors of the Lubin–Tate binomial

For `f = uniformizerPolynomial π q`, the level-`n` iterate is monic of degree `q ^ n`
when `q ≥ 2`. The next iterate is its product with `primitiveDivisionPolynomial π q n`,
monic of degree `(q - 1) * q ^ n`, whose roots are the new roots at level `n + 1`
when `π` has nonzero image. Modulo an ideal containing `π`, both polynomials reduce to
powers of `X`. The primitive factor is Eisenstein when `π ∈ I` and `π ∉ I ^ 2`.
When `q = 0` in the coefficient semiring, the iterate has derivative `C (π ^ n)` and is
separable if `π` is a unit.

These results supply polynomial inputs for the degree and uniformizer calculations for
primitive Lubin–Tate points (Yoshida, *Local class field theory via Lubin–Tate theory*,
Lemma 3.4). The coercion to power series agrees with the binomial in
`TauCeti.isLubinTateSeries_C_mul_X_add_X_pow`. We use Mathlib's
`Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` and `Polynomial.iterate_comp_eval`.
-/

public section

namespace TauCeti.LubinTate

open Polynomial

variable {R : Type*} [CommSemiring R]

/-- The polynomial `X ^ q + C π * X` for the Lubin–Tate binomial. -/
noncomputable def uniformizerPolynomial (π : R) (q : ℕ) : R[X] := X ^ q + C π * X

/-- The explicit binomial for the action of the uniformizer. -/
theorem uniformizerPolynomial_def (π : R) (q : ℕ) :
    uniformizerPolynomial π q = X ^ q + C π * X := (rfl)

/-- The polynomial coerces to the Lubin–Tate binomial power series. -/
@[simp] theorem coe_uniformizerPolynomial (π : R) (q : ℕ) :
    (uniformizerPolynomial π q : PowerSeries R) = PowerSeries.C π * PowerSeries.X +
      PowerSeries.X ^ q := by
  simp only [uniformizerPolynomial_def, coe_add, coe_pow, coe_mul, coe_C, coe_X]
  exact add_comm _ _

/-- The primitive factor of the Lubin–Tate binomial at level `n + 1`. -/
noncomputable def primitiveDivisionPolynomial (π : R) (q n : ℕ) : R[X] :=
  (X ^ (q - 1) + C π).comp ((uniformizerPolynomial π q).comp^[n] X)

/-- The primitive factor is the first-level factor evaluated at the preceding iterate. -/
theorem primitiveDivisionPolynomial_def (π : R) (q n : ℕ) :
    primitiveDivisionPolynomial π q n =
      (X ^ (q - 1) + C π).comp ((uniformizerPolynomial π q).comp^[n] X) := (rfl)

/-- The level-`n + 1` iterate is the product of the level-`n` iterate and the primitive factor. -/
theorem iterate_comp_succ_eq_mul_primitiveDivisionPolynomial (π : R) (q n : ℕ) (hq : q ≠ 0) :
    (uniformizerPolynomial π q).comp^[n + 1] X =
      (uniformizerPolynomial π q).comp^[n] X * primitiveDivisionPolynomial π q n := by
  have hq' : q - 1 + 1 = q := Nat.succ_pred_eq_of_ne_zero hq
  have hf : uniformizerPolynomial π q = (X ^ (q - 1) + C π) * X := by
    rw [uniformizerPolynomial_def, add_mul, ← pow_succ, hq']
  rw [primitiveDivisionPolynomial_def, mul_comm, hf, iterate_comp_mul_X_succ]

/-- For `q ≥ 2`, the level-`n` iterate is monic of degree `q ^ n`. -/
theorem isMonicOfDegree_iterate_comp_uniformizerPolynomial [Nontrivial R]
    (π : R) (q n : ℕ) (hq : 2 ≤ q) :
    IsMonicOfDegree ((uniformizerPolynomial π q).comp^[n] X) (q ^ n) := by
  have hf : IsMonicOfDegree (uniformizerPolynomial π q) q := by
    rw [uniformizerPolynomial_def]
    have hle : (C π * X : R[X]).natDegree ≤ 1 :=
      natDegree_le_iff_degree_le.mpr (degree_C_mul_X_le π)
    exact (isMonicOfDegree_X_pow R q).add_right (hle.trans_lt (by lia))
  exact hf.iterate_comp n

/-- For `q ≥ 2`, the primitive factor at level `n + 1` is monic of degree `(q - 1) * q ^ n`. -/
theorem isMonicOfDegree_primitiveDivisionPolynomial [Nontrivial R] (π : R) (q n : ℕ) (hq : 2 ≤ q) :
    IsMonicOfDegree (primitiveDivisionPolynomial π q n) ((q - 1) * q ^ n) := by
  rw [primitiveDivisionPolynomial_def]
  have hg : IsMonicOfDegree (X ^ (q - 1) + C π) (q - 1) :=
    (isMonicOfDegree_X_pow R _).add_right (by rw [natDegree_C]; lia)
  exact hg.comp (pow_ne_zero _ (by lia))
    (isMonicOfDegree_iterate_comp_uniformizerPolynomial π q n hq)

/-- For `q ≠ 0`, zero is a root of every iterate of the Lubin–Tate binomial. -/
theorem eval_zero_iterate_comp_uniformizerPolynomial (π : R) {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    ((uniformizerPolynomial π q).comp^[n] X).eval 0 = 0 := by
  rw [iterate_comp_eval, eval_X]
  apply Function.iterate_fixed
  simp only [uniformizerPolynomial_def, eval_add, eval_pow, eval_X, zero_pow hq, eval_mul,
    eval_C, mul_zero, add_zero]

/-- The primitive factor has constant coefficient `π` for `q ≥ 2`. -/
@[simp]
theorem coeff_zero_primitiveDivisionPolynomial (π : R) (q n : ℕ) (hq : 2 ≤ q) :
    (primitiveDivisionPolynomial π q n).coeff 0 = π := by
  have hq' : q - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hq
  simp only [primitiveDivisionPolynomial_def, coeff_zero_eq_eval_zero, eval_comp,
    eval_zero_iterate_comp_uniformizerPolynomial π (by lia : q ≠ 0), eval_add, eval_pow,
    eval_X, zero_pow hq', eval_C, zero_add]

/-- The Lubin–Tate binomial commutes with coefficient maps. -/
@[simp]
theorem uniformizerPolynomial_map {S : Type*} [CommSemiring S] (π : R) (q : ℕ)
    (φ : R →+* S) : (uniformizerPolynomial π q).map φ = uniformizerPolynomial (φ π) q := by
  simp only [uniformizerPolynomial_def, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_mul, map_C]

/-- The primitive factor commutes with coefficient maps. -/
@[simp]
theorem map_primitiveDivisionPolynomial {S : Type*} [CommSemiring S] (π : R) (q n : ℕ)
    (φ : R →+* S) :
    (primitiveDivisionPolynomial π q n).map φ = primitiveDivisionPolynomial (φ π) q n := by
  simp only [primitiveDivisionPolynomial_def, map_comp, Polynomial.map_add, Polynomial.map_pow,
    map_X, map_C, map_iterate_comp, uniformizerPolynomial_map]

/-- With zero linear parameter, the level-`n` iterate is the power `X ^ (q ^ n)`. -/
theorem iterate_comp_uniformizerPolynomial_zero (q n : ℕ) :
    (uniformizerPolynomial (0 : R) q).comp^[n] X = X ^ (q ^ n) := by
  rw [uniformizerPolynomial_def, map_zero, zero_mul, add_zero]
  exact iterate_comp_X_pow X q n

/-- Modulo an ideal containing `π`, the level-`n` iterate is `X ^ (q ^ n)`. -/
theorem map_mk_iterate_comp_uniformizerPolynomial {A : Type*} [CommRing A] {π : A} (q n : ℕ)
    {I : Ideal A} (hπ : π ∈ I) :
    ((uniformizerPolynomial π q).comp^[n] X).map (Ideal.Quotient.mk I) = X ^ (q ^ n) := by
  rw [map_iterate_comp, uniformizerPolynomial_map, Ideal.Quotient.eq_zero_iff_mem.mpr hπ, map_X,
    iterate_comp_uniformizerPolynomial_zero]

/-- Modulo an ideal containing `π`, the primitive factor is the corresponding power of `X`. -/
theorem map_mk_primitiveDivisionPolynomial {R : Type*} [CommRing R] {π : R} (q n : ℕ)
    {I : Ideal R} (hπ : π ∈ I) :
    (primitiveDivisionPolynomial π q n).map (Ideal.Quotient.mk I) = X ^ ((q - 1) * q ^ n) := by
  rw [primitiveDivisionPolynomial_def, map_comp, map_mk_iterate_comp_uniformizerPolynomial q n hπ]
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, map_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr hπ, map_zero, add_zero, pow_comp, X_comp, ← pow_mul,
    Nat.mul_comm]

/-- If `π ∈ I` and `π ∉ I ^ 2`, the primitive factor is Eisenstein at `I`. -/
theorem primitiveDivisionPolynomial_isEisensteinAt {R : Type*} [CommRing R] {π : R} (q n : ℕ)
    {I : Ideal R} (hπ : π ∈ I) (hπ₂ : π ∉ I ^ 2) :
    (primitiveDivisionPolynomial π q n).IsEisensteinAt I := by
  have hI : I ≠ ⊤ := fun h ↦ hπ₂ ((Ideal.pow_eq_top_iff.mpr (.inl h)) ▸ Submodule.mem_top)
  by_cases hq : 2 ≤ q
  swap
  · have hzero : q - 1 = 0 := by lia
    rw [primitiveDivisionPolynomial_def, hzero, pow_zero]
    rw [← C_1, ← C_add, C_comp]
    have hc : 1 + π ∉ I := fun h ↦ (Ideal.ne_top_iff_one I).mp hI ((I.add_mem_iff_left hπ).mp h)
    refine ⟨by rwa [leadingCoeff_C], fun {i} hi ↦ ?_, ?_⟩
    · rw [natDegree_C] at hi
      lia
    · rw [coeff_C_zero]
      exact fun h ↦ hc (Ideal.pow_le_self two_ne_zero h)
  have := nontrivial_of_ne π 0 fun h ↦ hπ₂ (h ▸ (I ^ 2).zero_mem)
  have hdeg := isMonicOfDegree_primitiveDivisionPolynomial π q n hq
  refine hdeg.monic.isEisensteinAt_of_mem_of_notMem hI (fun {i} hi ↦ ?_) ?_
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← coeff_map, map_mk_primitiveDivisionPolynomial q n hπ, coeff_X_pow]
    rw [hdeg.natDegree_eq] at hi
    exact ite_eq_right hi.ne
  · rwa [coeff_zero_primitiveDivisionPolynomial π q n hq]

/-- The derivative of the level-`n` iterate is `π ^ n` when `q` vanishes in the coefficient ring. -/
theorem derivative_iterate_comp_uniformizerPolynomial (π : R) (q n : ℕ) (hq : (q : R) = 0) :
    derivative ((uniformizerPolynomial π q).comp^[n] X) = C (π ^ n) := by
  have hf : derivative (uniformizerPolynomial π q) = C π := by
    simp only [uniformizerPolynomial_def, derivative_add, derivative_X_pow, hq, map_zero,
      zero_mul, zero_add, derivative_C_mul_X]
  exact derivative_iterate_comp_X_of_derivative_eq_C hf n

/-- The level-`n` iterate is separable when `q` vanishes and `π` is a unit. -/
theorem iterate_comp_uniformizerPolynomial_separable (π : R) (q n : ℕ) (hq : (q : R) = 0)
    (hπ : IsUnit π) : ((uniformizerPolynomial π q).comp^[n] X).Separable := by
  rw [separable_def, derivative_iterate_comp_uniformizerPolynomial π q n hq,
    ← mul_one (C (π ^ n)), isCoprime_mul_unit_left_right ((hπ.pow n).map C)]
  exact isCoprime_one_right

/-- The roots of the primitive factor are exactly the roots appearing at level `n + 1`
that were absent at level `n`, when the uniformizer has nonzero image.
This is not a simp rule because it expands one root test into two. -/
theorem primitiveDivisionPolynomial_eval₂_eq_zero_iff {S : Type*} [CommSemiring S]
    [NoZeroDivisors S] {π : R} {q n : ℕ} {φ : R →+* S} {x : S} (hq : 2 ≤ q) (hπ : φ π ≠ 0) :
    (primitiveDivisionPolynomial π q n).eval₂ φ x = 0 ↔
      ((uniformizerPolynomial π q).comp^[n + 1] X).eval₂ φ x = 0 ∧
      ((uniformizerPolynomial π q).comp^[n] X).eval₂ φ x ≠ 0 := by
  rw [iterate_comp_succ_eq_mul_primitiveDivisionPolynomial π q n (by lia), eval₂_mul, mul_eq_zero]
  have hprev (hx : ((uniformizerPolynomial π q).comp^[n] X).eval₂ φ x = 0) :
      (primitiveDivisionPolynomial π q n).eval₂ φ x ≠ 0 := by
    have hq' : q - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hq
    simpa only [primitiveDivisionPolynomial_def, eval₂_comp, hx, eval₂_add, eval₂_X_pow,
      zero_pow hq', eval₂_C, zero_add] using hπ
  grind

end TauCeti.LubinTate
