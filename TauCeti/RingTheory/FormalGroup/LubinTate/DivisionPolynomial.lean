/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Division polynomials for the Lubin–Tate binomial

For the binomial in `TauCeti.isLubinTateSeries_C_mul_X_add_X_pow`, the factorization is
the polynomial case of Yoshida, *Local class field theory via Lubin–Tate theory*, Lemma 3.4.

* `TauCeti.LubinTate.divisionPolynomial_isEisensteinAt` gives the Eisenstein criterion
  for these factors, using `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`.
* `TauCeti.LubinTate.iterate_comp_uniformizerPolynomial_separable` gives simple torsion
  roots when `q` vanishes in the coefficient field, by `Polynomial.derivative_comp`.
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

/-- The primitive factor of the Lubin–Tate binomial at level `n + 1`. -/
noncomputable def divisionPolynomial (π : R) (q n : ℕ) : R[X] :=
  (X ^ (q - 1) + C π).comp ((uniformizerPolynomial π q).comp^[n] X)

/-- The primitive factor is the first-level factor evaluated at the preceding iterate. -/
theorem divisionPolynomial_def (π : R) (q n : ℕ) :
    divisionPolynomial π q n =
      (X ^ (q - 1) + C π).comp ((uniformizerPolynomial π q).comp^[n] X) := (rfl)

/-- The level-`n + 1` iterate is the product of the level-`n` iterate and the primitive factor. -/
theorem iterate_comp_succ_eq_mul_divisionPolynomial (π : R) (q n : ℕ) (hq : q ≠ 0) :
    (uniformizerPolynomial π q).comp^[n + 1] X =
      (uniformizerPolynomial π q).comp^[n] X * divisionPolynomial π q n := by
  have hq' : q - 1 + 1 = q := Nat.succ_pred_eq_of_ne_zero hq
  have hf : uniformizerPolynomial π q = X * (X ^ (q - 1) + C π) := by
    rw [uniformizerPolynomial_def, mul_add, ← pow_succ', hq', mul_comm X (C π)]
  rw [Function.iterate_succ_apply', divisionPolynomial_def]
  calc
    _ = (X * (X ^ (q - 1) + C π)).comp _ := congrArg (fun f : R[X] ↦ f.comp _) hf
    _ = _ := by rw [mul_comp, X_comp]

/-- For `q ≥ 2`, the level-`n` iterate is monic of degree `q ^ n`. -/
theorem isMonicOfDegree_iterate_comp_uniformizerPolynomial [Nontrivial R]
    (π : R) (q n : ℕ) (hq : 2 ≤ q) :
    IsMonicOfDegree ((uniformizerPolynomial π q).comp^[n] X) (q ^ n) := by
  have hf : IsMonicOfDegree (uniformizerPolynomial π q) q := by
    rw [uniformizerPolynomial_def]
    have hle : (C π * X : R[X]).natDegree ≤ 1 :=
      natDegree_le_iff_degree_le.mpr (degree_C_mul_X_le π)
    exact (isMonicOfDegree_X_pow R q).add_right (hle.trans_lt (by lia))
  induction n with
  | zero => simpa only [pow_zero, Function.iterate_zero_apply] using isMonicOfDegree_X R
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact hf.comp (pow_ne_zero _ (by lia)) ih

/-- For `q ≥ 2`, the primitive factor at level `n + 1` is monic of degree `(q - 1) * q ^ n`. -/
theorem isMonicOfDegree_divisionPolynomial [Nontrivial R] (π : R) (q n : ℕ) (hq : 2 ≤ q) :
    IsMonicOfDegree (divisionPolynomial π q n) ((q - 1) * q ^ n) := by
  rw [divisionPolynomial_def]
  have hg : IsMonicOfDegree (X ^ (q - 1) + C π) (q - 1) :=
    (isMonicOfDegree_X_pow R _).add_right (by rw [natDegree_C]; lia)
  exact hg.comp (pow_ne_zero _ (by lia))
    (isMonicOfDegree_iterate_comp_uniformizerPolynomial π q n hq)

/-- The primitive factor has constant coefficient `π` for `q ≥ 2`. -/
@[simp]
theorem coeff_zero_divisionPolynomial (π : R) (q n : ℕ) (hq : 2 ≤ q) :
    (divisionPolynomial π q n).coeff 0 = π := by
  have hq' : q - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hq
  have hzero : ∀ k : ℕ, ((uniformizerPolynomial π q).comp^[k] X).eval 0 = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', eval_comp, ih]
      simp only [uniformizerPolynomial_def, eval_add, eval_pow, eval_X, eval_mul, eval_C,
        zero_pow (by lia : q ≠ 0), mul_zero, add_zero]
  simp only [divisionPolynomial_def, coeff_zero_eq_eval_zero, eval_comp, hzero, eval_add,
    eval_pow, eval_X, zero_pow hq', eval_C, zero_add]

/-- The Lubin–Tate binomial commutes with coefficient maps. -/
@[simp]
theorem uniformizerPolynomial_map {S : Type*} [CommSemiring S] (π : R) (q : ℕ)
    (φ : R →+* S) : (uniformizerPolynomial π q).map φ = uniformizerPolynomial (φ π) q := by
  simp only [uniformizerPolynomial_def, Polynomial.map_add, Polynomial.map_pow, map_X,
    Polynomial.map_mul, map_C]

/-- Coefficient maps commute with iteration of the Lubin–Tate binomial. -/
@[simp]
theorem map_iterate_comp_uniformizerPolynomial {S : Type*} [CommSemiring S] (π : R) (q n : ℕ)
    (φ : R →+* S) : ((uniformizerPolynomial π q).comp^[n] X).map φ =
      (uniformizerPolynomial (φ π) q).comp^[n] X := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', map_comp, uniformizerPolynomial_map, ih]

/-- The primitive factor commutes with coefficient maps. -/
@[simp]
theorem map_divisionPolynomial {S : Type*} [CommSemiring S] (π : R) (q n : ℕ)
    (φ : R →+* S) :
    (divisionPolynomial π q n).map φ = divisionPolynomial (φ π) q n := by
  simp only [divisionPolynomial_def, map_comp, Polynomial.map_add, Polynomial.map_pow,
    map_X, map_C, map_iterate_comp_uniformizerPolynomial]

/-- Modulo an ideal containing `π`, the primitive factor is the corresponding power of `X`. -/
theorem map_mk_divisionPolynomial {R : Type*} [CommRing R] {π : R} (q n : ℕ)
    {I : Ideal R} (hπ : π ∈ I) :
    (divisionPolynomial π q n).map (Ideal.Quotient.mk I) = X ^ ((q - 1) * q ^ n) := by
  have hmap : ∀ k : ℕ, ((uniformizerPolynomial (0 : R ⧸ I) q).comp^[k] X) =
      X ^ (q ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [uniformizerPolynomial_def, map_zero, zero_mul, add_zero, pow_comp, X_comp,
        ← pow_mul, pow_succ]
  rw [map_divisionPolynomial, Ideal.Quotient.eq_zero_iff_mem.mpr hπ, divisionPolynomial_def, hmap]
  simp only [map_zero, add_zero, pow_comp, X_comp, ← pow_mul, Nat.mul_comm]

/-- If `π ∈ I` and `π ∉ I ^ 2`, the primitive factor is Eisenstein at `I`. -/
theorem divisionPolynomial_isEisensteinAt {R : Type*} [CommRing R] {π : R} (q n : ℕ)
    {I : Ideal R} (hπ : π ∈ I) (hπ₂ : π ∉ I ^ 2) :
    (divisionPolynomial π q n).IsEisensteinAt I := by
  have hI : I ≠ ⊤ := fun h ↦ hπ₂ ((Ideal.pow_eq_top_iff.mpr (.inl h)) ▸ Submodule.mem_top)
  by_cases hq : 2 ≤ q
  swap
  · have hzero : q - 1 = 0 := by lia
    rw [divisionPolynomial_def, hzero, pow_zero]
    rw [← C_1, ← C_add, C_comp]
    have hc : 1 + π ∉ I := fun h ↦ (Ideal.ne_top_iff_one I).mp hI ((I.add_mem_iff_left hπ).mp h)
    refine ⟨by rwa [leadingCoeff_C], fun {i} hi ↦ ?_, ?_⟩
    · rw [natDegree_C] at hi
      lia
    · rw [coeff_C_zero]
      exact fun h ↦ hc (Ideal.pow_le_self two_ne_zero h)
  have := nontrivial_of_ne π 0 fun h ↦ hπ₂ (h ▸ (I ^ 2).zero_mem)
  have hdeg := isMonicOfDegree_divisionPolynomial π q n hq
  refine hdeg.monic.isEisensteinAt_of_mem_of_notMem hI (fun {i} hi ↦ ?_) ?_
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← coeff_map, map_mk_divisionPolynomial q n hπ, coeff_X_pow]
    rw [hdeg.natDegree_eq] at hi
    exact ite_eq_right hi.ne
  · rwa [coeff_zero_divisionPolynomial π q n hq]

/-- The derivative of the level-`n` iterate is `π ^ n` when `q` vanishes in the coefficient ring. -/
theorem derivative_iterate_comp_uniformizerPolynomial (π : R) (q n : ℕ) (hq : (q : R) = 0) :
    derivative ((uniformizerPolynomial π q).comp^[n] X) = C (π ^ n) := by
  have hf : derivative (uniformizerPolynomial π q) = C π := by
    simp only [uniformizerPolynomial_def, derivative_add, derivative_X_pow, hq, map_zero,
      zero_mul, zero_add, derivative_C_mul_X]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', derivative_comp, hf, C_comp, ih]
    rw [← C_mul, pow_succ]

/-- The level-`n` iterate is separable when `q` vanishes and `π` is a unit. -/
theorem iterate_comp_uniformizerPolynomial_separable (π : R) (q n : ℕ) (hq : (q : R) = 0)
    (hπ : IsUnit π) : ((uniformizerPolynomial π q).comp^[n] X).Separable := by
  rw [separable_def, derivative_iterate_comp_uniformizerPolynomial π q n hq,
    ← mul_one (C (π ^ n)), isCoprime_mul_unit_left_right ((hπ.pow n).map C)]
  exact isCoprime_one_right

/-- The roots of the primitive factor are exactly the roots appearing at level `n + 1`
that were absent at level `n`, when the uniformizer has nonzero image. -/
@[simp]
theorem divisionPolynomial_eval₂_eq_zero_iff {S : Type*} [CommSemiring S] [NoZeroDivisors S]
    {π : R} {q n : ℕ} {φ : R →+* S} {x : S} (hq : 2 ≤ q) (hπ : φ π ≠ 0) :
    (divisionPolynomial π q n).eval₂ φ x = 0 ↔
      ((uniformizerPolynomial π q).comp^[n + 1] X).eval₂ φ x = 0 ∧
      ((uniformizerPolynomial π q).comp^[n] X).eval₂ φ x ≠ 0 := by
  rw [iterate_comp_succ_eq_mul_divisionPolynomial π q n (by lia), eval₂_mul, mul_eq_zero]
  have hprev (hx : ((uniformizerPolynomial π q).comp^[n] X).eval₂ φ x = 0) :
      (divisionPolynomial π q n).eval₂ φ x ≠ 0 := by
    have hq' : q - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hq
    simpa only [divisionPolynomial_def, eval₂_comp, hx, eval₂_add, eval₂_X_pow, zero_pow hq',
      eval₂_C, zero_add] using hπ
  grind

end TauCeti.LubinTate
