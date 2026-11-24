/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Reflection
import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Normalized ambiguous forms

A binary quadratic form `f = (a, b, c)` is properly equivalent to its reflection
`f⁻ = (a, -b, c)` exactly when it has an improper automorph, an integral change of variables of
determinant `-1` fixing it; its proper class is then called ambiguous. The simplest ambiguous
forms are the *normalized* ones, with `b = 0` or `b = a`: the reflection fixes `(a, 0, c)`, and the
translation `(x, y) ↦ (x - y, y)` carries `(a, a, c)` to `(a, -a, c)`.

This file proves that every ambiguous class of integral forms contains a normalized form
(`exists_smul_b_eq_zero_or_b_eq_a_iff`), with no hypothesis on the discriminant. Over `ℚ` an
improper automorph `g` of a nonzero form has trace zero, since the Gram matrix of the form
identifies `g` with its inverse transpose `g⁻ᵀ`, whose trace is `tr g⁻¹ = -tr g` because
`det g = -1`; hence `g² = 1`, and `g` has a primitive integral eigenvector `v`. In an
oriented basis `(v, e)` the automorph sends `v` to `±v` and `e` to `∓e + k v`, and invariance of
the form forces `b = ±k a` with `a = f(v)`; a translation `e ↦ e + m v` then moves `b` to `0` or
`a`. When the form represents a positive integer, which
is the case for every positive definite form and every form of positive discriminant
(`exists_isCoprime_eval_pos`), the normalized form can moreover be chosen with `a > 0`
(`exists_smul_a_pos_and_b_eq_zero_or_b_eq_a`).

Normalized ambiguous forms with `a > 0` are the explicit representatives through which the
ambiguous classes, the classes of order at most two in the class group, are counted in genus
theory.

## Main results

* `TauCeti.BinaryQuadraticForm.exists_smul_eq_smul_reflected_iff`: being properly equivalent to
  the reflection is a property of the proper class.
* `TauCeti.BinaryQuadraticForm.exists_eq_smul_reflected_of_b_eq_zero_or_b_eq_a`: a normalized form
  is properly equivalent to its reflection, over any commutative ring.
* `TauCeti.BinaryQuadraticForm.exists_smul_b_eq_zero_or_b_eq_a_iff`: an integral form is properly
  equivalent to its reflection exactly when its proper class contains a normalized form.
* `TauCeti.BinaryQuadraticForm.exists_smul_a_pos_and_b_eq_zero_or_b_eq_a`: an ambiguous class
  representing a positive integer contains a normalized form with positive leading coefficient.

## References

* C. F. Gauss, *Disquisitiones Arithmeticae*, art. 163–165, for ambiguous forms.
* D. A. Cox, *Primes of the Form x² + ny²*, §3, for ambiguous forms and genus theory.
* D. A. Buell, *Binary Quadratic Forms: Classical Theory and Modern Computations*, Springer,
  1989, for ambiguous forms of either sign of the discriminant.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

section CommRing

variable {R : Type*} [CommRing R] {f : BinaryQuadraticForm R}

/-- If `γ` carries the reflection of `f` to `f`, then `δ γ conjJ(δ)⁻¹` carries the reflection of
`δ • f` to `δ • f`. -/
theorem smul_eq_smul_smul_reflected {γ : SL(2, R)} (h : f = γ • f.reflected) (δ : SL(2, R)) :
    δ • f = (δ * γ * (SpecialLinearGroup.conjJ δ)⁻¹) • (δ • f).reflected := by
  rw [reflected_smul, smul_smul, inv_mul_cancel_right, mul_smul, ← h]

/-- **Ambiguity is a class property.** A form is properly equivalent to its reflection exactly
when every properly equivalent form is. -/
theorem exists_smul_eq_smul_reflected_iff (f : BinaryQuadraticForm R) (δ : SL(2, R)) :
    (∃ γ : SL(2, R), δ • f = γ • (δ • f).reflected) ↔ ∃ γ : SL(2, R), f = γ • f.reflected := by
  refine ⟨fun ⟨γ, h⟩ ↦ ?_, fun ⟨γ, h⟩ ↦ ⟨_, smul_eq_smul_smul_reflected h δ⟩⟩
  have h' := smul_eq_smul_smul_reflected h δ⁻¹
  rw [inv_smul_smul] at h'
  exact ⟨_, h'⟩

/-- **Normalized forms are ambiguous.** A form `(a, b, c)` with `b = 0` or `b = a` is properly
equivalent to its reflection: `(a, 0, c)` is its own reflection, and `T` carries `(a, a, c)` to
`(a, -a, c)`. -/
theorem exists_eq_smul_reflected_of_b_eq_zero_or_b_eq_a (h : f.b = 0 ∨ f.b = f.a) :
    ∃ γ : SL(2, R), f = γ • f.reflected := by
  rcases h with h | h
  · exact ⟨1, by ext <;> simp [h]⟩
  · refine ⟨SpecialLinearGroup.map (Int.castRingHom R) ModularGroup.T⁻¹, ?_⟩
    ext <;> simp [h, ModularGroup.coe_T, two_mul]

end CommRing

variable {f : BinaryQuadraticForm ℤ}

/-- An improper automorph `σ γ⁻¹` of a nonzero integral form has trace zero, where
`σ = diag(1, -1)`: the diagonal entries of `γ` agree. -/
private theorem apply_zero_zero_eq_apply_one_one {γ : SL(2, ℤ)} (hf : f ≠ 0)
    (h : f = γ • f.reflected) : γ 0 0 = γ 1 1 := by
  have ha := congrArg BinaryQuadraticForm.a h
  have hb := congrArg BinaryQuadraticForm.b h
  have hc := congrArg BinaryQuadraticForm.c h
  simp only [smul_a, smul_b, smul_c, reflected_a, reflected_b, reflected_c] at ha hb hc
  have hdet := SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  -- The three coefficients of `f` are each killed by twice the difference of the diagonal
  -- entries of `γ`; these are the entries of `G g = g⁻ᵀ G` for the Gram matrix `G` of `f`.
  have h₁ : 2 * (f.a * (γ 1 1 - γ 0 0)) = 0 := by
    linear_combination -2 * γ 0 0 * ha - γ 1 0 * hb - (2 * f.a * γ 1 1 + f.b * γ 1 0) * hdet
  have h₂ : 2 * (f.b * (γ 1 1 - γ 0 0)) = 0 := by
    linear_combination 2 * γ 0 1 * ha - γ 0 0 * hb + γ 1 1 * hb - 2 * γ 1 0 * hc +
      (-f.b * (γ 1 1 - γ 0 0) + 2 * γ 0 1 * f.a - 2 * γ 1 0 * f.c) * hdet
  have h₃ : 2 * (f.c * (γ 1 1 - γ 0 0)) = 0 := by
    linear_combination γ 0 1 * hb + 2 * γ 1 1 * hc + (f.b * γ 0 1 + 2 * f.c * γ 0 0) * hdet
  by_contra hne
  have hne' : γ 1 1 - γ 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  exact hf <| BinaryQuadraticForm.ext
    (by simpa [hne'] using h₁) (by simpa [hne'] using h₂) (by simpa [hne'] using h₃)

/-- An ambiguous form whose improper automorph fixes the line of `(1, 0)` has `a ∣ b`. -/
private theorem a_dvd_b_of_eq_smul_reflected {γ : SL(2, ℤ)} (h : f = γ • f.reflected)
    (hγ : γ 1 0 = 0) : f.a ∣ f.b := by
  have hb := congrArg BinaryQuadraticForm.b h
  simp only [smul_b, reflected_a, reflected_b, reflected_c, hγ] at hb
  have hdet := SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  rw [hγ] at hdet
  refine ⟨-(γ 0 1 * γ 1 1), mul_left_cancel₀ two_ne_zero ?_⟩
  linear_combination hb - f.b * hdet

/-- A form with `a ∣ b` is translated by a power of `T` to a form with `b = 0` or `b = a`. -/
private theorem exists_T_zpow_smul_b_eq_zero_or_b_eq_a (h : f.a ∣ f.b) :
    ∃ k : ℤ, (ModularGroup.T ^ k • f).b = 0 ∨
      (ModularGroup.T ^ k • f).b = (ModularGroup.T ^ k • f).a := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m / 2, ?_⟩
  have hdiv := Int.mul_ediv_add_emod m 2
  simp only [T_zpow_smul]
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2
  · left
    linear_combination hm - f.a * hdiv + f.a * hm2
  · right
    linear_combination hm - f.a * hdiv + f.a * hm2

/-- **Ambiguous classes contain normalized forms.** An integral binary quadratic form is properly
equivalent to its reflection `(a, -b, c)` exactly when it is properly equivalent to a form
`(a, b, c)` with `b = 0` or `b = a`. No hypothesis on the discriminant is needed. -/
theorem exists_smul_b_eq_zero_or_b_eq_a_iff :
    (∃ γ : SL(2, ℤ), (γ • f).b = 0 ∨ (γ • f).b = (γ • f).a) ↔
      ∃ γ : SL(2, ℤ), f = γ • f.reflected := by
  refine ⟨fun ⟨δ, hδ⟩ ↦ (exists_smul_eq_smul_reflected_iff f δ).mp
    (exists_eq_smul_reflected_of_b_eq_zero_or_b_eq_a hδ), fun ⟨γ, h⟩ ↦ ?_⟩
  by_cases hf : f = 0
  · exact ⟨1, Or.inl (by simp [hf])⟩
  have hp := apply_zero_zero_eq_apply_one_one hf h
  have hdet := SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  rw [← hp] at hdet
  -- The form `r x² - 2 p x y + q y²`, of discriminant `4`, vanishes at a coprime pair `(u, v)`;
  -- this is an eigenvector of the improper automorph `σ γ⁻¹`, with `σ = diag(1, -1)`.
  obtain ⟨u, v, huv, huv0⟩ := exists_isCoprime_eval_eq_zero_of_discrim_eq_sq
    ⟨γ 1 0, -2 * γ 0 0, γ 0 1⟩ 2 (by
      simp only [discrim_def, _root_.discrim]
      linear_combination 4 * hdet)
  simp only [eval_mk] at huv0
  obtain ⟨ρ, hρ0, hρ1⟩ := huv.exists_SL2_col 0
  -- In the oriented basis `(ρ e₀, ρ e₁)`, whose first vector is the eigenvector `(u, v)`, the
  -- improper automorph fixes the first line.
  have h₁ := smul_eq_smul_smul_reflected h ρ⁻¹
  have hγ₁ : (ρ⁻¹ * γ * (SpecialLinearGroup.conjJ ρ⁻¹)⁻¹) 1 0 = 0 := by
    rw [SpecialLinearGroup.conjJ_inv, inv_inv]
    -- The `(1, 0)` entry, written out in terms of the first column `(u, v)` of `ρ`.
    have hentry : (ρ⁻¹ * γ * SpecialLinearGroup.conjJ ρ) 1 0 =
        γ 1 0 * u ^ 2 - (γ 0 0 + γ 1 1) * u * v + γ 0 1 * v ^ 2 := by
      simp [Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_two, adjugate_fin_two, hρ0, hρ1]
      ring
    rw [hentry]
    linear_combination huv0 + u * v * hp
  obtain ⟨k, hk⟩ := exists_T_zpow_smul_b_eq_zero_or_b_eq_a (a_dvd_b_of_eq_smul_reflected h₁ hγ₁)
  exact ⟨ModularGroup.T ^ k * ρ⁻¹, by rwa [mul_smul]⟩

/-- A normalized form representing a positive integer is properly equivalent to a normalized form
with positive leading coefficient. -/
private theorem exists_smul_a_pos_of_b_eq_zero_or_b_eq_a (hpos : ∃ x y, 0 < f.eval x y)
    (hf : f.b = 0 ∨ f.b = f.a) :
    ∃ γ : SL(2, ℤ), 0 < (γ • f).a ∧ ((γ • f).b = 0 ∨ (γ • f).b = (γ • f).a) := by
  obtain ⟨x, y, hxy⟩ := hpos
  rw [eval_def] at hxy
  by_cases ha : 0 < f.a
  · exact ⟨1, by simpa using ⟨ha, hf⟩⟩
  by_cases hb : f.b = 0
  · -- `(a, 0, c)` with `a ≤ 0` represents a positive value only if `c > 0`; then `S` gives
    -- `(c, 0, a)`.
    refine ⟨ModularGroup.S, ?_⟩
    rw [S_smul]
    refine ⟨?_, Or.inl (by simp [hb])⟩
    by_contra hc
    rw [hb] at hxy
    nlinarith [mul_nonpos_iff.mpr (Or.inr ⟨not_lt.mp ha, sq_nonneg x⟩),
      mul_nonpos_iff.mpr (Or.inr ⟨not_lt.mp hc, sq_nonneg y⟩)]
  · -- `(a, a, c)` with `a < 0`: then `4 c - a > 0`, and `T⁻¹ S T⁻² S = !![-1, -1; 2, 1]`
    -- gives `(4 c - a, 4 c - a, c)`.
    have hb' : f.b = f.a := hf.resolve_left hb
    have ha' : f.a < 0 := lt_of_le_of_ne (not_lt.mp ha) fun h0 ↦ hb (hb'.trans h0)
    have hγ : (ModularGroup.T ^ (-1 : ℤ) * ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) *
        ModularGroup.S) • f = ⟨4 * f.c - f.a, 4 * f.c - f.a, f.c⟩ := by
      simp only [mul_smul, S_smul, T_zpow_smul, hb']
      ext <;> ring
    refine ⟨ModularGroup.T ^ (-1 : ℤ) * ModularGroup.S * ModularGroup.T ^ (-2 : ℤ) *
      ModularGroup.S, ?_⟩
    rw [hγ]
    refine ⟨?_, Or.inr rfl⟩
    -- `4 a f(x, y) = a² (2 x + y)² - a (a - 4 c) y² < 0`.
    have hid : 4 * f.a * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) =
        f.a ^ 2 * (2 * x + y) ^ 2 + f.a * (4 * f.c - f.a) * y ^ 2 := by
      rw [hb']
      ring
    have hneg : f.a * (4 * f.c - f.a) * y ^ 2 < 0 := by
      nlinarith [sq_nonneg (f.a * (2 * x + y)), mul_neg_of_neg_of_pos ha' hxy]
    by_contra hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos ha'.le (not_lt.mp hc), sq_nonneg y]

/-- **Ambiguous classes contain normalized forms with positive leading coefficient.** An integral
binary quadratic form that represents a positive integer and is properly equivalent to its
reflection is properly equivalent to a form `(a, b, c)` with `a > 0` and `b = 0` or `b = a`. The
hypothesis holds for every positive definite form and every form of positive discriminant
(`exists_isCoprime_eval_pos`); it cannot be dropped, as `-x² - y²` shows. -/
theorem exists_smul_a_pos_and_b_eq_zero_or_b_eq_a (hpos : ∃ x y, 0 < f.eval x y)
    (h : ∃ γ : SL(2, ℤ), f = γ • f.reflected) :
    ∃ γ : SL(2, ℤ), 0 < (γ • f).a ∧ ((γ • f).b = 0 ∨ (γ • f).b = (γ • f).a) := by
  obtain ⟨δ, hδ⟩ := exists_smul_b_eq_zero_or_b_eq_a_iff.mpr h
  obtain ⟨γ, hγ⟩ :=
    exists_smul_a_pos_of_b_eq_zero_or_b_eq_a ((exists_eval_smul_iff δ f (0 < ·)).mpr hpos) hδ
  exact ⟨γ * δ, by rwa [mul_smul]⟩

end TauCeti.BinaryQuadraticForm
