/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.BooleanCube.Walsh
public import Mathlib.Data.Finset.Density

/-!
# Plancherel's identity and the variance on the Boolean cube

For real functions on a finite cube `ι → ZMod 2` with the uniform probability measure, the
average of a product is the sum of the products of the Walsh coefficients (Plancherel's
identity). Consequently the mean square of a function is the sum of its squared coefficients,
and its variance is the part of that sum carried by the nonempty sets of coordinates. These
identities translate averages of functions on the cube into statements about their Walsh
coefficients, which is how influences, noise stability and the inequalities built on them are
analysed.

## Main definitions

* `TauCeti.variance f`: the variance `𝔼 x, (f x - 𝔼 y, f y) ^ 2` of a real function on the cube.

## Main results

* `TauCeti.expect_mul_eq_sum_walshCoeff`: Plancherel's identity
  `𝔼 x, f x * g x = ∑ S, walshCoeff f S * walshCoeff g S`.
* `TauCeti.expect_sq_eq_sum_sq_walshCoeff`, `TauCeti.sum_sq_walshCoeff_eq_one`: Parseval's
  identity, and the total squared weight `1` of a sign-valued function.
* `TauCeti.variance_eq_sum_sq_walshCoeff`: the variance is the sum of the squared coefficients at
  the nonempty sets.
* `TauCeti.variance_eq_four_mul_dens_mul_one_sub`: a sign-valued function taking the value `-1`
  on a fraction `α` of the cube has variance `4 α (1 - α)`.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Section 1.4: Plancherel's Theorem, Parseval's Theorem, Proposition 1.13
  and Fact 1.14.
* R. de Wolf, *A Brief Introduction to Fourier Analysis on the Boolean Cube*, Theory of
  Computing Library, Graduate Surveys 1 (2008), Section 2.2.
-/

public section

open Finset
open scoped BigOperators

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Plancherel's identity** on the cube: the average of a product of two functions is the sum
of the products of their Walsh coefficients. -/
theorem expect_mul_eq_sum_walshCoeff (f g : (ι → ZMod 2) → ℝ) :
    𝔼 x, f x * g x = ∑ S, walshCoeff f S * walshCoeff g S := by
  calc 𝔼 x, f x * g x = 𝔼 x, ∑ S, walshCoeff g S * (f x * walsh S x) := by
        refine expect_congr rfl fun x _ ↦ ?_
        conv_lhs => rw [← sum_walshCoeff_mul_walsh g x]
        rw [mul_sum]
        exact sum_congr rfl fun S _ ↦ by ring
    _ = ∑ S, walshCoeff f S * walshCoeff g S := by
        rw [expect_sum_comm]
        simp_rw [← mul_expect, ← walshCoeff_def, mul_comm]

/-- **Parseval's identity** on the cube: the mean square of a function is the sum of its squared
Walsh coefficients. -/
theorem expect_sq_eq_sum_sq_walshCoeff (f : (ι → ZMod 2) → ℝ) :
    𝔼 x, f x ^ 2 = ∑ S, walshCoeff f S ^ 2 := by
  simpa only [sq] using expect_mul_eq_sum_walshCoeff f f

/-- The squared Walsh coefficients of a sign-valued function sum to `1`. -/
theorem sum_sq_walshCoeff_eq_one {f : (ι → ZMod 2) → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1) :
    ∑ S, walshCoeff f S ^ 2 = 1 := by
  rw [← expect_sq_eq_sum_sq_walshCoeff]
  have h (x : ι → ZMod 2) : f x ^ 2 = 1 := by rcases hf x with h | h <;> simp [h]
  simp [h]

/-- The **variance** of a real function on the cube for the uniform probability measure: the
mean square deviation `𝔼 x, (f x - 𝔼 y, f y) ^ 2` of `f` from its mean. -/
noncomputable def variance (f : (ι → ZMod 2) → ℝ) : ℝ :=
  𝔼 x, (f x - 𝔼 y, f y) ^ 2

lemma variance_def (f : (ι → ZMod 2) → ℝ) : variance f = 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := (rfl)

lemma variance_nonneg (f : (ι → ZMod 2) → ℝ) : 0 ≤ variance f :=
  expect_nonneg fun _ _ ↦ sq_nonneg _

/-- The variance is the mean square minus the square of the mean. -/
lemma variance_eq_expect_sq_sub_sq (f : (ι → ZMod 2) → ℝ) :
    variance f = 𝔼 x, f x ^ 2 - (𝔼 x, f x) ^ 2 := by
  simp_rw [variance_def, sub_sq, expect_add_distrib, expect_sub_distrib, mul_assoc,
    ← mul_expect, ← expect_mul, Fintype.expect_const]
  ring

/-- The variance of a function is the sum of its squared Walsh coefficients at the nonempty
sets of coordinates. -/
theorem variance_eq_sum_sq_walshCoeff (f : (ι → ZMod 2) → ℝ) :
    variance f = ∑ S with S.Nonempty, walshCoeff f S ^ 2 := by
  have h : ({S | S.Nonempty} : Finset (Finset ι)) = univ.erase ∅ := by
    ext S
    simp [← ne_empty_iff_nonempty]
  rw [variance_eq_expect_sq_sub_sq, expect_sq_eq_sum_sq_walshCoeff, ← walshCoeff_empty, h,
    ← add_sum_erase univ _ (mem_univ ∅), add_sub_cancel_left]

/-- A sign-valued function that takes the value `-1` on a fraction `α` of the cube has
variance `4 α (1 - α)`. -/
theorem variance_eq_four_mul_dens_mul_one_sub {f : (ι → ZMod 2) → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    variance f = 4 * ({x | f x = -1} : Finset (ι → ZMod 2)).dens *
      (1 - ({x | f x = -1} : Finset (ι → ZMod 2)).dens) := by
  set s : Finset (ι → ZMod 2) := {x | f x = -1}
  have hsq (x : ι → ZMod 2) : f x ^ 2 = 1 := by rcases hf x with h | h <;> simp [h]
  have hf' (x : ι → ZMod 2) : f x = 1 - 2 * Set.indicator (s : Set (ι → ZMod 2)) 1 x := by
    rcases hf x with h | h <;> norm_num [s, Set.indicator_apply, h]
  have hmean : 𝔼 x, f x = 1 - 2 * (s.dens : ℝ) := by
    simp_rw [hf', expect_sub_distrib, ← mul_expect, expect_indicator_one, Fintype.expect_const]
  rw [variance_eq_expect_sq_sub_sq, hmean]
  simp only [hsq, Fintype.expect_const]
  ring

end TauCeti
