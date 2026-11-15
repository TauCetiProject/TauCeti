/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.NumberTheory.NumberField.Quadratic.Norm

/-!
# Negative Pell equations and units of norm minus one

For a squarefree radicand, the negative Pell equation has an integral solution exactly when
the full ring of integers of the quadratic field has a unit of norm minus one. This includes
the half-integral case: if twice the coordinates of a norm-minus-one integer are odd, cubing
gives integral coordinates and preserves the norm. This comparison permits arithmetic
conditions stated using Pell equations to be applied to the units of the full ring of integers.

The quadratic-integer coordinates are described in Keith Conrad, *Factoring in Quadratic
Fields*, Theorem 3.4; multiplication and powers of Pell solutions are discussed in his
*Pell's Equation I*, Theorem 7.1. For the negative Pell equation and its class-group context,
see Peter Koymans and Carlo Pagano, *On Stevenhagen's conjecture*, Introduction.
-/

public section

open Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The negative Pell equation for a squarefree radicand is soluble over the integers if and
only if the full ring of integers of the corresponding quadratic field has a unit of norm
minus one. No positivity assumption on `d` is needed: the quadratic presentation excludes
square radicands, and both sides are false for negative radicands. -/
theorem exists_sq_sub_mul_sq_eq_neg_one_iff_exists_norm_eq_neg_one
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) :
    (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = -1) ↔
      ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact exists_norm_eq_neg_one_of_sq_sub_mul_sq_eq_neg_one hmin hgen hxy
  · rintro ⟨u, hu⟩
    have huZ : Algebra.norm ℤ (u : 𝓞 K) = -1 := by
      exact_mod_cast (Algebra.coe_norm_int (u : 𝓞 K)).trans hu
    by_cases hd4 : d % 4 = 1
    · obtain ⟨A, B, hAB⟩ := exists_sq_sub_mul_sq_eq_four_mul_norm hmin hgen hsf (u : 𝓞 K)
      rw [huZ] at hAB
      have hd2 : d % 2 = 1 := by omega
      have hpar := congrArg (fun n : ℤ => n % 2) hAB
      rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_two, Int.sq_emod_two, hd2] at hpar
      have hsame : A % 2 = B % 2 := by omega
      by_cases hA : A % 2 = 0
      · -- Even half-coordinates were already integral.
        have hA' : A = 2 * (A / 2) := by omega
        have hB' : B = 2 * (B / 2) := by omega
        refine ⟨A / 2, B / 2, ?_⟩
        rw [hA', hB'] at hAB
        nlinarith only [hAB]
      · -- For odd half-coordinates, these are the coordinates of the cube.
        have hAodd : A % 2 = 1 := by omega
        have hsq := Int.sq_emod_two A
        have hX : 2 * (A * (A ^ 2 + 3) / 2) = A * (A ^ 2 + 3) := by
          have hdiv : 2 ∣ A ^ 2 + 3 := by omega
          exact Int.mul_ediv_cancel' (dvd_mul_of_dvd_right hdiv A)
        have hY : 2 * (B * (A ^ 2 + 1) / 2) = B * (A ^ 2 + 1) := by
          have hdiv : 2 ∣ A ^ 2 + 1 := by omega
          exact Int.mul_ediv_cancel' (dvd_mul_of_dvd_right hdiv B)
        refine ⟨A * (A ^ 2 + 3) / 2, B * (A ^ 2 + 1) / 2, ?_⟩
        have hcube : (A * (A ^ 2 + 3)) ^ 2 - d * (B * (A ^ 2 + 1)) ^ 2 = -4 := by
          linear_combination (A ^ 2 + 1) ^ 2 * hAB
        rw [← hX, ← hY] at hcube
        nlinarith only [hcube]
    · obtain ⟨A, B, hAB⟩ :=
        exists_sq_sub_mul_sq_eq_norm_of_mod_four_ne_one hmin hgen hsf hd4 (u : 𝓞 K)
      exact ⟨A, B, hAB.trans huZ⟩

end NumberField
