/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Cubic.TripleRoot
public import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic.LinearCombination

/-!
# Repeated roots of monic cubics over perfect fields

A monic cubic over a perfect field has zero discriminant exactly when it factors as
`(X - ρ)² (X - σ)` with both roots in the ground field. This gives the three branches
of the residue-cubic test in Tate's algorithm: nonzero discriminant, a double root
and a distinct simple root, or a triple root.

The covariant `b² - 3c` distinguishes the last two branches for
`X³ + b X² + c X + d`: in the repeated-root factorization it is `(ρ - σ)²`.
The characteristic `2` and `3` cases are included. Perfectness supplies square roots
in characteristic `2` and cube roots in characteristic `3`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151,
  IV.9, the residue cubic in Steps 6–8 of Tate's algorithm.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

/-- The coefficients of a monic cubic with a specified repeated root and remaining root. -/
theorem cubic_eq_X_sub_C_sq_mul_X_sub_C_iff {R : Type*} [CommRing R] {b c d ρ σ : R} :
    X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 2 * (X - C σ) ↔
      b = -(ρ + ρ + σ) ∧ c = ρ * ρ + ρ * σ + ρ * σ ∧ d = -(ρ * ρ * σ) := by
  rw [sq (X - C ρ), Cubic.prod_X_sub_C_eq]
  have hP : X ^ 3 + C b * X ^ 2 + C c * X + C d = (⟨1, b, c, d⟩ : Cubic R).toPoly := by
    simp [Cubic.toPoly]
  rw [hP, Cubic.toPoly_injective]
  simp

variable {k : Type*} [Field k] [PerfectField k] {b c d : k}

/-- A monic cubic over a perfect field is a cube of a monic linear polynomial
exactly when its discriminant and quadratic covariant both vanish. These are the
triple-root branch tests of the residue-cubic classification. -/
theorem exists_cubic_eq_X_sub_C_pow_three_iff_discr_eq_zero_and_b_sq_eq_three_c :
    (∃ ρ : k, X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 3) ↔
      (⟨1, b, c, d⟩ : Cubic k).discr = 0 ∧ b ^ 2 = 3 * c := by
  constructor
  · rintro ⟨ρ, hρ⟩
    obtain ⟨rfl, rfl, rfl⟩ := cubic_eq_X_sub_C_pow_three_iff.1 hρ
    simp only [Cubic.discr, one_pow]
    constructor <;> ring
  · rintro ⟨hD, hb⟩
    simp only [Cubic.discr, one_pow] at hD
    have hB : b ^ 2 - 3 * c = 0 := sub_eq_zero.mpr hb
    have hS : b * c - 9 * d = 0 := by
      have hs : (b * c - 9 * d) ^ 2 = 0 := by
        linear_combination 4 * (c ^ 2 - 3 * b * d) * hB - 3 * hD
      exact (pow_eq_zero_iff two_ne_zero).1 hs
    have hC : c ^ 2 = 3 * b * d := by
      by_cases h3 : (3 : k) = 0
      · have hb : b = 0 := (pow_eq_zero_iff two_ne_zero).1 (by simpa [h3] using hB)
        have hc : c = 0 := by
          have hc3 : c ^ 3 = 0 := by
            rw [hb] at hD
            have h27 : (27 : k) = 0 := by linear_combination 9 * h3
            have h4 : (4 : k) = 1 := by linear_combination h3
            simpa [h27, h4] using hD
          exact (pow_eq_zero_iff three_ne_zero).1 hc3
        simp [hc, h3]
      · apply (mul_left_cancel₀ h3)
        linear_combination b * hS - c * hB
    exact exists_cubic_eq_X_sub_C_pow_three_iff.2 ⟨hb, hC, sub_eq_zero.mp hS⟩

/-- A monic cubic over a perfect field has zero discriminant exactly when it has a
repeated root in that field. In this case the remaining root is rational as well. -/
theorem cubic_discr_eq_zero_iff :
    (⟨1, b, c, d⟩ : Cubic k).discr = 0 ↔
      ∃ ρ σ : k, X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 2 * (X - C σ) := by
  constructor
  · intro hD
    by_cases hB : b ^ 2 - 3 * c = 0
    · obtain ⟨ρ, hρ⟩ :=
        exists_cubic_eq_X_sub_C_pow_three_iff_discr_eq_zero_and_b_sq_eq_three_c.2
          ⟨hD, sub_eq_zero.mp hB⟩
      exact ⟨ρ, ρ, by simpa only [pow_succ] using hρ⟩
    · simp only [Cubic.discr, one_pow] at hD
      -- Otherwise find the repeated root, by a square root in characteristic `2`
      -- and by the subresultant formula `(9d - bc)/(2(b² - 3c))` elsewhere.
      have hroot : ∃ ρ : k, 3 * ρ ^ 2 + 2 * b * ρ + c = 0 ∧
          ρ ^ 3 + b * ρ ^ 2 + c * ρ + d = 0 := by
        by_cases h2 : (2 : k) = 0
        · have : CharP k 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2
            (by exact_mod_cast h2)
          obtain ⟨ρ, hρ⟩ := surjective_frobenius k 2 c
          rw [frobenius_def] at hρ
          have hd : d = b * c := by
            have hs : (d - b * c) ^ 2 = 0 := by
              linear_combination hD +
                (2 * c ^ 3 + 2 * b ^ 3 * d + 14 * d ^ 2 - 10 * b * c * d) * h2
            exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).1 hs)
          refine ⟨ρ, ?_, ?_⟩
          · linear_combination hρ + (ρ ^ 2 + b * ρ + c) * h2
          · linear_combination (ρ + b) * hρ + hd + (b * c + ρ * c) * h2
        · refine ⟨(9 * d - b * c) / (2 * (b ^ 2 - 3 * c)), ?_, ?_⟩
          · field_simp [h2, hB]
            linear_combination -9 * hD
          · field_simp [h2, hB]
            -- The remaining denominator uses the normalized product `c * 3`.
            have hB' : b ^ 2 - c * 3 ≠ 0 := by simpa only [mul_comm c 3] using hB
            field_simp [hB']
            linear_combination (-2 * b ^ 3 + 9 * b * c - 27 * d) * hD
      obtain ⟨ρ, hder, heval⟩ := hroot
      refine ⟨ρ, -b - 2 * ρ, cubic_eq_X_sub_C_sq_mul_X_sub_C_iff.2 ⟨by ring, ?_, ?_⟩⟩
      · linear_combination hder
      · linear_combination heval - ρ * hder
  · rintro ⟨ρ, σ, h⟩
    obtain ⟨rfl, rfl, rfl⟩ := cubic_eq_X_sub_C_sq_mul_X_sub_C_iff.1 h
    simp only [Cubic.discr, one_pow]
    ring

/-- A monic cubic over a perfect field has a double root distinct from its simple
root exactly when its discriminant vanishes and `b² - 3c` does not vanish. -/
theorem exists_cubic_eq_X_sub_C_sq_mul_X_sub_C_iff :
    (∃ ρ σ : k, ρ ≠ σ ∧
      X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 2 * (X - C σ)) ↔
      (⟨1, b, c, d⟩ : Cubic k).discr = 0 ∧ b ^ 2 ≠ 3 * c := by
  constructor
  · rintro ⟨ρ, σ, hρσ, h⟩
    refine ⟨cubic_discr_eq_zero_iff.2 ⟨ρ, σ, h⟩, ?_⟩
    obtain ⟨hb, hc, _⟩ := cubic_eq_X_sub_C_sq_mul_X_sub_C_iff.1 h
    have heq : b ^ 2 - 3 * c = (ρ - σ) ^ 2 := by rw [hb, hc]; ring
    exact sub_ne_zero.mp (heq ▸ pow_ne_zero 2 (sub_ne_zero.mpr hρσ))
  · rintro ⟨hD, hB⟩
    obtain ⟨ρ, σ, h⟩ := cubic_discr_eq_zero_iff.1 hD
    refine ⟨ρ, σ, ?_, h⟩
    intro heq
    obtain ⟨hb, hc, _⟩ := cubic_eq_X_sub_C_sq_mul_X_sub_C_iff.1 h
    apply hB
    rw [hb, hc, heq]
    ring

/-- The residue-cubic trichotomy: a monic cubic over a perfect field has nonzero
discriminant, one double and one distinct simple root, or a triple root. The first
case does not assert that the cubic splits over the ground field. -/
theorem cubic_root_trichotomy :
    (⟨1, b, c, d⟩ : Cubic k).discr ≠ 0 ∨
      (∃ ρ σ : k, ρ ≠ σ ∧
        X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 2 * (X - C σ)) ∨
      ∃ ρ : k, X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 3 := by
  by_cases hD : (⟨1, b, c, d⟩ : Cubic k).discr = 0
  · obtain ⟨ρ, σ, h⟩ := cubic_discr_eq_zero_iff.1 hD
    by_cases heq : ρ = σ
    · exact Or.inr (Or.inr ⟨ρ, by simpa only [← heq, pow_succ] using h⟩)
    · exact Or.inr (Or.inl ⟨ρ, σ, heq, h⟩)
  · exact Or.inl hD

end TauCeti.Polynomial
