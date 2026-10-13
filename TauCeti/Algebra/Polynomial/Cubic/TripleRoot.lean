/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic.LinearCombination

/-!
# Monic cubics with a triple root

A monic cubic `X³ + b X² + c X + d` is the cube `(X - ρ)³` exactly when `b = -3ρ`, `c = 3ρ²` and
`d = -ρ³`. Over a perfect field the existence of such a `ρ` can be read off the coefficients
without naming it: it holds exactly when

  `b² = 3 c`,  `c² = 3 b d`,  `b c = 9 d`,

that is, when the quadratic covariant `(b² - 3c) x² + (bc - 9d) x y + (c² - 3bd) y²` of the binary
cubic form `x³ + b x² y + c x y² + d y³` vanishes; away from characteristic `2` this covariant is
`-1/4` times the Hessian of the form. The criterion holds in every characteristic. Away from
characteristic `3` the root is `ρ = -b / 3`. In characteristic `3` the conditions say `b = c = 0`,
and the root is a cube root of `-d`, which exists because the field is perfect. Over the
imperfect field `𝔽₃(s)` the cubic `X³ - s` satisfies the conditions but is not the cube of a
linear polynomial.

This is the triple-root test of Tate's algorithm (Steps 6 to 8), applied to the residue cubic of
a Weierstrass equation over a discrete valuation ring.

## Main results

* `TauCeti.Polynomial.cubic_eq_X_sub_C_pow_three_iff`: over a commutative ring,
  `X³ + b X² + c X + d = (X - ρ)³` exactly when `b = -3ρ`, `c = 3ρ²` and `d = -ρ³`.
* `TauCeti.Polynomial.exists_cubic_eq_X_sub_C_pow_three_iff`: over a perfect field,
  `X³ + b X² + c X + d` is the cube of a monic linear polynomial exactly when `b² = 3c`,
  `c² = 3bd` and `bc = 9d`.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

/-- A monic cubic `X³ + b X² + c X + d` over a commutative ring is the cube `(X - ρ)³` exactly
when `b = -3ρ`, `c = 3ρ²` and `d = -ρ³`. -/
theorem cubic_eq_X_sub_C_pow_three_iff {R : Type*} [CommRing R] {b c d ρ : R} :
    X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 3 ↔
      b = -3 * ρ ∧ c = 3 * ρ ^ 2 ∧ d = -ρ ^ 3 := by
  have hcube : (X - C ρ) ^ 3 = (⟨1, -3 * ρ, 3 * ρ ^ 2, -ρ ^ 3⟩ : Cubic R).toPoly := by
    rw [pow_succ, sq, Cubic.prod_X_sub_C_eq]
    congr 2 <;> ring
  have hP : X ^ 3 + C b * X ^ 2 + C c * X + C d = (⟨1, b, c, d⟩ : Cubic R).toPoly := by
    simp [Cubic.toPoly]
  rw [hcube, hP, Cubic.toPoly_injective]
  simp

/-- **The triple-root test for a monic cubic.** Over a perfect field `k`, the cubic
`X³ + b X² + c X + d` is `(X - ρ)³` for some `ρ ∈ k` exactly when `b² = 3c`, `c² = 3bd` and
`bc = 9d`. Perfectness is needed only in characteristic `3`, where the conditions reduce to
`b = c = 0` and `ρ` is a cube root of `-d`. -/
theorem exists_cubic_eq_X_sub_C_pow_three_iff {k : Type*} [Field k] [PerfectField k]
    {b c d : k} :
    (∃ ρ, X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C ρ) ^ 3) ↔
      b ^ 2 = 3 * c ∧ c ^ 2 = 3 * b * d ∧ b * c = 9 * d := by
  simp only [cubic_eq_X_sub_C_pow_three_iff]
  constructor
  · rintro ⟨ρ, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> ring
  rintro ⟨hb, hc, hd⟩
  by_cases h3 : (3 : k) = 0
  · -- In characteristic `3` the conditions force `b = c = 0`, and `ρ` is a cube root of `-d`.
    have : CharP k 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 (by exact_mod_cast h3)
    obtain ⟨ρ, hρ⟩ := surjective_frobenius k 3 (-d)
    rw [frobenius_def] at hρ
    have hb0 : b = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [hb, h3, zero_mul])
    have hc0 : c = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [hc, h3, zero_mul, zero_mul])
    exact ⟨ρ, by simp [hb0, h3], by simp [hc0, h3], by rw [hρ, neg_neg]⟩
  · -- Away from characteristic `3`, the root is `-b / 3`.
    refine ⟨-b / 3, by field_simp, ?_, ?_⟩
    · field_simp
      linear_combination -hb
    · field_simp
      linear_combination -b * hb - 3 * hd

end TauCeti.Polynomial
