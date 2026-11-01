/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Cubic.RootSquaring
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Integer cubics whose fourth-power cubic is `X³ - γ X - 16`

In Heegner's and Stark's proof of the class number one theorem, a real algebraic integer `x`
generates a cubic extension of an imaginary quadratic field of class number one, its minimal
polynomial `X³ + a X² + b X + c` has integer coefficients, and the minimal polynomial of `x⁴` is
`X³ - γ₂ X - 16`, where `γ₂` is the value of the cube root of the `j`-function at the CM point.
This file determines all such integer cubics, and the corresponding values of `γ`, in terms of
the integer points of the quartic

  `y² = 2u(u³ + 1)`.

Write the Tschirnhaus transform by `X⁴` of `X³ + a X² + b X + c` (the monic cubic whose roots are
the fourth powers of its roots) as `X³ + a' X² + b' X - c⁴`; root squaring twice gives `a'` and
`b'` explicitly. It equals `X³ - γ X - 16` exactly when `c⁴ = 16`, `a' = 0` and `γ = -b'`. The
first condition is `c = ±2`, and by Newton's identities the second is
`2(a² - b)² = a⁴ - 4ac`. It forces `a` to be even. Writing `a = -c u` and `a² - b = 2y` turns it
into `y² = 2u(u³ + 1)`, and then `γ = heegnerGamma u y`.

The six integer points `(u, y) = (-1, 0), (0, 0), (1, ±2), (2, ±6)` of the quartic give the six
values `γ = -96, 0, -32, -5280, -960, -640320`, which are the values of `γ₂` at the CM points of
discriminants `-19, -3, -11, -67, -43, -163`.

## Main definitions

* `TauCeti.heegnerGamma u y`: the coefficient `γ` attached to the point `(u, y)` of the quartic.

## Main results

* `TauCeti.tschirnhausPolynomial_X_pow_four_eq_iff`: over a commutative ring of characteristic
  zero, the fourth-power cubic of `X³ + a X² + b X + c` with `a, b, c ∈ ℤ` is `X³ - γ X - 16`
  exactly when `c = ±2` and `a = -c u`, `b = 4u² - 2y` and `γ = heegnerGamma u y` for an integer
  point `(u, y)` of `y² = 2u(u³ + 1)`.
* `TauCeti.heegnerGamma_mem`: the values of `heegnerGamma` at the six known integer points.

## References

The reduction follows Heegner's class number one argument as completed by Stark:

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5.
-/

public section

open Polynomial

namespace TauCeti

/-- The coefficient `γ` of `X³ - γ X - 16` attached to an integer point `(u, y)` of the quartic
`y² = 2u(u³ + 1)`: it is `-16(((2u² - y)² + 2u)² + 2(u² - y))`. -/
def heegnerGamma (u y : ℤ) : ℤ :=
  -16 * (((2 * u ^ 2 - y) ^ 2 + 2 * u) ^ 2 + 2 * (u ^ 2 - y))

/-- The defining formula of `heegnerGamma`. -/
theorem heegnerGamma_def (u y : ℤ) :
    heegnerGamma u y = -16 * (((2 * u ^ 2 - y) ^ 2 + 2 * u) ^ 2 + 2 * (u ^ 2 - y)) :=
  (rfl)

/-- The integer conditions `c⁴ = 16` and `2(b² - 2ac) - (2b - a²)² = 0`, which say that the
fourth-power cubic of `X³ + a X² + b X + c` has the shape `X³ - γ X - 16`, are parametrized by the
integer points of `y² = 2u(u³ + 1)`. -/
private theorem exists_heegner_of_coeffs {a b c : ℤ} (hc : c ^ 4 = 16)
    (h : 2 * (b ^ 2 - 2 * a * c) - (2 * b - a ^ 2) ^ 2 = 0) :
    (c = 2 ∨ c = -2) ∧
      ∃ u y : ℤ, y ^ 2 = 2 * u * (u ^ 3 + 1) ∧ a = -c * u ∧ b = 4 * u ^ 2 - 2 * y := by
  have hc' : c = 2 ∨ c = -2 := by
    simpa [Nat.even_iff] using (pow_eq_pow_iff_of_ne_zero (by decide : (4 : ℕ) ≠ 0)).mp
      (show c ^ 4 = (2 : ℤ) ^ 4 by simpa using hc)
  refine ⟨hc', ?_⟩
  -- `(2b - a²)² = 2(b² - 2ac)` is even, hence so are `2b - a²`, `a²` and `a`.
  have ha : Even a := by
    have hsq : Even ((2 * b - a ^ 2) ^ 2) := ⟨b ^ 2 - 2 * a * c, by linear_combination -h⟩
    have heven : Even (2 * b - a ^ 2) := (Int.even_pow.1 hsq).1
    have ha2 : Even (a ^ 2) := by
      have := (even_two_mul b).sub heven
      rwa [sub_sub_cancel] at this
    exact (Int.even_pow.1 ha2).1
  obtain ⟨k, rfl⟩ := ha
  -- With `a = 2k`, Newton's identity reads `(a² - b)² = 4(2k⁴ - kc)`, so `a² - b` is even.
  have ht : Even ((k + k) ^ 2 - b) := by
    have h2 : 2 * (((k + k) ^ 2 - b) ^ 2 - 4 * (2 * k ^ 4 - k * c)) = 0 := by
      linear_combination -h
    have hsq : Even (((k + k) ^ 2 - b) ^ 2) := ⟨2 * (2 * k ^ 4 - k * c), by linarith⟩
    exact (Int.even_pow.1 hsq).1
  obtain ⟨m, hm⟩ := ht
  obtain rfl : b = (k + k) ^ 2 - (m + m) := by linarith
  have hy : 8 * (m ^ 2 - (2 * k ^ 4 - k * c)) = 0 := by linear_combination -h
  rcases hc' with rfl | rfl
  · exact ⟨-k, m, by linarith, by ring, by ring⟩
  · exact ⟨k, m, by linarith, by ring, by ring⟩

/-- **The fourth-power cubic `X³ - γ X - 16`.** Let `R` be a commutative ring of characteristic
zero and `a, b, c` integers. The Tschirnhaus transform of `X³ + a X² + b X + c` by `X⁴` is
`X³ - γ X - 16` exactly when `c = ±2` and there is an integer point `(u, y)` of the quartic
`y² = 2u(u³ + 1)` with `a = -c u`, `b = 4u² - 2y` and `γ = heegnerGamma u y`. -/
theorem tschirnhausPolynomial_X_pow_four_eq_iff {R : Type*} [CommRing R] [CharZero R]
    {a b c : ℤ} {γ : R} :
    tschirnhausPolynomial (X ^ 3 + C (a : R) * X ^ 2 + C (b : R) * X + C (c : R)) (X ^ 4) =
        X ^ 3 - C γ * X - 16 ↔
      (c = 2 ∨ c = -2) ∧ ∃ u y : ℤ, y ^ 2 = 2 * u * (u ^ 3 + 1) ∧ a = -c * u ∧
        b = 4 * u ^ 2 - 2 * y ∧ γ = heegnerGamma u y := by
  have hcubic (a' b' c' : R) :
      X ^ 3 + C a' * X ^ 2 + C b' * X - C c' = (⟨1, a', b', -c'⟩ : Cubic R).toPoly := by
    simp [Cubic.toPoly, sub_eq_add_neg]
  have hrhs : (X ^ 3 - C γ * X - 16 : R[X]) = (⟨1, 0, -γ, -16⟩ : Cubic R).toPoly := by
    simp only [Cubic.toPoly, map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, map_ofNat]
    ring
  rw [tschirnhausPolynomial_cubic_X_pow_four, hcubic, hrhs, Cubic.toPoly_injective]
  simp only [Cubic.mk.injEq, true_and, neg_inj]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h1' : 2 * (b ^ 2 - 2 * a * c) - (2 * b - a ^ 2) ^ 2 = 0 := by exact_mod_cast h1
    have h3' : c ^ 4 = 16 := by exact_mod_cast h3
    obtain ⟨hc, u, y, hy, rfl, rfl⟩ := exists_heegner_of_coeffs h3' h1'
    refine ⟨hc, u, y, hy, rfl, rfl, ?_⟩
    rw [← neg_neg γ, ← h2, heegnerGamma_def]
    rcases hc with rfl | rfl <;> push_cast <;> ring
  · rintro ⟨hc, u, y, hy, rfl, rfl, rfl⟩
    have hy' : (y : R) ^ 2 = 2 * u * (u ^ 3 + 1) := by exact_mod_cast hy
    rcases hc with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> push_cast [heegnerGamma_def] <;>
      first | ring1 | linear_combination (-8 : R) * hy'

/-- The values of `heegnerGamma` at the six integer points `(-1, 0)`, `(0, 0)`, `(1, ±2)`,
`(2, ±6)` of `y² = 2u(u³ + 1)` are `-96, 0, -32, -5280, -960, -640320`. -/
theorem heegnerGamma_mem {u y : ℤ}
    (h : (u, y) ∈ ({(-1, 0), (0, 0), (1, 2), (1, -2), (2, 6), (2, -6)} : Finset (ℤ × ℤ))) :
    heegnerGamma u y ∈ ({0, -32, -96, -960, -5280, -640320} : Finset ℤ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [heegnerGamma_def]

end TauCeti
