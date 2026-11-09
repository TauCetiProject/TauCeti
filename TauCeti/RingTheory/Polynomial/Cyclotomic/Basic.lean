/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Basic identities for cyclotomic polynomials

`Polynomial.cyclotomic_five` gives the fifth cyclotomic polynomial as the finite geometric
sum `X⁴ + X³ + X² + X + 1` over any ring.

Mathlib defines `Φ₅` abstractly, as a product over primitive roots of unity, and only unfolds it
to a sum through `Polynomial.cyclotomic_prime`. Recording the expanded form once, as a `simp`
lemma over an arbitrary ring, lets explicit factorisation and Galois-group computations work with
the concrete coefficients directly. It is used for the factorisation of `Φ₅` over a field
containing `√5` in `TauCeti.RingTheory.Polynomial.Cyclotomic.SqrtFive`, and to identify
`X⁴ + X³ + X² + X + 1` with `Φ₅` in the worked quartic examples in
`TauCeti.FieldTheory.GaloisGroups.Quartic.Examples`, where its Galois group over `ℚ` is
computed as `(ℤ/5)ˣ`.

`Polynomial.cyclotomic_twelve`, `Polynomial.cyclotomic_eighteen` and
`Polynomial.cyclotomic_thirty` expand `Φ₁₂`, `Φ₁₈` and `Φ₃₀` in the same way, which is what is
needed to check that these polynomials annihilate an explicit matrix.

Over any ring, `Polynomial.monic_cyclotomic_comp_X_add_one` and
`Polynomial.natDegree_cyclotomic_comp_X_add_one` record that the shifted cyclotomic polynomial
`Φ_n(X + 1)` is monic of degree `φ(n)`. They are used for the shifted prime-power cyclotomic
polynomials in `TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow`.
-/

public section

namespace Polynomial

/-- The fifth cyclotomic polynomial is `X ^ 4 + X ^ 3 + X ^ 2 + X + 1`. -/
@[simp]
theorem cyclotomic_five (R : Type*) [Ring R] : cyclotomic 5 R = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  abel

/-- The twelfth cyclotomic polynomial is `X ^ 4 - X ^ 2 + 1`. -/
@[simp]
theorem cyclotomic_twelve (R : Type*) [Ring R] : cyclotomic 12 R = X ^ 4 - X ^ 2 + 1 := by
  suffices cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  rw [show (12 : ℕ) = 6 * 2 from rfl,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide), cyclotomic_six]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

/-- The eighteenth cyclotomic polynomial is `X ^ 6 - X ^ 3 + 1`. -/
@[simp]
theorem cyclotomic_eighteen (R : Type*) [Ring R] : cyclotomic 18 R = X ^ 6 - X ^ 3 + 1 := by
  suffices cyclotomic 18 ℤ = X ^ 6 - X ^ 3 + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  rw [show (18 : ℕ) = 6 * 3 from rfl,
    ← cyclotomic_expand_eq_cyclotomic Nat.prime_three (by decide), cyclotomic_six]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

/-- The thirtieth cyclotomic polynomial is `X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1`. -/
@[simp]
theorem cyclotomic_thirty (R : Type*) [Ring R] :
    cyclotomic 30 R = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  suffices cyclotomic 30 ℤ = X ^ 8 + X ^ 7 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 by
    rw [← map_cyclotomic_int, this]
    simp
  have h := cyclotomic_expand_eq_cyclotomic_mul (p := 5) (n := 6) Nat.prime_five (by decide) ℤ
  apply mul_right_cancel₀ (cyclotomic_ne_zero 6 ℤ)
  rw [show (30 : ℕ) = 6 * 5 from rfl, ← h, cyclotomic_six]
  simp only [map_add, map_sub, map_pow, expand_X, map_one]
  ring

section Ring

variable {R : Type*} [Ring R]

/-- `Φ_n(X + 1)` has degree `φ(n)`. -/
@[simp]
theorem natDegree_cyclotomic_comp_X_add_one [Nontrivial R] (n : ℕ) :
    ((cyclotomic n R).comp (X + 1)).natDegree = n.totient := by
  have h1 : (X + 1 : R[X]).leadingCoeff = 1 := by simpa using (monic_X_add_C (1 : R)).leadingCoeff
  rw [natDegree_comp_eq_of_mul_ne_zero (by simp [(cyclotomic.monic n R).leadingCoeff, h1]),
    natDegree_cyclotomic]
  simp

/-- `Φ_n(X + 1)` is monic. -/
theorem monic_cyclotomic_comp_X_add_one (n : ℕ) : ((cyclotomic n R).comp (X + 1)).Monic := by
  simpa using (cyclotomic.monic n R).comp_X_add_C 1

end Ring

end Polynomial
