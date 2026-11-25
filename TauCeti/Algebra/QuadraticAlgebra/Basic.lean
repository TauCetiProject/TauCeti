/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Powers of the generator and the norm form of a quadratic algebra

For the quadratic algebra `R[√r]` over any commutative semiring, powers of the generator
alternate between scalars at even exponents and scalar multiples of the generator at odd
exponents. These formulas include exponent zero and do not require finite-field hypotheses.

If `X² - t X - n` has no root in a field, the binary quadratic form `a² + t a b - n b²`, the norm
form of `F[X] / (X² - t X - n)`, has no nontrivial zero
(`TauCeti.sq_add_mul_mul_sub_mul_sq_eq_zero_iff`).
-/

public section

namespace QuadraticAlgebra

/-- For odd `n`, the `n`-th power of the generator of `R[√r]` is `r ^ (n / 2) • ω`. -/
theorem omega_pow_of_odd {R : Type*} [CommSemiring R] {r : R} {n : ℕ} (hn : Odd n) :
    (ω : QuadraticAlgebra R r 0) ^ n = r ^ (n / 2) • ω := by
  conv_lhs => rw [← Nat.two_mul_div_two_add_one_of_odd hn]
  rw [pow_succ, pow_mul, sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
    ← map_pow, ← Algebra.smul_def]

/-- For even `n`, the `n`-th power of the generator of `R[√r]` is the scalar `r ^ (n / 2)`. -/
theorem omega_pow_of_even {R : Type*} [CommSemiring R] {r : R} {n : ℕ} (hn : Even n) :
    (ω : QuadraticAlgebra R r 0) ^ n = algebraMap R _ (r ^ (n / 2)) := by
  conv_lhs => rw [← Nat.two_mul_div_two_of_even hn]
  rw [pow_mul, sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero, ← map_pow]

end QuadraticAlgebra

namespace TauCeti

/-- **A quadratic without roots has an anisotropic norm form.** If `X² - t X - n` has no root in
the field `F`, then `a² + t a b - n b²` vanishes only at `a = b = 0`: for `b ≠ 0` a zero would make
`-a / b` a root. This is `QuadraticAlgebra.norm_eq_zero_iff_eq_zero` in coordinates. -/
theorem sq_add_mul_mul_sub_mul_sq_eq_zero_iff {F : Type*} [Field F] {t n : F}
    (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) {a b : F} :
    a ^ 2 + t * a * b - n * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  have : Fact (∀ x : F, x ^ 2 ≠ n + t * x) := ⟨fun x ↦ add_comm n (t * x) ▸ hirr x⟩
  simpa [QuadraticAlgebra.norm_def, QuadraticAlgebra.ext_iff, sq, mul_assoc] using
    QuadraticAlgebra.norm_eq_zero_iff_eq_zero (z := (⟨a, b⟩ : QuadraticAlgebra F n t))

end TauCeti
