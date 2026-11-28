/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# The generator of a quadratic algebra

For the quadratic algebra `R[√r]` over any commutative semiring, powers of the generator
alternate between scalars at even exponents and scalar multiples of the generator at odd
exponents. These formulas include exponent zero and do not require finite-field hypotheses.

When the defining relation is `ω² = -1 + bω`, the generator is a unit, with inverse `b - ω`.
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

open scoped QuadraticAlgebra

namespace TauCeti.QuadraticAlgebra

/-- The coordinate generator of `QuadraticAlgebra R (-1) b` as a unit, with inverse `b - ω`. -/
def omegaUnit {R : Type*} [CommRing R] (b : R) : (QuadraticAlgebra R (-1) b)ˣ :=
  Units.mkOfMulEqOne ω (algebraMap R _ b - ω) (by ext <;> simp)

/-- The underlying value of `omegaUnit b` is the coordinate generator `ω`. -/
@[simp] theorem omegaUnit_val {R : Type*} [CommRing R] (b : R) :
    (omegaUnit b : QuadraticAlgebra R (-1) b) = ω := (rfl)

/-- The inverse of `omegaUnit b` has underlying value `b - ω`. -/
@[simp] theorem omegaUnit_inv_val {R : Type*} [CommRing R] (b : R) :
    (↑((omegaUnit b)⁻¹) : QuadraticAlgebra R (-1) b) = algebraMap R _ b - ω := (rfl)

/-- Coefficient change sends the generator unit to the generator unit. The coefficient
`f (-1)` in `mapRingHom` is identified with `-1` by the ring homomorphism laws; the optional
proof argument allows callers to use their chosen transport. Use this equation to rewrite
transported units. For the underlying value of the untransported `Units.map`, `simp` uses
`Units.coe_map`, `omegaUnit_val`, and `QuadraticAlgebra.mapRingHom_omega`. -/
theorem _root_.RingHom.map_omegaUnit {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (b : R) (h : f (-1) = (-1 : S) := by simp) :
    Units.map (h ▸
      (_root_.QuadraticAlgebra.mapRingHom f (-1) b).toMonoidHom) (omegaUnit b) =
      omegaUnit (f b) := by
  apply Units.ext
  simp only [Units.coe_map, omegaUnit_val]
  suffices ∀ (a a' : S) (h : a = a')
      (g : QuadraticAlgebra R (-1) b →* QuadraticAlgebra S a (f b)),
      g ω = ω → (h ▸ g) ω = ω from
    this _ _ _ _ (_root_.QuadraticAlgebra.mapRingHom_omega f (-1) b)
  intro a a' h g hg
  subst a'
  exact hg

end TauCeti.QuadraticAlgebra
