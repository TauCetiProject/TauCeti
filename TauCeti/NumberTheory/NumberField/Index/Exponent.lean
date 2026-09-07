/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import TauCeti.NumberTheory.NumberField.Index.Discriminant
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The index and the conductor exponent have the same prime divisors

For an integral primitive element `θ` of a number field `K`, two integers measure how far the
order `ℤ[θ]` is from `𝓞 K`: the index `[𝓞 K : ℤ[θ]]` (`IntegralPrimitiveElement.index`) and the
conductor exponent `RingOfIntegers.exponent θ`, the least positive integer `e` with
`e • 𝓞 K ⊆ ℤ[θ]`. They are different integers in general, but they have the same prime
divisors: the exponent divides the index, since the finite group `𝓞 K / ℤ[θ]` is killed by its
order, and every prime dividing the order of that group divides its exponent, by Cauchy's
theorem.

Combined with the index formula `disc (minpoly ℤ θ) = [𝓞 K : ℤ[θ]]² · disc K`, this gives the
hypothesis of the Kummer–Dedekind theorem in checkable form: a prime not dividing the
discriminant of the minimal polynomial does not divide the conductor exponent.

## Main results

* `RingOfIntegers.exponent_dvd_iff`: the conductor exponent of `θ` divides `n` exactly
  when `n` lies in the conductor of `ℤ[θ]`.
* `TauCeti.NumberField.IntegralPrimitiveElement.dvd_index_iff_dvd_exponent`: a prime divides the
  index exactly when it divides the conductor exponent.
* `TauCeti.NumberField.IntegralPrimitiveElement.not_dvd_exponent_of_not_dvd_discr_minpoly`: a
  natural number not dividing `disc (minpoly ℤ θ)` does not divide the conductor exponent.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §8.
-/

public section

open scoped NumberField
open RingOfIntegers

namespace RingOfIntegers

variable {K : Type*} [Field K]

/-- The conductor exponent of `θ` divides `n` exactly when `n` lies in the conductor of
`ℤ[θ]`. -/
theorem exponent_dvd_iff (θ : 𝓞 K) {n : ℕ} : exponent θ ∣ n ↔ (n : 𝓞 K) ∈ conductor ℤ θ := by
  rw [← Int.natCast_dvd_natCast, ← Ideal.mem_span_singleton, exponent,
    Int.ideal_span_absNorm_eq_self, Ideal.under_def, Ideal.mem_comap, map_natCast]

end RingOfIntegers

namespace TauCeti.NumberField.IntegralPrimitiveElement

variable {K : Type*} [Field K] [NumberField K]

/-- A multiple `n • b` vanishes in the quotient `𝓞 K / ℤ[θ]` exactly when `n * b` lies in the
order `ℤ[θ]`. -/
theorem nsmul_mkQ_eq_zero_iff (θ : IntegralPrimitiveElement K) (n : ℕ) (b : 𝓞 K) :
    (n • θ.adjoin.toSubmodule.mkQ b : θ.Quotient) = 0 ↔ (n : 𝓞 K) * b ∈ θ.adjoin := by
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Subalgebra.mem_toSubmodule,
    nsmul_eq_mul]

/-- The conductor exponent of `θ` divides the index `[𝓞 K : ℤ[θ]]`. -/
theorem exponent_dvd_index (θ : IntegralPrimitiveElement K) : exponent θ.1 ∣ θ.index := by
  rw [exponent_dvd_iff, mem_conductor_iff]
  intro b
  rw [← adjoin_def, ← nsmul_mkQ_eq_zero_iff, index_def]
  exact card_nsmul_eq_zero'

/-- A prime dividing the index `[𝓞 K : ℤ[θ]]` divides the conductor exponent of `θ`. -/
theorem dvd_exponent_of_dvd_index (θ : IntegralPrimitiveElement K) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ θ.index) : p ∣ exponent θ.1 := by
  classical
  have : Fintype θ.Quotient := Fintype.ofFinite _
  rw [index_def, Nat.card_eq_fintype_card] at hp
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hp
  rw [← hx]
  refine (AddMonoid.addOrder_dvd_exponent x).trans ?_
  rw [AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero]
  intro g
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ g
  rw [nsmul_mkQ_eq_zero_iff, adjoin_def]
  exact mem_conductor_iff.mp ((exponent_dvd_iff θ.1).mp dvd_rfl) b

/-- **Index and exponent have the same prime divisors.** A prime divides the index
`[𝓞 K : ℤ[θ]]` exactly when it divides the conductor exponent of `θ`. -/
theorem dvd_index_iff_dvd_exponent (θ : IntegralPrimitiveElement K) {p : ℕ} [Fact p.Prime] :
    p ∣ θ.index ↔ p ∣ exponent θ.1 :=
  ⟨θ.dvd_exponent_of_dvd_index, fun h => h.trans θ.exponent_dvd_index⟩

/-- **The checkable Kummer–Dedekind hypothesis.** A natural number not dividing the discriminant
of `minpoly ℤ θ` does not divide the conductor exponent of `θ`. -/
theorem not_dvd_exponent_of_not_dvd_discr_minpoly (θ : IntegralPrimitiveElement K) {p : ℕ}
    (hp : ¬ (p : ℤ) ∣ (minpoly ℤ θ.1).discr) : ¬ p ∣ exponent θ.1 := by
  intro h
  apply hp
  rw [θ.discr_minpoly_eq_index_sq_mul_discr]
  exact (dvd_pow (Int.natCast_dvd_natCast.mpr (h.trans θ.exponent_dvd_index))
    two_ne_zero).mul_right _

end TauCeti.NumberField.IntegralPrimitiveElement
