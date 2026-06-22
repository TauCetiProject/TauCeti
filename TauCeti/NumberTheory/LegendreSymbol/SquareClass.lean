/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Legendre symbols and square-class changes of radicand

Replacing an integer `a` by `a * u ^ 2`, with `p ∤ u`, changes neither whether `p` divides it
nor its Legendre symbol modulo `p`. This file records that elementary single-variable API:
the positive divisibility equivalence `dvd_mul_sq_iff` and its negation `not_dvd_mul_sq_iff`,
and the Legendre-symbol invariance `legendreSym_mul_sq`.

These facts are generic Legendre-symbol and divisibility statements; the indexed-family
wrappers consumed by the multiquadratic splitting law live in
`TauCeti.NumberTheory.Multiquadratic.LegendreSquareClass`.
-/

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- An integer prime from the ambient natural prime `p`. -/
private theorem prime_intCast_of_fact : Prime (p : ℤ) :=
  Nat.prime_iff_prime_int.mp Fact.out

/-- For `u` with `p ∤ u`, the prime `p` divides `a * u ^ 2` exactly when it divides `a`. -/
theorem dvd_mul_sq_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    (p : ℤ) ∣ a * u ^ 2 ↔ (p : ℤ) ∣ a := by
  refine ⟨fun h => ?_, fun ha => dvd_mul_of_dvd_left ha _⟩
  rcases (prime_intCast_of_fact (p := p)).dvd_mul.mp h with ha | hu2
  · exact ha
  · exact absurd ((prime_intCast_of_fact (p := p)).dvd_of_dvd_pow hu2) hu

/-- Multiplying by `u ^ 2` with `p ∤ u` preserves non-divisibility by `p`. -/
theorem not_dvd_mul_sq_iff {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ¬ (p : ℤ) ∣ a * u ^ 2 ↔ ¬ (p : ℤ) ∣ a :=
  not_congr (dvd_mul_sq_iff hu)

/-- Multiplying an integer by `u ^ 2` with `p ∤ u` does not change its Legendre symbol. -/
theorem legendreSym_mul_sq {a u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    legendreSym p (a * u ^ 2) = legendreSym p a := by
  rw [legendreSym.mul,
    legendreSym.sq_one' p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]), mul_one]

end TauCeti
