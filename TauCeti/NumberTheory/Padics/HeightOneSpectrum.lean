/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import TauCeti.NumberTheory.Padics.PadicValRat

/-!
# Units at the height-one primes of `ℚ`

Let `R` be the ring of integers of `ℚ` in the sense of `IsIntegralClosure R ℤ ℚ`, and let `v` be a
height-one prime of `R`, corresponding to the rational prime
`p = Rat.HeightOneSpectrum.primesEquiv v`.
This file compares the `v`-adic valuation with the `p`-adic valuation `padicValRat p`, and records
that `ℤ` has infinitely many height-one prime ideals. It identifies the height-one prime of `R`
corresponding to a rational prime `p` with the ideal `(p)`.

## Main results

* `Infinite (HeightOneSpectrum ℤ)`: `ℤ` has infinitely many height-one prime ideals.
* `Rat.HeightOneSpectrum.fact_prime_natGenerator`: the rational prime `natGenerator v` of `v` is
  prime, as an instance.
* `Rat.HeightOneSpectrum.valuation_eq_one_iff_padicValRat_eq_zero`: a nonzero rational number is
  a unit at `v` exactly when its `p`-adic valuation vanishes.
* `Rat.HeightOneSpectrum.valuation_eq_one_of_not_dvd`: a rational number whose numerator
  and denominator are prime to `p` is a unit at `v`.
* `Rat.HeightOneSpectrum.asIdeal_primesEquiv_symm`: the height-one prime of `R` corresponding to
  the prime `p` is `(p)`.
* `Rat.HeightOneSpectrum.liesOver_asIdeal_primesEquiv_symm_iff`: a proper ideal lies over it exactly
  when it contains `p`.
-/

public section

open IsDedekindDomain

namespace TauCeti

/-- `ℤ` has infinitely many height-one prime ideals, in bijection with the rational primes. -/
instance : Infinite (HeightOneSpectrum ℤ) :=
  Infinite.of_surjective _ Rat.HeightOneSpectrum.primesEquiv.surjective

end TauCeti

namespace Rat.HeightOneSpectrum

/-- The rational prime of a height-one prime of the ring of integers of `ℚ` is prime. -/
instance fact_prime_natGenerator {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    (v : HeightOneSpectrum R) : Fact (natGenerator v).Prime :=
  ⟨prime_natGenerator v⟩

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R]
  [IsFractionRing R ℚ]

omit [IsFractionRing R ℚ] in
/-- The rational prime corresponding to `v` under `primesEquiv` is `natGenerator v`. -/
theorem coe_primesEquiv (v : HeightOneSpectrum R) : (primesEquiv v : ℕ) = natGenerator v :=
  rfl

omit [IsFractionRing R ℚ] in
/-- The rational prime of the height-one prime corresponding to `p` under `primesEquiv` is `p`. -/
@[simp]
theorem natGenerator_primesEquiv_symm (p : Nat.Primes) :
    natGenerator ((primesEquiv (R := R)).symm p) = p := by
  rw [← coe_primesEquiv, Equiv.apply_symm_apply]

omit [IsFractionRing R ℚ] in
/-- Distinct height-one primes have distinct rational primes. -/
theorem natGenerator_injective : Function.Injective (natGenerator (R := R)) := fun v w h ↦
  primesEquiv.injective <| Subtype.ext <| by rw [coe_primesEquiv, coe_primesEquiv, h]

/-- A nonzero rational number is a unit at the height-one prime `v` exactly when its `p`-adic
valuation vanishes, for `p` the rational prime corresponding to `v`. -/
theorem valuation_eq_one_iff_padicValRat_eq_zero (v : HeightOneSpectrum R) {x : ℚ}
    (hx : x ≠ 0) : v.valuation ℚ x = 1 ↔ padicValRat (primesEquiv v) x = 0 := by
  have : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).property⟩
  rw [(valuation_equiv_padicValuation v).eq_one_iff_eq_one]
  simp [Rat.padicValuation, hx]

/-- A rational number whose numerator and denominator are prime to the rational prime
`natGenerator v` is a unit at the height-one prime `v`. -/
theorem valuation_eq_one_of_not_dvd (v : HeightOneSpectrum R) {x : ℚ}
    (hnum : ¬natGenerator v ∣ x.num.natAbs) (hden : ¬natGenerator v ∣ x.den) :
    v.valuation ℚ x = 1 := by
  have hx : x ≠ 0 := by rintro rfl; exact hnum (by simp)
  rw [valuation_eq_one_iff_padicValRat_eq_zero v hx, coe_primesEquiv]
  exact (padicValRat.eq_zero_iff hx).2 ⟨hnum, hden⟩

omit [IsFractionRing R ℚ] in
/-- The height-one prime of `R` corresponding to the prime `p` under `primesEquiv` is the ideal
`(p)`. -/
@[simp]
theorem asIdeal_primesEquiv_symm (p : Nat.Primes) :
    ((primesEquiv (R := R)).symm p).asIdeal = Ideal.span {((p : ℕ) : R)} := by
  -- Mathlib defines the inverse of `primesEquiv` as the image of `(p)` under `intEquiv.symm`.
  change (Ideal.span {((p : ℕ) : ℤ)}).map (IsIntegralClosure.intEquiv R).symm = _
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

omit [IsFractionRing R ℚ] in
/-- A proper ideal `P` of an `R`-algebra lies over the height-one prime of `R` corresponding to
the prime `p` exactly when `p ∈ P`. -/
theorem liesOver_asIdeal_primesEquiv_symm_iff {S : Type*} [CommRing S] [Algebra R S] {P : Ideal S}
    (hP : P ≠ ⊤) (p : Nat.Primes) :
    P.LiesOver ((primesEquiv (R := R)).symm p).asIdeal ↔ ((p : ℕ) : S) ∈ P := by
  have hp : Prime ((p : ℕ) : R) := by
    rw [← map_natCast (IsIntegralClosure.intEquiv R).symm, MulEquiv.prime_iff]
    exact Nat.prime_iff_prime_int.1 p.property
  rw [asIdeal_primesEquiv_symm, Ideal.liesOver_span_iff hP hp]
  simp

end Rat.HeightOneSpectrum
