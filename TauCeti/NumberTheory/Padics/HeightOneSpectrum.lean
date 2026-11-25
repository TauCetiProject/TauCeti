/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Units at the height-one primes of `ℚ`

Let `R` be the ring of integers of `ℚ` in the sense of `IsIntegralClosure R ℤ ℚ`, and let `v` be a
height-one prime of `R`, corresponding to the rational prime
`p = Rat.HeightOneSpectrum.primesEquiv v`.
This file compares the `v`-adic valuation with the `p`-adic valuation `padicValRat p`, and records
that `ℤ` has infinitely many height-one prime ideals. For `R = ℤ` it identifies the height-one
prime corresponding to a rational prime `p` with the ideal `(p)`.

## Main results

* `Infinite (HeightOneSpectrum ℤ)`: `ℤ` has infinitely many height-one prime ideals.
* `Rat.HeightOneSpectrum.valuation_eq_one_iff_padicValRat_eq_zero`: a nonzero rational number is
  a unit at `v` exactly when its `p`-adic valuation vanishes.
* `Rat.HeightOneSpectrum.asIdeal_primesEquiv_symm`: the height-one prime of `ℤ` corresponding to
  the prime `p` is `(p)`.
* `Rat.HeightOneSpectrum.liesOver_asIdeal_primesEquiv_symm_iff`: a prime ideal lies over it exactly
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

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R]
  [IsFractionRing R ℚ]

/-- A nonzero rational number is a unit at the height-one prime `v` exactly when its `p`-adic
valuation vanishes, for `p` the rational prime corresponding to `v`. -/
theorem valuation_eq_one_iff_padicValRat_eq_zero (v : HeightOneSpectrum R) {x : ℚ}
    (hx : x ≠ 0) : v.valuation ℚ x = 1 ↔ padicValRat (primesEquiv v) x = 0 := by
  have : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).property⟩
  rw [(valuation_equiv_padicValuation v).eq_one_iff_eq_one]
  simp [Rat.padicValuation, hx]

/-- The height-one prime of `ℤ` corresponding to the prime `p` under `primesEquiv` is the ideal
`(p)`. -/
@[simp]
theorem asIdeal_primesEquiv_symm (p : Nat.Primes) :
    ((primesEquiv (R := ℤ)).symm p).asIdeal = Ideal.span {((p : ℕ) : ℤ)} := by
  -- the only ring automorphism of `ℤ` is the identity
  have h : (IsIntegralClosure.intEquiv ℤ).symm = RingEquiv.refl ℤ := RingEquiv.ext fun _ ↦ by simp
  -- Mathlib defines the inverse of `primesEquiv` as the image of `(p)` under `intEquiv.symm`.
  change (Ideal.span {((p : ℕ) : ℤ)}).map (IsIntegralClosure.intEquiv ℤ).symm = _
  rw [h]
  exact Ideal.map_id _

/-- A prime ideal `P` of a commutative ring lies over the height-one prime of `ℤ` corresponding to
the prime `p` exactly when `p ∈ P`. -/
theorem liesOver_asIdeal_primesEquiv_symm_iff {S : Type*} [CommRing S] (P : Ideal S) [P.IsPrime]
    (p : Nat.Primes) :
    P.LiesOver ((primesEquiv (R := ℤ)).symm p).asIdeal ↔ ((p : ℕ) : S) ∈ P := by
  rw [asIdeal_primesEquiv_symm,
    Ideal.liesOver_span_iff Ideal.IsPrime.ne_top' (Nat.prime_iff_prime_int.1 p.property)]
  simp

end Rat.HeightOneSpectrum
