/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Model
public import TauCeti.NumberTheory.QuadraticOrder.PrimeIdeal
public import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.Algebra.Squarefree

/-!
# Explicit prime ideals of the ring of integers of `ℚ(√d)`

Let `d` be a squarefree nonsquare integer and `K = QuadraticAlgebra ℚ d 0` the model of `ℚ(√d)`.
Through the coordinate equivalences `QuadraticAlgebra.ringOfIntegersEquiv` (`𝓞 K ≅ ℤ[√d]` for
`d ≢ 1 (mod 4)`) and `QuadraticAlgebra.ringOfIntegersEquivHalf` (`𝓞 K ≅ ℤ[(1 + √d)/2]` for
`d ≡ 1 (mod 4)`), this file transports the explicit prime ideals of an integral quadratic algebra
(`TauCeti.NumberTheory.QuadraticOrder.PrimeIdeal`) to `𝓞 K`. Write `√d ∈ 𝓞 K` for
`NumberField.integralSqrt` and `η = (1 + √d)/2` for `NumberField.halfGen`. For every rational
prime `p`, the prime `2` included:

* if `d ≢ 1 (mod 4)` and `r² ≡ d (mod p)`, then `(p, √d - r)` is a maximal ideal of norm `p` and
  `(p) = (p, √d - r) (p, √d + r)`;
* if `d ≡ 1 (mod 4)` and `r² - r ≡ (d - 1)/4 (mod p)`, then `(p, η - r)` is a maximal ideal of
  norm `p` and `(p) = (p, η - r) (p, η - (1 - r))`;
* otherwise, when the relevant polynomial has no root modulo `p`, the ideal `(p)` is maximal:
  `p` is inert.

The two factors coincide exactly in the ramified case, so together these cover split, ramified
and inert primes. The factorization needs no case distinction at `2`, because Dedekind's criterion
holds at every `p` in the maximal order. By
contrast, in the order `ℤ[√d]` of conductor `2` with `d ≡ 1 (mod 4)` the criterion fails at `2`:
`(2, √d - 1)² ≠ (2)` (`QuadraticAlgebra.span_two_omega_sub_one_sq_ne_span_two`).

## Main results

* `QuadraticAlgebra.map_ringOfIntegersEquiv_symm_span`,
  `map_ringOfIntegersEquivHalf_symm_span`: the ideal `(p, ω - r)` of the integral model
  corresponds to `(p, √d - r)`, respectively `(p, η - r)`, in `𝓞 K`.
* `QuadraticAlgebra.isMaximal_span_natCast_integralSqrt_sub`,
  `absNorm_span_natCast_integralSqrt_sub`,
  `span_natCast_integralSqrt_sub_mul_span_natCast_integralSqrt_add`,
  `isMaximal_span_natCast_iff_of_mod_four_ne_one`: the case `d ≢ 1 (mod 4)`.
* `QuadraticAlgebra.isMaximal_span_natCast_halfGen_sub`, `absNorm_span_natCast_halfGen_sub`,
  `span_natCast_halfGen_sub_mul_span_natCast_halfGen_sub`,
  `isMaximal_span_natCast_iff_of_mod_four_eq_one`: the case `d ≡ 1 (mod 4)`.

## References

* D. A. Marcus, *Number Fields*, Chapter 3, Theorem 25.
* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
-/

public section

open NumberField

namespace QuadraticAlgebra

variable {d : ℤ} [Fact (¬ IsSquare d)] {p : ℕ} [Fact p.Prime] {r : ℤ}

/-! ### Transport along a coordinate equivalence -/

section Transport

variable {a b : ℤ} (e : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) ≃ₐ[ℤ] QuadraticAlgebra ℤ a b)

omit [Fact p.Prime] in
private theorem map_symm_span_pair (r : ℤ) :
    (Ideal.span {(p : QuadraticAlgebra ℤ a b), ω - (r : QuadraticAlgebra ℤ a b)}).map e.symm =
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)), e.symm ω - r} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast, map_sub, map_intCast]

omit [Fact p.Prime] in
private theorem map_symm_span_natCast :
    (Ideal.span {(p : QuadraticAlgebra ℤ a b)}).map e.symm =
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

omit [Fact p.Prime] in
private theorem isMaximal_map_symm_iff (I : Ideal (QuadraticAlgebra ℤ a b)) :
    (I.map e.symm).IsMaximal ↔ I.IsMaximal :=
  Ideal.isMaximal_map_iff_of_bijective _ e.symm.bijective

end Transport

/-! ### The case `d ≢ 1 (mod 4)` -/

section ModFourNeOne

variable (hsf : Squarefree d) (hd4 : d % 4 ≠ 1)

omit [Fact p.Prime] in
/-- **Ideal transport for `d ≢ 1 (mod 4)`.** The ideal `(p, ω - r)` of `ℤ[√d]` corresponds to
the ideal `(p, √d - r)` of `𝓞 ℚ(√d)`. -/
theorem map_ringOfIntegersEquiv_symm_span (r : ℤ) :
    (Ideal.span {(p : QuadraticAlgebra ℤ d 0), ω - (r : QuadraticAlgebra ℤ d 0)}).map
        (ringOfIntegersEquiv hsf hd4).symm =
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
        integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r} := by
  rw [map_symm_span_pair, ringOfIntegersEquiv_symm_omega]

include hsf hd4 in
/-- **The prime `(p, √d - r)`.** For `d ≢ 1 (mod 4)` and a square root `r` of `d` modulo `p`,
the ideal `(p, √d - r)` of `𝓞 ℚ(√d)` is maximal. -/
theorem isMaximal_span_natCast_integralSqrt_sub (hr : (p : ℤ) ∣ r ^ 2 - d) :
    (Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
      integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r}).IsMaximal := by
  rw [← map_ringOfIntegersEquiv_symm_span hsf hd4, isMaximal_map_symm_iff]
  exact isMaximal_span_natCast_omega_sub (by simpa using hr)

omit [Fact p.Prime] in
include hsf hd4 in
/-- **The norm of `(p, √d - r)` is `p`.** -/
@[simp]
theorem absNorm_span_natCast_integralSqrt_sub (hr : (p : ℤ) ∣ r ^ 2 - d) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
      integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r}) = p := by
  rw [← map_ringOfIntegersEquiv_symm_span hsf hd4, Ideal.absNorm_map_of_ringEquiv_eq_natCard]
  exact card_quotient_span_natCast_omega_sub (by simpa using hr)

include hsf hd4 in
/-- **The factorization of `p` for `d ≢ 1 (mod 4)`.** For a square root `r` of `d` modulo a prime
`p`, the ideal `p 𝓞 ℚ(√d)` is the product `(p, √d - r) (p, √d + r)` of two maximal ideals of
norm `p`. The two factors coincide exactly when `p ∣ 2r` (`span_natCast_omega_sub_eq_iff`),
which is the ramified case. -/
theorem span_natCast_integralSqrt_sub_mul_span_natCast_integralSqrt_add
    (hr : (p : ℤ) ∣ r ^ 2 - d) :
    Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
        integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r} *
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
        integralSqrt (omega_sq_eq_algebraMap_int (d := d)) + r} =
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} := by
  have hr' : (p : ℤ) ∣ r ^ 2 - 0 * r - d := by simpa using hr
  have h := (span_natCast_omega_sub_mul_span_natCast_omega_sub_eq_iff hr').mpr <| by
    simpa using TauCeti.Int.not_dvd_two_mul_and_sq_dvd_sq_sub_of_squarefree
      (Nat.prime_iff_prime_int.mp Fact.out) hsf hd4 r
  have h' := congrArg (Ideal.map (ringOfIntegersEquiv hsf hd4).symm) h
  rw [Ideal.map_mul, map_ringOfIntegersEquiv_symm_span, map_ringOfIntegersEquiv_symm_span,
    map_symm_span_natCast] at h'
  simpa [sub_eq_add_neg] using h'

include hsf hd4 in
/-- **Inert primes for `d ≢ 1 (mod 4)`.** The ideal `p 𝓞 ℚ(√d)` is maximal exactly when `d` is
not a square modulo `p`. -/
theorem isMaximal_span_natCast_iff_of_mod_four_ne_one :
    (Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))}).IsMaximal ↔
      ∀ r : ℤ, ¬ (p : ℤ) ∣ r ^ 2 - d := by
  rw [← map_symm_span_natCast (ringOfIntegersEquiv hsf hd4), isMaximal_map_symm_iff,
    isMaximal_span_natCast_iff]
  simp

end ModFourNeOne

/-! ### The case `d ≡ 1 (mod 4)` -/

section ModFourEqOne

variable (hsf : Squarefree d) (hd4 : d % 4 = 1)

omit [Fact p.Prime] in
/-- **Ideal transport for `d ≡ 1 (mod 4)`.** The ideal `(p, ω - r)` of `ℤ[(1 + √d)/2]`
corresponds to the ideal `(p, η - r)` of `𝓞 ℚ(√d)`, where `η = (1 + √d)/2`. -/
theorem map_ringOfIntegersEquivHalf_symm_span (r : ℤ) :
    (Ideal.span {(p : QuadraticAlgebra ℤ ((d - 1) / 4) 1),
      ω - (r : QuadraticAlgebra ℤ ((d - 1) / 4) 1)}).map (ringOfIntegersEquivHalf hsf hd4).symm =
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
        halfGen minpoly_integralSqrt_omega hd4 - r} := by
  rw [map_symm_span_pair, ringOfIntegersEquivHalf_symm_omega]

include hsf in
/-- **The prime `(p, η - r)`.** For `d ≡ 1 (mod 4)` and a root `r` of `X² - X - (d - 1)/4`
modulo `p`, the ideal `(p, η - r)` of `𝓞 ℚ(√d)`, `η = (1 + √d)/2`, is maximal. -/
theorem isMaximal_span_natCast_halfGen_sub (hr : (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4) :
    (Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
      halfGen minpoly_integralSqrt_omega hd4 - r}).IsMaximal := by
  rw [← map_ringOfIntegersEquivHalf_symm_span hsf hd4, isMaximal_map_symm_iff]
  exact isMaximal_span_natCast_omega_sub (by simpa using hr)

omit [Fact p.Prime] in
include hsf in
/-- **The norm of `(p, η - r)` is `p`.** -/
@[simp]
theorem absNorm_span_natCast_halfGen_sub (hr : (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
      halfGen minpoly_integralSqrt_omega hd4 - r}) = p := by
  rw [← map_ringOfIntegersEquivHalf_symm_span hsf hd4, Ideal.absNorm_map_of_ringEquiv_eq_natCard]
  exact card_quotient_span_natCast_omega_sub (by simpa using hr)

include hsf in
/-- **The factorization of `p` for `d ≡ 1 (mod 4)`.** For a root `r` of `X² - X - (d - 1)/4`
modulo a prime `p`, the ideal `p 𝓞 ℚ(√d)` is the product `(p, η - r) (p, η - (1 - r))` of two
maximal ideals of norm `p`, where `η = (1 + √d)/2`. The two factors coincide exactly when
`p ∣ 2r - 1` (`span_natCast_omega_sub_eq_iff`), which is the ramified case. -/
theorem span_natCast_halfGen_sub_mul_span_natCast_halfGen_sub
    (hr : (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4) :
    Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
        halfGen minpoly_integralSqrt_omega hd4 - r} *
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
        halfGen minpoly_integralSqrt_omega hd4 - (1 - r : ℤ)} =
      Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} := by
  have hr' : (p : ℤ) ∣ r ^ 2 - 1 * r - (d - 1) / 4 := by simpa using hr
  have h := (span_natCast_omega_sub_mul_span_natCast_omega_sub_eq_iff hr').mpr <| by
    simpa using TauCeti.Int.not_dvd_two_mul_sub_one_and_sq_dvd_sq_sub_sub_of_squarefree
      (Nat.prime_iff_prime_int.mp Fact.out) hsf hd4 r
  have h' := congrArg (Ideal.map (ringOfIntegersEquivHalf hsf hd4).symm) h
  rwa [Ideal.map_mul, map_ringOfIntegersEquivHalf_symm_span,
    map_ringOfIntegersEquivHalf_symm_span, map_symm_span_natCast] at h'

include hsf hd4 in
/-- **Inert primes for `d ≡ 1 (mod 4)`.** The ideal `p 𝓞 ℚ(√d)` is maximal exactly when
`X² - X - (d - 1)/4` has no root modulo `p`. -/
theorem isMaximal_span_natCast_iff_of_mod_four_eq_one :
    (Ideal.span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))}).IsMaximal ↔
      ∀ r : ℤ, ¬ (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4 := by
  rw [← map_symm_span_natCast (ringOfIntegersEquivHalf hsf hd4), isMaximal_map_symm_iff,
    isMaximal_span_natCast_iff]
  simp

end ModFourEqOne

end QuadraticAlgebra
