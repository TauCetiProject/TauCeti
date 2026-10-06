/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Prime

/-!
# The projective Weierstrass polynomial is prime

For a Weierstrass curve `W'` over an integral domain `R`, the homogeneous Weierstrass polynomial

`Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`

is a prime element of `R[X, Y, Z]`, so the homogeneous coordinate ring
`WeierstrassCurve.Projective.CoordinateRing W'` is an integral domain. No ellipticity hypothesis
is needed.

## Main results

* `WeierstrassCurve.Projective.prime_polynomial`: over an integral domain, the Weierstrass
  polynomial in projective coordinates is prime.
* `WeierstrassCurve.Projective.instIsDomainCoordinateRing`: over an integral domain, the
  homogeneous coordinate ring of a Weierstrass curve is an integral domain.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/ForMathlib/WeierstrassProjectivePrime.lean`, declarations
`WeierstrassCurve.projective_polynomial_prime` and `ModularCurves.instIsDomainProjCoordRing`,
which treat Weierstrass curves over a field; here the base is any integral domain, and the
coordinate ring is `WeierstrassCurve.Projective.CoordinateRing`.
-/

public section

open MvPolynomial
open scoped Polynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W' : Projective R)

-- The negative of the Weierstrass polynomial in projective coordinates, as a monic cubic in `X`
-- over `R[Y, Z]`, where `Y` and `Z` are the variables `X 0` and `X 1` of `R[Y, Z]`.
private noncomputable def cubic : (MvPolynomial (Fin 2) R)[X] :=
  Cubic.toPoly ⟨1, X 1 * C W'.a₂, X 1 * (C W'.a₄ * X 1 - C W'.a₁ * X 0),
    X 1 * (C W'.a₆ * X 1 ^ 2 - C W'.a₃ * X 0 * X 1 - X 0 ^ 2)⟩

private theorem finSuccEquiv_polynomial : finSuccEquiv R 2 W'.polynomial = -W'.cubic := by
  have hX1 : finSuccEquiv R 2 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
  have hX2 : finSuccEquiv R 2 (X 2) = Polynomial.C (X 1) := finSuccEquiv_X_succ (j := 1)
  have hC (a : R) : finSuccEquiv R 2 (C a) = Polynomial.C (C a) := (finSuccEquiv R 2).commutes a
  simp only [polynomial, cubic, Cubic.toPoly, map_add, map_sub, map_mul, map_pow, map_one,
    one_mul, finSuccEquiv_X_zero, hX1, hX2, hC]
  ring

private theorem monic_cubic : W'.cubic.Monic := Cubic.monic_of_a_eq_one'

private theorem map_cubic {S : Type*} [CommRing S] (f : R →+* S) :
    (W'.map f).cubic = W'.cubic.map (MvPolynomial.map f) := by
  simp [cubic, ← Cubic.map_toPoly, Cubic.map]

private theorem irreducible_cubic [IsDomain R] : Irreducible W'.cubic := by
  -- the cubic is Eisenstein at the prime `Z`
  have hP : (Ideal.span {(X 1 : MvPolynomial (Fin 2) R)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime X_prime
  have hdeg : W'.cubic.natDegree = 3 := Cubic.natDegree_of_a_ne_zero' one_ne_zero
  refine (W'.monic_cubic.isEisensteinAt_of_mem_of_notMem hP.ne_top (fun {n} hn ↦ ?_) ?_).irreducible
    hP W'.monic_cubic.isPrimitive (by lia)
  · rw [hdeg] at hn
    interval_cases n <;> simp [cubic, Ideal.mem_span_singleton]
  · -- the constant coefficient `Z (a₆Z² - a₃YZ - Y²)` is not divisible by `Z²`, as `Z ∤ Y²`
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two, cubic, Cubic.coeff_eq_d,
      isRegular_X.left.dvd_cancel_left,
      dvd_sub_right (Dvd.intro (C W'.a₆ * X 1 - C W'.a₃ * X 0) (by ring))]
    simp [X_pow_eq_monomial]

private theorem prime_cubic [IsDomain R] : Prime W'.cubic := by
  -- the cubic stays irreducible, hence prime, over the factorial ring `K[Y, Z]`, where `K` is the
  -- fraction field of `R`
  have hK := (irreducible_cubic (W'.map (algebraMap R (FractionRing R)))).prime
  rw [map_cubic] at hK
  -- divisibility by a monic polynomial descends along `R[Y, Z] ⊆ K[Y, Z]`
  refine ⟨W'.monic_cubic.ne_zero, fun hu ↦ hK.not_isUnit (hu.map (Polynomial.mapRingHom _)),
    fun a b h ↦ ?_⟩
  simp only [← Polynomial.map_dvd_map _ (MvPolynomial.map_injective (algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R))) W'.monic_cubic, Polynomial.map_mul] at h ⊢
  exact hK.dvd_or_dvd h

/-- Over an integral domain, the Weierstrass polynomial
`Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)` in projective coordinates is prime in
`R[X, Y, Z]`. Its irreducibility follows by `Prime.irreducible`; compare
`WeierstrassCurve.Affine.irreducible_polynomial` for the affine Weierstrass polynomial. -/
theorem prime_polynomial [IsDomain R] : Prime W'.polynomial := by
  rw [← MulEquiv.prime_iff (finSuccEquiv R 2), finSuccEquiv_polynomial]
  exact W'.prime_cubic.neg

/-- Over an integral domain, the homogeneous coordinate ring of a Weierstrass curve is an integral
domain; compare the corresponding instance on the affine coordinate ring
`WeierstrassCurve.Affine.CoordinateRing`. -/
instance [IsDomain R] : IsDomain W'.CoordinateRing :=
  have := Ideal.isPrime_span_singleton_of_prime W'.prime_polynomial
  inferInstance

end WeierstrassCurve.Projective
