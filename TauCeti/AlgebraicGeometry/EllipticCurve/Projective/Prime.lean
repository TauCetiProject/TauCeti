/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
public import TauCeti.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.GroupWithZero.Action.Regular
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

Over any commutative ring `R`, the Weierstrass polynomial is, up to sign, a monic cubic in `X`
over `R[Y, Z]`. Hence the class of `Z` is a nonzerodivisor of the homogeneous coordinate ring, and
the classes of `Z` and `Y` form a regular sequence in it.

## Main results

* `WeierstrassCurve.Projective.prime_polynomial`: over an integral domain, the Weierstrass
  polynomial in projective coordinates is prime.
* `WeierstrassCurve.Projective.instIsDomainCoordinateRing`: over an integral domain, the
  homogeneous coordinate ring of a Weierstrass curve is an integral domain.
* `WeierstrassCurve.Projective.coord_two_mem_nonZeroDivisors`: over any commutative ring, the
  class of `Z` is a nonzerodivisor of the homogeneous coordinate ring.
* `WeierstrassCurve.Projective.isWeaklyRegular_coord_two_coord_one`: over any commutative ring,
  the classes of `Z` and `Y` form a regular sequence in the homogeneous coordinate ring.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/ForMathlib/WeierstrassProjectivePrime.lean`, declarations
`WeierstrassCurve.projective_polynomial_prime` and `ModularCurves.instIsDomainProjCoordRing`,
which treat Weierstrass curves over a field; here the base is any integral domain, and the
coordinate ring is `WeierstrassCurve.Projective.CoordinateRing`.

`coord_two_mem_nonZeroDivisors` corresponds, at the same commit, to
`chart_isLocalizationElem_nonZeroDivisor` in the file
`projects/ModularCurves/ModularCurves/EllipticCurve/PoleFiltration.lean`, which rests on
`zChart_z_nonZeroDivisor` and `infChart_t_nonZeroDivisor` of that file. The source shows, chart by
chart, that the class of `Z` is a nonzerodivisor of the dehomogenised coordinate rings of the
charts `D₊(X)` and `D₊(Y)`: on `D₊(X)` because the dehomogenised cubic has constant coefficient
`-1` as a polynomial in `Z`, on `D₊(Y)` because it is, up to sign, monic in `X`. Here the
statement is made once, for the homogeneous coordinate ring, by the second of these arguments.
The injectivity of the restrictions `A_{(Xⱼ)} → A_{(XⱼZ)}`, which is what the source draws from
the statements on the charts, follows from it by `HomogeneousLocalization.awayMap_injective`.
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

-- As a polynomial in `X` over `R[Y, Z]`, the Weierstrass polynomial is the negative of the monic
-- `cubic`, so a class in the homogeneous coordinate ring vanishes exactly when the remainder
-- modulo `cubic` does.
private theorem mk_eq_zero_iff_modByMonic_eq_zero (q : MvPolynomial (Fin 3) R) :
    Ideal.Quotient.mk (Ideal.span {W'.polynomial}) q = 0 ↔ finSuccEquiv R 2 q %ₘ W'.cubic = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_dvd, ← map_dvd_iff (finSuccEquiv R 2), finSuccEquiv_polynomial,
    Polynomial.modByMonic_eq_zero_iff_dvd W'.monic_cubic]
  exact neg_dvd

/-- The class of the homogeneous coordinate `Z` is a nonzerodivisor of the homogeneous coordinate
ring `R[X, Y, Z] ⧸ (W'(X, Y, Z))` of a Weierstrass curve. -/
theorem coord_two_mem_nonZeroDivisors : W'.coord 2 ∈ nonZeroDivisors W'.CoordinateRing := by
  refine mem_nonZeroDivisors_iff_left.mpr fun x hx ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- `Z` is a constant of `R[Y, Z][X]`, so the remainder of `Z * p` is `Z` times that of `p`
  rw [← map_mul, mk_eq_zero_iff_modByMonic_eq_zero, map_mul, ← Fin.succ_one_eq_two,
    finSuccEquiv_X_succ, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic] at hx
  -- and `Z` is a nonzerodivisor of `R[Y, Z]`, so it acts injectively on polynomials over it
  rw [mk_eq_zero_iff_modByMonic_eq_zero]
  exact isRegular_X.left.isSMulRegular.polynomial.right_eq_zero_of_smul hx

-- In `R[Y, Z]`, the variable `Y` is a nonzerodivisor modulo `Z`: as a polynomial in `Y` over
-- `R[Z]`, the coefficients of `Y * u` are those of `u`, shifted by one.
private theorem X_one_dvd_of_X_one_dvd_X_zero_mul {u : MvPolynomial (Fin 2) R}
    (h : X 1 ∣ X 0 * u) : X 1 ∣ u := by
  rw [← map_dvd_iff (finSuccEquiv R 1), map_mul, finSuccEquiv_X_zero, ← Fin.succ_zero_eq_one,
    finSuccEquiv_X_succ, Polynomial.C_dvd_iff_dvd_coeff] at h
  rw [← map_dvd_iff (finSuccEquiv R 1), ← Fin.succ_zero_eq_one, finSuccEquiv_X_succ,
    Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  simpa using h (i + 1)

/-- The classes of the homogeneous coordinates `Z` and `Y` form a regular sequence in the
homogeneous coordinate ring `A = R[X, Y, Z] ⧸ (W'(X, Y, Z))` of a Weierstrass curve: `Z` is a
nonzerodivisor of `A`, and `Y` is a nonzerodivisor of `A ⧸ (Z) = R[X, Y] ⧸ (X³)`. -/
theorem isWeaklyRegular_coord_two_coord_one :
    RingTheory.Sequence.IsWeaklyRegular W'.CoordinateRing [W'.coord 2, W'.coord 1] := by
  refine RingTheory.Sequence.isWeaklyRegular_pair_iff.mpr
    ⟨W'.coord_two_mem_nonZeroDivisors, fun a ⟨b, hb⟩ ↦ ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- over `R[Y, Z]`, the remainders of `p` and `q` modulo `cubic` satisfy `Y • r = Z • r'`
  have hpq := (W'.mk_eq_zero_iff_modByMonic_eq_zero (X 1 * p - X 2 * q)).mp
    (by rw [map_sub, map_mul, map_mul, sub_eq_zero]; exact hb)
  rw [map_sub, map_mul, map_mul, ← Fin.succ_zero_eq_one, ← Fin.succ_one_eq_two,
    finSuccEquiv_X_succ, finSuccEquiv_X_succ, Polynomial.sub_modByMonic,
    ← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic,
    Polynomial.smul_modByMonic, sub_eq_zero] at hpq
  -- so `Z` divides the remainder `r` of `p`, coefficientwise
  obtain ⟨t, ht⟩ : Polynomial.C (X 1) ∣ finSuccEquiv R 2 p %ₘ W'.cubic := by
    refine Polynomial.C_dvd_iff_dvd_coeff _ _ |>.mpr fun i ↦ X_one_dvd_of_X_one_dvd_X_zero_mul ?_
    have := congr(Polynomial.coeff $hpq i)
    simp only [Polynomial.coeff_smul, smul_eq_mul] at this
    exact ⟨_, this⟩
  -- and `p` is congruent to `r` modulo the Weierstrass polynomial
  refine ⟨Ideal.Quotient.mk _ ((finSuccEquiv R 2).symm t), ?_⟩
  rw [← map_mul, ← sub_eq_zero, ← map_sub, mk_eq_zero_iff_modByMonic_eq_zero, map_sub, map_mul,
    AlgEquiv.apply_symm_apply, ← Fin.succ_one_eq_two, finSuccEquiv_X_succ, ← ht,
    Polynomial.modByMonic_eq_zero_iff_dvd W'.monic_cubic]
  exact dvd_sub_comm.mp (Polynomial.dvd_modByMonic_sub _ _)

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
