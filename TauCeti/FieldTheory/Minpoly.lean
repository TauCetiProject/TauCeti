/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Minimal polynomials of quadratic elements, units, and scalar-tower roots

This file collects reusable facts about minimal polynomials of quadratic elements, units, and
elements annihilated by polynomials over a subring.

## Main results

* `TauCeti.Algebra.minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two`: the minimal polynomial
  of a quadratic element of an `F`-algebra whose square is in the base field `F`.
* `IsIntegral.exists_quadratic_relation`: a degree-two integral element of a ring algebra
  satisfies a monic quadratic relation over its commutative base ring.
* `minpoly.coeff_zero_ne_zero_of_isUnit`: the minimal polynomial of an integral unit has nonzero
  constant coefficient.
* `TauCeti.minpoly_eq_map_of_aeval_eq_zero`,
  `TauCeti.minpoly_eq_map_intCastRingHom_of_aeval_eq_zero`: in a scalar tower `R → F → E` (and in
  particular for `P : ℤ[X]` via `Int.castRingHom F`), a monic polynomial `P` annihilating `α : E`
  whose image in `F[X]` is irreducible maps to `minpoly F α`.
-/

public section

open Polynomial

namespace TauCeti.Algebra

/-- The minimal polynomial of a quadratic element whose square is `r` is `X² - r`.

Only the base `F` need be a field; `L` is an arbitrary `F`-algebra ring, so this also covers
quadratic elements of noncommutative algebras, such as `i` in a quaternion algebra. -/
theorem minpoly_eq_X_sq_sub_C_of_sq_eq_of_natDegree_eq_two {F L : Type*} [Field F] [Ring L]
    [Algebra F L] {x : L} {r : F}
    (hx2 : x ^ 2 = algebraMap F L r) (hdegree : (minpoly F x).natDegree = 2) :
    minpoly F x = X ^ 2 - C r := by
  have hxint : IsIntegral F x := minpoly.ne_zero_iff.mp fun hzero ↦ by
    simp [hzero] at hdegree
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hxint)
    (Polynomial.monic_X_pow_sub_C r (by norm_num)) (minpoly.dvd F x ?_) ?_
  · simp [hx2]
  · rw [hdegree, Polynomial.natDegree_X_pow_sub_C]

end TauCeti.Algebra

/-- An integral element of degree two satisfies a monic quadratic relation over the base ring. -/
theorem IsIntegral.exists_quadratic_relation {K L : Type*} [CommRing K] [Ring L]
    [Algebra K L] {y : L} (hyint : IsIntegral K y)
    (hdeg : (minpoly K y).natDegree = 2) :
    ∃ b c : K, y ^ 2 + algebraMap K L b * y + algebraMap K L c = 0 := by
  cases subsingleton_or_nontrivial K with
  | inl h => simp [Polynomial.natDegree_of_subsingleton] at hdeg
  | inr h =>
    obtain ⟨b, c, hpoly⟩ :=
      Polynomial.isMonicOfDegree_two_iff.mp ⟨hdeg, minpoly.monic hyint⟩
    refine ⟨b, c, ?_⟩
    have h0 := minpoly.aeval K y
    rw [hpoly] at h0
    simpa using h0

/-- The minimal polynomial of an integral unit has nonzero constant coefficient. Unlike
`minpoly.coeff_zero_ne_zero`, the algebra need not be a domain. -/
theorem minpoly.coeff_zero_ne_zero_of_isUnit {A B : Type*} [Field A] [Ring B] [Algebra A B]
    {x : B} (hx : IsIntegral A x) (hu : IsUnit x) : (minpoly A x).coeff 0 ≠ 0 := by
  intro h0
  have hm : minpoly A x ≠ 0 := minpoly.ne_zero hx
  have hdiv : divX (minpoly A x) ≠ 0 := fun h ↦ hm (by rwa [divX_eq_zero_iff, h0, C_0] at h)
  have hX : Polynomial.aeval x (divX (minpoly A x)) = 0 := by
    have hmx := minpoly.aeval A x
    have h := divX_mul_X_add (minpoly A x)
    rw [h0, C_0, add_zero] at h
    rw [← h, map_mul, aeval_X] at hmx
    exact hu.mul_left_eq_zero.mp hmx
  exact absurd (minpoly.degree_le_of_ne_zero A x hdiv hX) (not_le.mpr (degree_divX_lt hm))

namespace TauCeti

/-- In a scalar tower `R → F → E` over a field `F` and a nontrivial `F`-algebra `E`, if `α : E` is
annihilated by a monic polynomial `P : R[X]` whose image in `F[X]` is irreducible, then
`minpoly F α` equals `P.map (algebraMap R F)`. -/
theorem minpoly_eq_map_of_aeval_eq_zero {R F E : Type*} [CommSemiring R] [Field F] [Ring E]
    [Nontrivial E] [Algebra R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E] {α : E}
    {P : R[X]} (hP : P.Monic) (hirr : Irreducible (P.map (algebraMap R F)))
    (hroot : aeval α P = 0) :
    minpoly F α = P.map (algebraMap R F) :=
  (minpoly.eq_of_irreducible_of_monic hirr (by rw [aeval_map_algebraMap, hroot])
    (hP.map (algebraMap R F))).symm

/-- Over a field `F` and a nontrivial `F`-algebra `E`, if `α : E` is annihilated by a monic
integral polynomial `P : ℤ[X]` whose image under `Int.castRingHom F` is irreducible, then
`minpoly F α` equals `P.map (Int.castRingHom F)`. -/
theorem minpoly_eq_map_intCastRingHom_of_aeval_eq_zero {F E : Type*} [Field F] [Ring E]
    [Nontrivial E] [Algebra F E] {α : E} {P : ℤ[X]} (hP : P.Monic)
    (hirr : Irreducible (P.map (Int.castRingHom F))) (hroot : aeval α P = 0) :
    minpoly F α = P.map (Int.castRingHom F) := by
  have hhom : Int.castRingHom F = algebraMap ℤ F := RingHom.ext_int _ _
  rw [hhom] at hirr ⊢
  exact minpoly_eq_map_of_aeval_eq_zero hP hirr hroot

end TauCeti
