/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Algebraic.Denominator
public import Mathlib.RingTheory.Polynomial.GaussLemma

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.Algebra.Polynomial.Normalize

/-!
# The primitive minimal polynomial over `ℤ`

For an element `x` of a field `F` of characteristic zero, the *primitive minimal polynomial*
`F_x = primitiveMinpoly x ∈ ℤ[X]` is obtained from `minpoly ℚ x` by clearing denominators and
dividing by the content, with the sign chosen so that the leading coefficient `a₀` is positive.
For algebraic `x` it is the unique primitive irreducible integer polynomial with positive leading
coefficient vanishing at `x`, and its image in `ℚ[X]` is `a₀ • minpoly ℚ x`. When `x` is
transcendental over `ℚ` the junk value is `1`.

This is the polynomial from which the classical size invariants of an algebraic number are read
off: its naive height is the largest absolute value of a coefficient of `F_x`, and its Mahler
measure is the Mahler measure of `F_x`. Unlike `minpoly ℤ x`, which vanishes at non-integral
algebraic numbers, `F_x` is meaningful for every algebraic `x`, and its leading coefficient
clears the denominator of `x`.

## Main definitions

* `TauCeti.primitiveMinpoly x`: the primitive minimal polynomial `F_x ∈ ℤ[X]` of `x`.

## Main results

* `TauCeti.map_primitiveMinpoly`: the image of `F_x` in `ℚ[X]` is `a₀ • minpoly ℚ x`.
* `TauCeti.isPrimitive_primitiveMinpoly`, `TauCeti.leadingCoeff_primitiveMinpoly_pos`,
  `TauCeti.irreducible_primitiveMinpoly`, `TauCeti.aeval_primitiveMinpoly`: `F_x` is primitive,
  has positive leading coefficient, and for algebraic `x` is irreducible and vanishes at `x`.
* `TauCeti.primitiveMinpoly_dvd_iff`: for algebraic `x`, `F_x ∣ P` in `ℤ[X]` iff `P(x) = 0`.
* `TauCeti.primitiveMinpoly_eq_of_irreducible`: the uniqueness characterisation of `F_x`.
* `TauCeti.primitiveMinpoly_eq_minpoly_int`: `F_x = minpoly ℤ x` for `x` integral over `ℤ`.
* `TauCeti.primitiveMinpoly_ratCast`: `F_q = (den q) X - num q` for `q ∈ ℚ`.
* `TauCeti.primitiveMinpoly_map`, `TauCeti.primitiveMinpoly_eq_of_minpoly_eq`: `F_x` depends only
  on `minpoly ℚ x`, so it is preserved by field embeddings and shared by conjugates.
* `TauCeti.isIntegral_leadingCoeff_primitiveMinpoly_smul`,
  `TauCeti.natDenominator_dvd_leadingCoeff_primitiveMinpoly`: `a₀ x` is an algebraic integer, so
  the denominator of `x` divides `a₀`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 3, §3.1 and Lemma 3.7;
  ch. 6, §6.1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F] {F' : Type*} [Field F'] [CharZero F']

/-- The *primitive minimal polynomial* `F_x ∈ ℤ[X]` of `x` over `ℚ`: the primitive integer
multiple of `minpoly ℚ x` with positive leading coefficient. It is obtained by clearing the
denominators of `minpoly ℚ x`, taking the primitive part and normalizing the sign.

For `x` transcendental over `ℚ`, `minpoly ℚ x = 0` and the value is `1`
(`primitiveMinpoly_of_not_isAlgebraic`). -/
noncomputable def primitiveMinpoly (x : F) : ℤ[X] :=
  normalize (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)).primPart

/-- `F_x` depends only on `minpoly ℚ x`: elements with the same minimal polynomial over `ℚ`, for
instance conjugates, possibly lying in different fields, share their primitive minimal
polynomial. -/
theorem primitiveMinpoly_eq_of_minpoly_eq {x : F} {y : F'} (h : minpoly ℚ x = minpoly ℚ y) :
    primitiveMinpoly x = primitiveMinpoly y := by
  rw [primitiveMinpoly, primitiveMinpoly, h]

/-- Field embeddings preserve the primitive minimal polynomial. -/
@[simp]
theorem primitiveMinpoly_map (f : F →+* F') (x : F) :
    primitiveMinpoly (f x) = primitiveMinpoly x :=
  primitiveMinpoly_eq_of_minpoly_eq (minpoly.algHom_eq f.toRatAlgHom f.injective x)

/-- The junk value: `F_x = 1` for `x` transcendental over `ℚ`. -/
@[simp]
theorem primitiveMinpoly_of_not_isAlgebraic {x : F} (hx : ¬IsAlgebraic ℚ x) :
    primitiveMinpoly x = 1 := by
  rw [primitiveMinpoly, minpoly.eq_zero (isAlgebraic_iff_isIntegral.not.mp hx),
    (IsFractionRing.integerNormalization_eq_zero_iff (A := ℤ)).mpr rfl, primPart_zero,
    normalize_one]

/-- The primitive minimal polynomial is primitive. -/
theorem isPrimitive_primitiveMinpoly (x : F) : (primitiveMinpoly x).IsPrimitive :=
  isPrimitive_of_dvd (isPrimitive_primPart _) (normalize_dvd_iff.mpr dvd_rfl)

/-- The primitive minimal polynomial is nonzero, also for transcendental `x`. -/
@[simp]
theorem primitiveMinpoly_ne_zero (x : F) : primitiveMinpoly x ≠ 0 :=
  (isPrimitive_primitiveMinpoly x).ne_zero

/-- The leading coefficient `a₀` of the primitive minimal polynomial is positive. -/
theorem leadingCoeff_primitiveMinpoly_pos (x : F) : 0 < (primitiveMinpoly x).leadingCoeff := by
  rw [primitiveMinpoly, leadingCoeff_normalize, ← Int.abs_eq_normalize, abs_pos,
    leadingCoeff_ne_zero]
  exact primPart_ne_zero _

/-- For algebraic `x`, the image of `F_x` in `ℚ[X]` is `a₀ • minpoly ℚ x`, where `a₀` is the
leading coefficient of `F_x`. -/
theorem map_primitiveMinpoly {x : F} (hx : IsAlgebraic ℚ x) :
    (primitiveMinpoly x).map (Int.castRingHom ℚ) =
      C ((primitiveMinpoly x).leadingCoeff : ℚ) * minpoly ℚ x := by
  set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hm : minpoly ℚ x ≠ 0 := minpoly.ne_zero (isAlgebraic_iff_isIntegral.mp hx)
  have hq : q ≠ 0 := fun h ↦ hm (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  obtain ⟨b, -, hbq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
    (minpoly ℚ x)
  rw [algebraMap_int_eq] at hbq
  -- `minpoly ℚ x` divides the image of `q = content q * primPart q`, hence that of `F_x`.
  have hdvd : minpoly ℚ x ∣ (primitiveMinpoly x).map (Int.castRingHom ℚ) := by
    have h1 : q ∣ C q.content * primitiveMinpoly x := by
      conv_lhs => rw [q.eq_C_content_mul_primPart]
      exact mul_dvd_mul_left _ (dvd_normalize_iff.mpr dvd_rfl)
    have h2 := Polynomial.map_dvd (Int.castRingHom ℚ) h1
    rw [hbq, Polynomial.map_mul, map_C] at h2
    have hc : IsUnit (C (Int.castRingHom ℚ q.content)) :=
      isUnit_C.mpr (by simpa using content_eq_zero_iff.not.mpr hq)
    exact hc.dvd_mul_left.mp ((dvd_smul_of_dvd _ dvd_rfl).trans h2)
  have hdeg : ((primitiveMinpoly x).map (Int.castRingHom ℚ)).natDegree ≤
      (minpoly ℚ x).natDegree := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), primitiveMinpoly,
      natDegree_normalize', natDegree_primPart,
      ← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)) q, hbq]
    exact natDegree_smul_le _ _
  rw [eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (isAlgebraic_iff_isIntegral.mp hx)) hdvd hdeg,
    leadingCoeff_map_of_injective (RingHom.injective_int _), eq_intCast]

/-- For algebraic `x`, the primitive minimal polynomial vanishes at `x`. -/
@[simp]
theorem aeval_primitiveMinpoly {x : F} (hx : IsAlgebraic ℚ x) :
    aeval x (primitiveMinpoly x) = 0 := by
  rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, map_primitiveMinpoly hx, aeval_mul,
    minpoly.aeval, mul_zero]

/-- The primitive minimal polynomial has the degree of `x` over `ℚ`. For transcendental `x` both
sides are `0`. -/
@[simp]
theorem natDegree_primitiveMinpoly (x : F) :
    (primitiveMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
  by_cases hx : IsAlgebraic ℚ x
  · rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)),
      map_primitiveMinpoly hx, natDegree_C_mul (by exact_mod_cast
        (leadingCoeff_primitiveMinpoly_pos x).ne')]
  · rw [primitiveMinpoly_of_not_isAlgebraic hx,
      minpoly.eq_zero (isAlgebraic_iff_isIntegral.not.mp hx), natDegree_one, natDegree_zero]

/-- For algebraic `x`, the image of `F_x` in `ℚ[X]` is associated to `minpoly ℚ x`. -/
private lemma associated_map_primitiveMinpoly {x : F} (hx : IsAlgebraic ℚ x) :
    Associated ((primitiveMinpoly x).map (Int.castRingHom ℚ)) (minpoly ℚ x) := by
  rw [map_primitiveMinpoly hx]
  refine associated_unit_mul_left _ _ (isUnit_C.mpr (Ne.isUnit ?_))
  exact_mod_cast (leadingCoeff_primitiveMinpoly_pos x).ne'

/-- For algebraic `x`, the primitive minimal polynomial is irreducible in `ℤ[X]`. -/
theorem irreducible_primitiveMinpoly {x : F} (hx : IsAlgebraic ℚ x) :
    Irreducible (primitiveMinpoly x) :=
  (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (isPrimitive_primitiveMinpoly x)).mpr
    ((associated_map_primitiveMinpoly hx).symm.irreducible
      (minpoly.irreducible (isAlgebraic_iff_isIntegral.mp hx)))

/-- For algebraic `x`, the integer polynomials vanishing at `x` are exactly the multiples of
`F_x` in `ℤ[X]`. -/
theorem primitiveMinpoly_dvd_iff {x : F} (hx : IsAlgebraic ℚ x) {P : ℤ[X]} :
    primitiveMinpoly x ∣ P ↔ aeval x P = 0 := by
  refine ⟨fun ⟨Q, hQ⟩ ↦ by rw [hQ, aeval_mul, aeval_primitiveMinpoly hx, zero_mul], fun h ↦ ?_⟩
  rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (isPrimitive_primitiveMinpoly x),
    (associated_map_primitiveMinpoly hx).dvd_iff_dvd_left]
  exact minpoly.dvd ℚ x (by rw [← algebraMap_int_eq, aeval_map_algebraMap, h])

/-- The uniqueness characterisation: an irreducible `P ∈ ℤ[X]` with positive leading coefficient
vanishing at `x` is the primitive minimal polynomial of `x`. Such a `P` is automatically
nonconstant, hence primitive. -/
theorem primitiveMinpoly_eq_of_irreducible {x : F} {P : ℤ[X]} (hirr : Irreducible P)
    (hlc : 0 < P.leadingCoeff) (hPx : aeval x P = 0) :
    primitiveMinpoly x = P := by
  have hx : IsAlgebraic ℚ x := ⟨P.map (Int.castRingHom ℚ),
    (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hirr.ne_zero,
    by rw [← algebraMap_int_eq, aeval_map_algebraMap, hPx]⟩
  have hnorm (p : ℤ[X]) (hp : 0 < p.leadingCoeff) : normalize p = p := by
    simp [normalize_apply, Int.normUnit_eq, hp.le]
  exact Associated.eq_of_normalized
    ((irreducible_primitiveMinpoly hx).associated_of_dvd hirr
      ((primitiveMinpoly_dvd_iff hx).mpr hPx))
    (hnorm _ (leadingCoeff_primitiveMinpoly_pos x)) (hnorm _ hlc)

/-- For `x` integral over `ℤ`, the primitive minimal polynomial is the minimal polynomial over
`ℤ`. -/
theorem primitiveMinpoly_eq_minpoly_int {x : F} (hx : IsIntegral ℤ x) :
    primitiveMinpoly x = minpoly ℤ x := by
  have hmon := minpoly.monic hx
  exact primitiveMinpoly_eq_of_irreducible (minpoly.irreducible hx)
    (by rw [hmon.leadingCoeff]; exact one_pos) (minpoly.aeval ℤ x)

/-- The primitive minimal polynomial of a rational number `q` is `(den q) X - num q`. -/
@[simp]
theorem primitiveMinpoly_ratCast (q : ℚ) :
    primitiveMinpoly (q : F) = C (q.den : ℤ) * X - C q.num := by
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [sub_eq_add_neg, ← C_neg]
  have hirr := irreducible_C_mul_X_add_C hden (Rat.isCoprime_num_den q).neg_left.isRelPrime.symm
  refine primitiveMinpoly_eq_of_irreducible hirr
    (by rw [leadingCoeff_linear hden]; exact_mod_cast q.den_pos) ?_
  rw [aeval_add, aeval_mul, aeval_C, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast, eq_intCast]
  exact_mod_cast add_neg_eq_zero.mpr (Rat.den_mul_eq_num q)

/-- For algebraic `x`, the element `a₀ x` is integral over `ℤ`, where `a₀` is the leading
coefficient of `F_x` (Evertse, Lemma 3.7). -/
theorem isIntegral_leadingCoeff_primitiveMinpoly_smul {x : F} (hx : IsAlgebraic ℚ x) :
    IsIntegral ℤ ((primitiveMinpoly x).leadingCoeff • x) :=
  isIntegral_leadingCoeff_smul _ _ (aeval_primitiveMinpoly hx)

/-- For algebraic `x`, the denominator of `x` divides the leading coefficient of `F_x`. -/
theorem natDenominator_dvd_leadingCoeff_primitiveMinpoly {x : F} (hx : IsAlgebraic ℚ x) :
    (Algebra.natDenominator x : ℤ) ∣ (primitiveMinpoly x).leadingCoeff := by
  rw [Algebra.natDenominator_def, Int.natCast_natAbs, abs_dvd, Algebra.denominator_dvd_iff]
  exact isIntegral_leadingCoeff_primitiveMinpoly_smul hx

/-! ### Examples -/

/- `F_{2/3} = 3X - 2`, in every field of characteristic zero. -/
example : primitiveMinpoly (((2 : ℚ) / 3 : ℚ) : F) = C 3 * X - C 2 := by
  rw [primitiveMinpoly_ratCast, show ((2 : ℚ) / 3).den = 3 by norm_num,
    show ((2 : ℚ) / 3).num = 2 by norm_num, Nat.cast_ofNat]

/- `F_x` differs from `minpoly ℤ x` at the non-integral `x = 1/2`: there `minpoly ℤ x` is the junk
value `0`, while `F_{1/2} = 2X - 1` has leading coefficient `2`, not `1`. -/
example : primitiveMinpoly (((1 : ℚ) / 2 : ℚ) : F) ≠ minpoly ℤ (((1 : ℚ) / 2 : ℚ) : F) := by
  intro h
  have hint : IsIntegral ℤ (((1 : ℚ) / 2 : ℚ) : F) :=
    by_contra fun hn ↦ primitiveMinpoly_ne_zero _ (h.trans (minpoly.eq_zero hn))
  have := congrArg leadingCoeff h
  rw [(minpoly.monic hint).leadingCoeff, primitiveMinpoly_ratCast,
    show ((1 : ℚ) / 2).den = 2 by norm_num, sub_eq_add_neg, ← C_neg,
    leadingCoeff_linear (by norm_num)] at this
  norm_num at this

end TauCeti
