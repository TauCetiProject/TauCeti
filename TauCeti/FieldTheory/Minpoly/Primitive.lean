/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Algebraic.Denominator
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import TauCeti.Algebra.Polynomial.Reverse

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.Algebra.Polynomial.Normalize

/-!
# The primitive minimal polynomial over `ℤ`

For an element `x` of a division ring `F` of characteristic zero (typically a field), the
*primitive minimal polynomial* `F_x = primitiveMinpoly x ∈ ℤ[X]` is obtained from `minpoly ℚ x`
by clearing denominators and dividing by the content, with the sign chosen so that the leading
coefficient `a₀` is positive.
For algebraic `x` it is the unique primitive irreducible integer polynomial with positive leading
coefficient vanishing at `x`, and its image in `ℚ[X]` is `a₀ • minpoly ℚ x`. When `x` is
transcendental over `ℚ` the junk value is `1`.

This is the polynomial from which the classical size invariants of an algebraic number are read
off: its naive height is the largest absolute value of a coefficient of `F_x`, and its Mahler
measure is the Mahler measure of `F_x`. Unlike `minpoly ℤ x`, which vanishes at non-integral
algebraic numbers, `F_x` is meaningful for every algebraic `x`, and its leading coefficient
clears the denominator of `x` when `F` is a field.

## Main definitions

* `TauCeti.primitiveMinpoly x`: the primitive minimal polynomial `F_x ∈ ℤ[X]` of `x`.

## Main results

* `TauCeti.map_primitiveMinpoly`: the image of `F_x` in `ℚ[X]` is `a₀ • minpoly ℚ x`.
* `TauCeti.isPrimitive_primitiveMinpoly`, `TauCeti.leadingCoeff_primitiveMinpoly_pos`,
  `TauCeti.irreducible_primitiveMinpoly`, `TauCeti.aeval_primitiveMinpoly`: `F_x` is primitive,
  has positive leading coefficient, and for algebraic `x` is irreducible and vanishes at `x`.
* `TauCeti.rootSet_primitiveMinpoly`: for algebraic `x`, `F_x` and `minpoly ℚ x` have the same
  roots in every commutative domain that is a `ℚ`-algebra.
* `TauCeti.primitiveMinpoly_dvd_iff`: for algebraic `x`, `F_x ∣ P` in `ℤ[X]` iff `P(x) = 0`.
* `TauCeti.primitiveMinpoly_eq_of_irreducible`: the uniqueness characterisation of `F_x`.
* `TauCeti.primitiveMinpoly_eq_minpoly_int`: `F_x = minpoly ℤ x` for `x` integral over `ℤ`.
* `TauCeti.primitiveMinpoly_ratCast`: `F_q = (den q) X - num q` for `q ∈ ℚ`.
* `TauCeti.primitiveMinpoly_map`, `TauCeti.primitiveMinpoly_eq_of_minpoly_eq`: `F_x` depends only
  on `minpoly ℚ x`, so it is preserved by ring homomorphisms between division rings of
  characteristic zero (such as field embeddings) and shared by conjugates.
* `TauCeti.coeff_zero_primitiveMinpoly_ne_zero`: for nonzero algebraic `x`, the constant
  coefficient of `F_x` is nonzero.
* `TauCeti.isIntegral_leadingCoeff_primitiveMinpoly_smul`,
  `TauCeti.natDenominator_dvd_leadingCoeff_primitiveMinpoly`,
  `TauCeti.leadingCoeff_primitiveMinpoly_le_natDenominator_pow`: `a₀ x` is an algebraic integer,
  so in fields the denominator of `x` divides `a₀`, and conversely `a₀` is at most the `d`-th
  power of the denominator.
* `TauCeti.natDegree_minpoly_int_natDenominator_smul`: in fields, `D x` for the denominator `D`
  of `x` has the same degree over `ℤ` as `x` has over `ℚ`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 3, §3.1 and Lemma 3.7;
  ch. 6, §6.1.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

variable {F : Type*} [DivisionRing F] [CharZero F] {F' : Type*} [DivisionRing F'] [CharZero F']

/-- The *primitive minimal polynomial* `F_x ∈ ℤ[X]` of `x` over `ℚ`: the primitive integer
multiple of `minpoly ℚ x` with positive leading coefficient. It is obtained by clearing the
denominators of `minpoly ℚ x`, taking the primitive part and normalizing the sign.

For `x` transcendental over `ℚ`, `minpoly ℚ x = 0` and the value is `1`
(`primitiveMinpoly_of_not_isAlgebraic`). -/
noncomputable def primitiveMinpoly (x : F) : ℤ[X] :=
  normalize (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)).primPart

/-- `F_x` depends only on `minpoly ℚ x`: elements with the same minimal polynomial over `ℚ`, for
instance conjugates, possibly lying in different division rings, share their primitive minimal
polynomial. -/
theorem primitiveMinpoly_eq_of_minpoly_eq {x : F} {y : F'} (h : minpoly ℚ x = minpoly ℚ y) :
    primitiveMinpoly x = primitiveMinpoly y := by
  rw [primitiveMinpoly, primitiveMinpoly, h]

/-- Ring homomorphisms between division rings (for instance field embeddings) preserve the
primitive minimal polynomial. -/
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

/-- For nonzero algebraic `x`, the constant coefficient of the primitive minimal polynomial is
nonzero. -/
theorem coeff_zero_primitiveMinpoly_ne_zero {x : F} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    (primitiveMinpoly x).coeff 0 ≠ 0 := by
  intro h0
  have h := congrArg (fun p : ℚ[X] => p.coeff 0) (map_primitiveMinpoly hx)
  simp only [coeff_map, coeff_C_mul, h0, map_zero] at h
  rcases mul_eq_zero.mp h.symm with h' | h'
  · have hlc : ((primitiveMinpoly x).leadingCoeff : ℚ) ≠ 0 := by
      exact_mod_cast (leadingCoeff_primitiveMinpoly_pos x).ne'
    exact hlc h'
  · exact minpoly.coeff_zero_ne_zero hx.isIntegral hx0 h'

/-- For algebraic `x`, the primitive minimal polynomial has the same roots as `minpoly ℚ x` in
every commutative domain that is a `ℚ`-algebra: its image in `ℚ[X]` is a nonzero multiple of
`minpoly ℚ x`. -/
theorem rootSet_primitiveMinpoly {x : F} (hx : IsAlgebraic ℚ x) (K : Type*) [CommRing K]
    [IsDomain K] [Algebra ℚ K] : (primitiveMinpoly x).rootSet K = (minpoly ℚ x).rootSet K := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  ext z
  rw [mem_rootSet, mem_rootSet, ← aeval_map_algebraMap ℚ, algebraMap_int_eq,
    map_primitiveMinpoly hx, aeval_mul, aeval_C]
  simp [minpoly.ne_zero hx.isIntegral]

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

/-- If the primitive minimal polynomial of an algebraic `x` vanishes at `y`, possibly in another
division ring, then `x` and `y` are conjugate: they have the same minimal polynomial over `ℚ`. -/
theorem minpoly_eq_of_aeval_primitiveMinpoly_eq_zero {x : F} {y : F'} (hx : IsAlgebraic ℚ x)
    (h : aeval y (primitiveMinpoly x) = 0) : minpoly ℚ x = minpoly ℚ y := by
  rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, map_primitiveMinpoly hx, aeval_mul,
    aeval_C] at h
  exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx.isIntegral)
    ((mul_eq_zero.1 h).resolve_left (by simp)) (minpoly.monic hx.isIntegral)

/-- Reversing a primitive defining polynomial gives a multiple of the primitive
minimal polynomial of the inverse root. -/
theorem primitiveMinpoly_inv_dvd_reverse {x : F} (hx : IsAlgebraic ℚ x)
    (hx0 : x ≠ 0) : primitiveMinpoly x⁻¹ ∣ (primitiveMinpoly x).reverse := by
  apply (primitiveMinpoly_dvd_iff hx.isIntegral.inv.isAlgebraic).mpr
  simpa only [aeval_def] using
    ((primitiveMinpoly x).eval₂_inv_reverse_eq_zero_iff (algebraMap ℤ F) hx0).mpr
      (aeval_primitiveMinpoly hx)

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
    IsIntegral ℤ ((primitiveMinpoly x).leadingCoeff • x) := by
  refine ⟨_, monic_integralNormalization (primitiveMinpoly_ne_zero x), ?_⟩
  simpa only [Algebra.smul_def, aeval_def] using
    integralNormalization_aeval_eq_zero (aeval_primitiveMinpoly hx) (by simp)

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- For algebraic `x`, the denominator of `x` divides the leading coefficient of `F_x`. -/
theorem natDenominator_dvd_leadingCoeff_primitiveMinpoly {x : K} (hx : IsAlgebraic ℚ x) :
    (Algebra.natDenominator x : ℤ) ∣ (primitiveMinpoly x).leadingCoeff := by
  rw [Algebra.natDenominator_def, Int.natCast_natAbs, abs_dvd, Algebra.denominator_dvd_iff]
  exact isIntegral_leadingCoeff_primitiveMinpoly_smul hx

/-- For algebraic `x`, the integral multiple `D x` of `x` by its denominator `D` has the same
degree over `ℤ` as `x` has over `ℚ`: it generates the same field. -/
theorem natDegree_minpoly_int_natDenominator_smul {x : K} (hx : IsAlgebraic ℚ x) :
    (minpoly ℤ (Algebra.natDenominator x • x)).natDegree = (minpoly ℚ x).natDegree := by
  have hD0 : Algebra.natDenominator x ≠ 0 :=
    IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 hx)
  have hy : IsIntegral ℤ (Algebra.natDenominator x • x) := Algebra.isIntegral_natDenominator_smul x
  have hadj : ℚ⟮Algebra.natDenominator x • x⟯ = ℚ⟮x⟯ := by
    have hsmul : Algebra.natDenominator x • x =
        x * algebraMap ℚ K (Algebra.natDenominator x : ℚ) := by
      rw [nsmul_eq_mul, mul_comm, map_natCast]
    rw [hsmul, IntermediateField.adjoin_simple_mul_algebraMap x (Algebra.natDenominator x : ℚ)
      (by exact_mod_cast hD0)]
  have hmap : (minpoly ℤ (Algebra.natDenominator x • x)).map (algebraMap ℤ ℚ) =
      minpoly ℚ (Algebra.natDenominator x • x) :=
    (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy).symm
  rw [← natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hmap,
    ← IntermediateField.adjoin.finrank (K := ℚ) (hy.tower_top (A := ℚ)),
    ← IntermediateField.adjoin.finrank (K := ℚ) hx.isIntegral, hadj]

/-- For algebraic `x`, the leading coefficient of `F_x` is at most `D ^ d`, where `D` is the
denominator of `x` and `d` its degree. Together with
`natDenominator_dvd_leadingCoeff_primitiveMinpoly`, which gives `D ≤ a₀`, this bounds `a₀`
between `D` and `D ^ d`. -/
theorem leadingCoeff_primitiveMinpoly_le_natDenominator_pow {x : K} (hx : IsAlgebraic ℚ x) :
    (primitiveMinpoly x).leadingCoeff ≤
      (Algebra.natDenominator x : ℤ) ^ (minpoly ℚ x).natDegree := by
  set D : ℕ := Algebra.natDenominator x with hD
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 hx)
  have hDpos : (0 : ℤ) < (D : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hD0
  -- `D x` is integral over `ℤ` and generates the same field as `x`, so it has degree `d`.
  have hy : IsIntegral ℤ (D • x) := Algebra.isIntegral_natDenominator_smul x
  have hydeg : (minpoly ℤ (D • x)).natDegree = (minpoly ℚ x).natDegree := by
    simpa only [← hD] using natDegree_minpoly_int_natDenominator_smul hx
  -- the monic minimal polynomial of `D x`, pulled back along `X ↦ D X`, vanishes at `x`
  set Q : ℤ[X] := (minpoly ℤ (D • x)).comp (C (D : ℤ) * X) with hQ
  have hQx : aeval x Q = 0 := by
    have harg : aeval x (C (D : ℤ) * X) = D • x := by
      rw [nsmul_eq_mul, map_mul, aeval_C, aeval_X, map_natCast]
    rw [hQ, aeval_comp, harg]
    exact minpoly.aeval ℤ (D • x)
  obtain ⟨c, hc⟩ := (primitiveMinpoly_dvd_iff hx).mpr hQx
  have hp0 : primitiveMinpoly x ≠ 0 := primitiveMinpoly_ne_zero x
  have hQdeg : Q.natDegree = (minpoly ℤ (D • x)).natDegree := by
    rw [hQ, natDegree_comp, natDegree_C_mul_X _ (by simpa using hD0), mul_one]
  -- the quotient is a constant, and comparing leading coefficients gives `D ^ d = a₀ * c`
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    rw [hc, natDegree_zero, hydeg] at hQdeg
    exact absurd hQdeg (minpoly.natDegree_pos hx.isIntegral).ne'.symm
  have hcdeg : c.natDegree = 0 := by
    have h : Q.natDegree = (minpoly ℚ x).natDegree := by rw [hQdeg, hydeg]
    rw [hc, natDegree_mul hp0 hc0, natDegree_primitiveMinpoly] at h
    omega
  have hlc : (D : ℤ) ^ (minpoly ℚ x).natDegree =
      (primitiveMinpoly x).leadingCoeff * c.coeff 0 := by
    have hcC : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hcdeg
    have hQ' : Q.leadingCoeff = (primitiveMinpoly x).leadingCoeff * c.coeff 0 := by
      conv_lhs => rw [hc, hcC]
      rw [leadingCoeff_mul, leadingCoeff_C]
    have hQlc : Q.leadingCoeff = (D : ℤ) ^ (minpoly ℚ x).natDegree := by
      rw [hQ, leadingCoeff_comp (p := minpoly ℤ (D • x)) (q := C (D : ℤ) * X) (by
        rw [natDegree_C_mul_X _ (by simpa using hD0)]; exact one_ne_zero),
        (minpoly.monic hy).leadingCoeff, one_mul, leadingCoeff_C_mul_X, hydeg]
    rw [← hQlc]
    exact hQ'
  -- positivity of `D ^ d` forces `c ≠ 0` to be positive
  have hcpos : 0 < c.coeff 0 := by
    have hpos : 0 < (primitiveMinpoly x).leadingCoeff * c.coeff 0 := by
      rw [← hlc]; exact pow_pos hDpos _
    rcases mul_pos_iff.mp hpos with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (leadingCoeff_primitiveMinpoly_pos x).not_gt
  calc (primitiveMinpoly x).leadingCoeff
      = (primitiveMinpoly x).leadingCoeff * 1 := (mul_one _).symm
    _ ≤ (primitiveMinpoly x).leadingCoeff * c.coeff 0 :=
        mul_le_mul_of_nonneg_left (by omega) (leadingCoeff_primitiveMinpoly_pos x).le
    _ = (D : ℤ) ^ (minpoly ℚ x).natDegree := hlc.symm

end Field

/-! ### Examples -/

/- `F_{2/3} = 3X - 2`, in every division ring of characteristic zero. -/
example : primitiveMinpoly (((2 : ℚ) / 3 : ℚ) : F) = C 3 * X - C 2 := by
  rw [primitiveMinpoly_ratCast]
  norm_num

/- `F_x` differs from `minpoly ℤ x` at the non-integral `x = 1/2`: there `minpoly ℤ x` is the junk
value `0`, while `F_{1/2} = 2X - 1` has leading coefficient `2`, not `1`. -/
example : primitiveMinpoly (((1 : ℚ) / 2 : ℚ) : F) ≠ minpoly ℤ (((1 : ℚ) / 2 : ℚ) : F) := by
  intro h
  have hint : IsIntegral ℤ (((1 : ℚ) / 2 : ℚ) : F) :=
    by_contra fun hn ↦ primitiveMinpoly_ne_zero _ (h.trans (minpoly.eq_zero hn))
  have := congrArg leadingCoeff h
  have hden : ((1 : ℚ) / 2).den = 2 := by norm_num
  rw [(minpoly.monic hint).leadingCoeff, primitiveMinpoly_ratCast, hden, sub_eq_add_neg,
    ← C_neg, leadingCoeff_linear (by norm_num)] at this
  norm_num at this

end TauCeti
