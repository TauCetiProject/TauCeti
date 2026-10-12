/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check

import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic.NormNum.IsSquare
import TauCeti.FieldTheory.GaloisGroups.Certificate.Routes
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Pure

/-!
# Pure quintics and the Frobenius certificate for `X⁵ - 2`

A pure quintic `X⁵ - a` with `a : ℤ` that is irreducible over `ℚ` has the Frobenius group
`F₂₀ = AGL(1, 5)` of order `20` as Galois group, the label `5T3`. This module proves that from
the resolvent data alone. The discriminant `3125a⁴ = 5(25a²)²` is not a square in `ℚ`, and the
resolvent sextic `X⁶ - 3125a⁴X` is separable with the rational root `0`, which is the third row
of the quintic decision table.

The Kummer example `X⁵ - 2` is then certified by the Frobenius route: it is irreducible modulo
`11`, which does not divide its discriminant `50000 = 2⁴5⁵`, that discriminant is not a square,
and `0` is a root of its separable resolvent sextic `X⁶ - 50000X`.

## Main results

* `TauCeti.hasSexticRoot_X_pow_five_sub_C`: for `a ≠ 0`, the integer `0` is a root of the
  separable resolvent sextic of `X⁵ - a`.
* `TauCeti.hasGaloisLabel_X_pow_five_sub_C`: for `a : ℤ`, a pure quintic `X⁵ - a` that is
  irreducible over `ℚ` has the label `5T3`.
* `Polynomial.factorDegrees_X_pow_five_sub_two_eleven`: `X⁵ - 2` is irreducible modulo `11`.
* `TauCeti.QuinticCertificate.check_X_pow_five_sub_two`: the Frobenius-route certificate for
  `X⁵ - 2` checks.
* `TauCeti.hasGaloisLabel_X_pow_five_sub_two`: `X⁵ - 2` has Galois label `5T3`, and
  `TauCeti.natCard_gal_X_pow_five_sub_two`: its Galois group has order `20`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §1.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

/-! ### Pure quintics -/

/-- For `a ≠ 0`, the integer `0` is a root of the resolvent sextic `X⁶ - 3125a⁴X` of the pure
quintic `X⁵ - a`, and that sextic has nonzero discriminant. -/
theorem hasSexticRoot_X_pow_five_sub_C {a : ℤ} (ha : a ≠ 0) :
    HasSexticRoot (X ^ 5 - C a) 0 := by
  refine HasSexticRoot.mk (by simp) ?_
  rw [(monic_resolventSextic _).discr_ne_zero_iff_separable_map ℚ, algebraMap_int_eq]
  exact separable_map_resolventSextic_X_pow_five_sub_C ha

/-- **An irreducible pure quintic `X⁵ - a` with `a : ℤ` has the label `5T3`.** For an integer
`a` with `X⁵ - a` irreducible over `ℚ`, the Galois group of `X⁵ - a` acting on its five roots is
the Frobenius group `F₂₀ = AGL(1, 5)` of order `20`: the discriminant `3125a⁴` is not a square,
and the resolvent sextic `X⁶ - 3125a⁴X` is separable with the rational root `0`. -/
theorem hasGaloisLabel_X_pow_five_sub_C {a : ℤ} (hirr : Irreducible (X ^ 5 - C (a : ℚ))) :
    HasGaloisLabel (X ^ 5 - C (a : ℚ)) (⟨2, by simp⟩ : TransitiveGroupIndex 5) := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, C_0, sub_zero] at hirr
    exact not_irreducible_pow (by norm_num) hirr
  have hmap : (X ^ 5 - C a : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 5 - C (a : ℚ) := by simp
  have hf : (X ^ 5 - C a : ℤ[X]).Monic := monic_X_pow_sub_C a (by norm_num)
  rw [← hmap] at hirr ⊢
  refine hasGaloisLabel_five_two_of_not_isSquare_discr_of_hasSexticRoot hf hirr
    natDegree_X_pow_sub_C (hf.isSquare_discr_map_rat_iff.not.mp ?_)
    (hasSexticRoot_X_pow_five_sub_C ha)
  rw [hmap]
  exact not_isSquare_discr_X_pow_five_sub_C (by exact_mod_cast ha)

/-! ### The Kummer quintic `X⁵ - 2` -/

/-- The discriminant of `X⁵ - 2` is `50000 = 2⁴ · 5⁵`. -/
theorem discr_X_pow_five_sub_two : (X ^ 5 - 2 : ℤ[X]).discr = 50000 := by
  rw [← C_ofNat, discr_X_pow_sub_C]
  norm_num

end TauCeti

namespace Polynomial

local instance factPrimeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The reduction of `X⁵ - 2` modulo `11` is irreducible: `2` is not a fifth power in `𝔽₁₁`. -/
theorem irreducible_X_pow_five_sub_two_zmod_eleven : Irreducible (X ^ 5 - 2 : (ZMod 11)[X]) := by
  rw [← C_ofNat]
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_five (by decide)

/-- `X⁵ - 2` has a single irreducible factor of degree five modulo `11`. -/
@[simp] theorem factorDegrees_X_pow_five_sub_two_eleven :
    (X ^ 5 - 2 : ℤ[X]).factorDegrees 11 = {5} := by
  rw [factorDegrees_eq_singleton_iff]
  norm_num only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat]
  exact ⟨irreducible_X_pow_five_sub_two_zmod_eleven, by compute_degree!⟩

end Polynomial

namespace TauCeti

/-- The Frobenius-route certificate for `X⁵ - 2` checks: it is irreducible modulo `11`, which
does not divide its discriminant `50000`, the discriminant is not a square, and `0` is a root of
its separable resolvent sextic `X⁶ - 50000X`. -/
@[simp] theorem QuinticCertificate.check_X_pow_five_sub_two :
    (QuinticCertificate.frobeniusF20 11 0).check (X ^ 5 - 2) = true := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hgood : IsGoodPrime (X ^ 5 - 2) 11 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_two]
    decide
  rw [QuinticCertificate.check_eq_true_iff, QuinticCertificate.verifies_frobeniusF20_iff]
  refine ⟨HasFactorDegrees.mk hgood Polynomial.factorDegrees_X_pow_five_sub_two_eleven, ?_, ?_⟩
  · rw [discr_X_pow_five_sub_two]
    norm_num
  · rw [← C_ofNat]
    exact hasSexticRoot_X_pow_five_sub_C two_ne_zero

/-- **`X⁵ - 2` has Galois label `5T3`**: its Galois group over `ℚ` is the Frobenius group `F₂₀`.
This is the Kummer example. -/
theorem hasGaloisLabel_X_pow_five_sub_two :
    HasGaloisLabel ((X ^ 5 - 2 : ℤ[X]).map (Int.castRingHom ℚ))
      (⟨2, by simp⟩ : TransitiveGroupIndex 5) := by
  have h := QuinticCertificate.check_sound (by monicity! : (X ^ 5 - 2 : ℤ[X]).Monic)
    QuinticCertificate.check_X_pow_five_sub_two
  rwa [QuinticCertificate.label_frobeniusF20] at h

/-- The Galois group of `X⁵ - 2` over `ℚ` has order `20`. -/
theorem natCard_gal_X_pow_five_sub_two : Nat.card (X ^ 5 - 2 : ℚ[X]).Gal = 20 := by
  have hmap : (X ^ 5 - 2 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 5 - 2 := by simp
  rw [← hmap, hasGaloisLabel_X_pow_five_sub_two.natCard_gal, natCard_referenceSubgroup_five_two]

end TauCeti
