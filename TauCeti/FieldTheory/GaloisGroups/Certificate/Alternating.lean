/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check

import TauCeti.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# An alternating quintic certificate

The polynomial `X⁵ + 20X - 16` has discriminant `32000²`, is irreducible modulo `3`,
and has factor degrees `(1,1,3)` modulo `7`. These data give an alternating-route
certificate, proving that its Galois group over `ℚ` has label `5T4`.

The main results are `TauCeti.QuinticCertificate.check_X_pow_five_add_twenty_mul_X_sub_sixteen`
and `TauCeti.hasGaloisLabel_X_pow_five_add_twenty_mul_X_sub_sixteen`.
-/

public section

open Polynomial

namespace TauCeti

/-- The discriminant of `X⁵ + 20X - 16` is `32000²`. -/
theorem discr_X_pow_five_add_twenty_mul_X_sub_sixteen :
    (X ^ 5 + 20 * X - 16 : ℤ[X]).discr = 32000 ^ 2 := by
  simpa [sub_eq_add_neg] using discr_X_pow_five_add_C_mul_X_add_C (20 : ℤ) (-16)

end TauCeti

namespace Polynomial

/-- The reduction of `X⁵ + 20X - 16` modulo `3` is irreducible. -/
theorem irreducible_X_pow_five_add_twenty_mul_X_sub_sixteen_zmod_three :
    Irreducible (X ^ 5 + 20 * X - 16 : (ZMod 3)[X]) := by
  have hf : (X ^ 5 + 20 * X - 16 : (ZMod 3)[X]) = X ^ 5 + C 20 * X + C (-16) := by
    simp only [map_neg, C_ofNat]
    ring
  rw [hf]
  exact irreducible_X_pow_five_add_C_mul_X_add_C (by decide) (by decide)

/-- The alternating quintic has a single irreducible factor of degree five modulo `3`. -/
@[simp] theorem factorDegrees_X_pow_five_add_twenty_mul_X_sub_sixteen_three :
    (X ^ 5 + 20 * X - 16 : ℤ[X]).factorDegrees 3 = {5} := by
  rw [factorDegrees_eq_singleton_iff]
  norm_num only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat]
  exact ⟨irreducible_X_pow_five_add_twenty_mul_X_sub_sixteen_zmod_three, by compute_degree!⟩

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The reduction of `X⁵ + 20X - 16` modulo `7` has factor degrees `{1, 1, 3}`. -/
@[simp] theorem factorDegrees_X_pow_five_add_twenty_mul_X_sub_sixteen_seven :
    (X ^ 5 + 20 * X - 16 : ℤ[X]).factorDegrees 7 = {1, 1, 3} := by
  have hirr : Irreducible (X ^ 3 + 5 * X ^ 2 + 5 * X + 2 : (ZMod 7)[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · have hd : (X ^ 3 + 5 * X ^ 2 + 5 * X + 2 : (ZMod 7)[X]).natDegree = 3 := by
        compute_degree!
      simp [hd]
    · intro x
      simp only [IsRoot.def, eval_add, eval_pow, eval_mul, eval_X, eval_ofNat]
      fin_cases x <;> decide
  let factors : Multiset (ZMod 7)[X] :=
    {X - C 2, X - C 3, X ^ 3 + 5 * X ^ 2 + 5 * X + 2}
  have hfactors : ∀ p ∈ factors, Irreducible p := by
    intro p hp
    simp only [factors, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact irreducible_X_sub_C _
    · exact irreducible_X_sub_C _
    · exact hirr
  have hprod : (X ^ 5 + 20 * X - 16 : ℤ[X]).map (Int.castRingHom (ZMod 7)) =
      factors.prod := by
    have hseven : (7 : (ZMod 7)[X]) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (ZMod 7)[X] 7
    norm_num [factors, C_ofNat]
    linear_combination (2 * X ^ 3 - X ^ 2 - 4 : (ZMod 7)[X]) * hseven
  rw [factorDegrees_eq_map_natDegree_of_map_eq_prod hfactors hprod]
  have hd : (X ^ 3 + 5 * X ^ 2 + 5 * X + 2 : (ZMod 7)[X]).natDegree = 3 := by
    compute_degree!
  simp [factors, hd]

end Polynomial

namespace TauCeti

/-- The alternating-route certificate for `X⁵ + 20X - 16` checks, using primes `3` and `7`
and the square root `32000` of its discriminant. -/
@[simp] theorem QuinticCertificate.check_X_pow_five_add_twenty_mul_X_sub_sixteen :
    (QuinticCertificate.alternating 3 7 32000).check (X ^ 5 + 20 * X - 16) = true := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hgood3 : IsGoodPrime (X ^ 5 + 20 * X - 16) 3 := by
    rw [isGoodPrime_iff, discr_X_pow_five_add_twenty_mul_X_sub_sixteen]
    decide
  have hgood7 : IsGoodPrime (X ^ 5 + 20 * X - 16) 7 := by
    rw [isGoodPrime_iff, discr_X_pow_five_add_twenty_mul_X_sub_sixteen]
    decide
  rw [QuinticCertificate.check_eq_true_iff, QuinticCertificate.verifies_alternating_iff]
  exact ⟨HasFactorDegrees.mk hgood3
      factorDegrees_X_pow_five_add_twenty_mul_X_sub_sixteen_three,
    discr_X_pow_five_add_twenty_mul_X_sub_sixteen,
    HasFactorDegrees.mk hgood7 factorDegrees_X_pow_five_add_twenty_mul_X_sub_sixteen_seven⟩

/-- **`X⁵ + 20X - 16` has Galois label `5T4`.** -/
theorem hasGaloisLabel_X_pow_five_add_twenty_mul_X_sub_sixteen :
    HasGaloisLabel ((X ^ 5 + 20 * X - 16 : ℤ[X]).map (Int.castRingHom ℚ))
      (⟨3, by simp⟩ : TransitiveGroupIndex 5) := by
  -- Apply the certificate soundness theorem `TauCeti.QuinticCertificate.check_sound`.
  have h := QuinticCertificate.check_sound (by monicity! :
    (X ^ 5 + 20 * X - 16 : ℤ[X]).Monic)
    QuinticCertificate.check_X_pow_five_add_twenty_mul_X_sub_sixteen
  simpa only [QuinticCertificate.label_alternating] using h

end TauCeti
