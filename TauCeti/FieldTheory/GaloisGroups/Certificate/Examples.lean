/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Check
public import TauCeti.FieldTheory.GaloisGroups.Symmetric.Basic

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree
import TauCeti.Algebra.Polynomial.SpecificDegree
import TauCeti.FieldTheory.GaloisGroups.Certificate.Generic
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees

/-!
# Examples of quintic Galois-group certificate evidence

This module works out the two standard Frobenius-cycle routes to the symmetric quintic Galois group
`S₅` (label `5T5`):

* `X⁵ - X - 1`, certified by `QuinticCertificate.symmetric 5 2` from its factorizations of degrees
  `{5}` modulo `5` and `{2, 3}` modulo `2`;
* `X⁵ - X + 3`, certified from its factorizations of degrees `{5}` modulo `5` and `{1, 1, 1, 2}`
  modulo `3` via `TauCeti.hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two` and
  `TauCeti.hasGaloisLabel_five_four_of_factorDegrees_five_and_one_one_one_two`.

## Main results

* `TauCeti.QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one`,
  `TauCeti.hasGaloisLabel_X_pow_five_sub_X_sub_one`: symmetric-route certificate and label `5T5`
  for `X⁵ - X - 1`.
* `TauCeti.monic_X_pow_five_sub_X_add_three`, `TauCeti.discr_X_pow_five_sub_X_add_three`,
  `Polynomial.factorDegrees_X_pow_five_sub_X_add_three_five`,
  `Polynomial.factorDegrees_X_pow_five_sub_X_add_three_three`: monicity, discriminant, and factor
  degrees modulo `5` and `3` of `X⁵ - X + 3`.
* `TauCeti.hasFullSymmetricGaloisGroup_X_pow_five_sub_X_add_three`,
  `TauCeti.hasGaloisLabel_X_pow_five_sub_X_add_three`: full symmetric Galois group `S₅` and label
  `5T5` for `X⁵ - X + 3`.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

/-! ### `X ^ 5 - X - 1` via `{5}` modulo `5` and `{2, 3}` modulo `2` -/

/-- `X⁵ - X - 1` has a symmetric-route certificate: it is irreducible modulo `5`, and has factor
degrees `(2,3)` modulo `2`. Both primes are good, since neither divides its discriminant. -/
theorem QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one :
    (QuinticCertificate.symmetric 5 2).check (X ^ 5 - X - 1) = true := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := monic_X_pow_five_sub_X_sub_one
  have hirr := (factorDegrees_eq_singleton_iff.mp factorDegrees_X_pow_five_sub_X_sub_one_five).1
  have hgood5 : IsGoodPrime (X ^ 5 - X - 1) 5 := (isGoodPrime_iff _ 5).mpr <|
    (hf.separable_map_zmod_iff_not_dvd_discr 5).mp (PerfectField.separable_of_irreducible hirr)
  have hgood2 : IsGoodPrime (X ^ 5 - X - 1) 2 :=
    (isGoodPrime_iff _ 2).mpr not_two_dvd_discr_X_pow_five_sub_X_sub_one
  rw [QuinticCertificate.check_eq_true_iff, QuinticCertificate.verifies_symmetric_iff]
  refine ⟨HasFactorDegrees.mk hgood5 factorDegrees_X_pow_five_sub_X_sub_one_five,
    HasFactorDegrees.mk hgood2 ?_⟩
  rw [factorDegrees_X_pow_five_sub_X_sub_one_two]
  decide

/-- **`X⁵ - X - 1` has label `5T5`.** Its symmetric-route certificate checks. -/
theorem hasGaloisLabel_X_pow_five_sub_X_sub_one :
    HasGaloisLabel ((X ^ 5 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ))
      (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have h := QuinticCertificate.check_sound monic_X_pow_five_sub_X_sub_one
    QuinticCertificate.check_symmetric_X_pow_five_sub_X_sub_one
  rwa [QuinticCertificate.label_symmetric] at h

/-! ### `X ^ 5 - X + 3` via `{5}` modulo `5` and `{1, 1, 1, 2}` modulo `3` -/

/-- `X ^ 5 - X + 3` is monic over `ℤ`. -/
theorem monic_X_pow_five_sub_X_add_three : (X ^ 5 - X + 3 : ℤ[X]).Monic := by
  have h : (X ^ 5 - X + 3 : ℤ[X]) = X ^ 5 - (X - 3) := by ring
  rw [h]
  exact monic_X_pow_sub (by compute_degree!)

/-- The discriminant of `X ^ 5 - X + 3` is `5⁵ · 3⁴ - 4⁴ = 252869`. -/
theorem discr_X_pow_five_sub_X_add_three : (X ^ 5 - X + 3 : ℤ[X]).discr = 252869 := by
  have h : (X ^ 5 - X + 3 : ℤ[X]) = X ^ 5 + C (-1 : ℤ) * X + C (3 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [h, discr_X_pow_five_add_C_mul_X_add_C]
  norm_num

end TauCeti

namespace Polynomial

local instance factPrimeFiveExamples : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `X ^ 5 - X + 3` is an Artin–Schreier quintic modulo `5` and is therefore irreducible over
`ZMod 5`. -/
theorem irreducible_X_pow_five_sub_X_add_three_zmod_five :
    Irreducible (X ^ 5 - X + 3 : (ZMod 5)[X]) := by
  have h : (X ^ 5 - X + 3 : (ZMod 5)[X]) = X ^ 5 + C (-1) * X + C 3 := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [h]
  exact irreducible_X_pow_five_add_C_mul_X_add_C (by decide) (by decide)

/-- `X ^ 5 - X + 3` has factor degrees `{5}` modulo `5`. -/
@[simp] theorem factorDegrees_X_pow_five_sub_X_add_three_five :
    (X ^ 5 - X + 3 : ℤ[X]).factorDegrees 5 = {5} := by
  rw [Polynomial.factorDegrees_eq_singleton_iff]
  have hmap : (X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom (ZMod 5)) = X ^ 5 - X + 3 := by
    simp
  rw [hmap]
  refine ⟨irreducible_X_pow_five_sub_X_add_three_zmod_five, ?_⟩
  have h : (X ^ 5 - X + 3 : (ZMod 5)[X]) = X ^ 5 - (X - 3) := by ring
  rw [h]
  compute_degree!

/-- `X ^ 2 + 1` is irreducible over `ZMod 3`: `-1` is not a square modulo `3`. -/
theorem irreducible_X_sq_add_one_zmod_three : Irreducible (X ^ 2 + 1 : (ZMod 3)[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    rw [hdeg]
    decide
  · intro x
    rw [Polynomial.IsRoot.def]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- Modulo `3`, `X ^ 5 - X + 3` reduces to `X ^ 5 - X = X * (X - 1) * (X + 1) * (X ^ 2 + 1)`, so
its factor degrees are `{1, 1, 1, 2}`. -/
@[simp] theorem factorDegrees_X_pow_five_sub_X_add_three_three :
    (X ^ 5 - X + 3 : ℤ[X]).factorDegrees 3 = {1, 1, 1, 2} := by
  let s : Multiset (ZMod 3)[X] := {X, X - C 1, X - C (-1), X ^ 2 + 1}
  have hs : ∀ q ∈ s, Irreducible q := by
    intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact irreducible_X
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact irreducible_X_sub_C 1
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact irreducible_X_sub_C (-1)
    · rw [Multiset.mem_singleton.mp hq]
      exact irreducible_X_sq_add_one_zmod_three
  have hmap : (X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom (ZMod 3)) = s.prod := by
    have h3 : (3 : (ZMod 3)[X]) = 0 := by simpa using CharP.cast_eq_zero (ZMod 3)[X] 3
    dsimp [s]
    simp only [Multiset.prod_cons, Multiset.prod_singleton,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, C_1, map_neg, h3]
    ring
  rw [Polynomial.factorDegrees_eq_map_natDegree_of_map_eq_prod hs hmap]
  have hd2 : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
  simp only [s, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    natDegree_X, natDegree_X_sub_C, hd2]

end Polynomial

namespace TauCeti

/-- `X ^ 5 - X + 3` has full symmetric Galois group `S₅` over `ℚ`. -/
theorem hasFullSymmetricGaloisGroup_X_pow_five_sub_X_add_three :
    ((X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom ℚ)).HasFullSymmetricGaloisGroup := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hgood5 : IsGoodPrime (X ^ 5 - X + 3) 5 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  have hgood3 : IsGoodPrime (X ^ 5 - X + 3) 3 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  refine hasFullSymmetricGaloisGroup_of_prime_and_replicate_one_add_two
    monic_X_pow_five_sub_X_add_three Nat.prime_five
    (HasFactorDegrees.mk hgood5 factorDegrees_X_pow_five_sub_X_add_three_five)
    (HasFactorDegrees.mk hgood3 ?_)
  rw [factorDegrees_X_pow_five_sub_X_add_three_three]
  decide

/-- **`X ^ 5 - X + 3` has label `5T5`** from its factorizations modulo `5` and `3`. -/
theorem hasGaloisLabel_X_pow_five_sub_X_add_three :
    HasGaloisLabel ((X ^ 5 - X + 3 : ℤ[X]).map (Int.castRingHom ℚ))
      (⟨4, by simp⟩ : TransitiveGroupIndex 5) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hgood5 : IsGoodPrime (X ^ 5 - X + 3) 5 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  have hgood3 : IsGoodPrime (X ^ 5 - X + 3) 3 := by
    rw [isGoodPrime_iff, discr_X_pow_five_sub_X_add_three]
    decide
  exact hasGaloisLabel_five_four_of_factorDegrees_five_and_one_one_one_two
    monic_X_pow_five_sub_X_add_three
    (HasFactorDegrees.mk hgood5 factorDegrees_X_pow_five_sub_X_add_three_five)
    (HasFactorDegrees.mk hgood3 factorDegrees_X_pow_five_sub_X_add_three_three)

end TauCeti
