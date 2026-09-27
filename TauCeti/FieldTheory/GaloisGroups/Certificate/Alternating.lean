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
  let f : ℤ[X] := X ^ 5 + 20 * X - 16
  let g : ℤ[X] := X ^ 4 + 4
  have hf : f.Monic := by dsimp [f]; monicity!
  have hdeg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  have hgdeg : g.natDegree = 4 := by dsimp [g]; compute_degree!
  have hder : f.derivative = C 5 * g := by
    simp [f, g]
    ring
  have hres := resultant_deriv (f := f) (natDegree_pos_iff_degree_pos.mp (by omega))
  rw [hdeg, hf.leadingCoeff, hder] at hres
  norm_num at hres
  -- Removing a multiple of the quartic leaves a linear polynomial in the resultant.
  have hred : f = C 16 * (X - C 1) + g * X := by simp [f, g]; ring
  have hresult : f.resultant g 5 4 = 16 ^ 4 * 5 := by
    rw [hred, resultant_add_mul_left _ _ _ 5 4 (by simp) (by omega)]
    rw [resultant_add_left_deg _ _ 1 4 4 (by compute_degree!)]
    rw [resultant_C_mul_left, resultant_X_sub_C_left _ _ _ (by omega)]
    norm_num [g]
  rw [resultant_C_mul_right, hresult] at hres
  norm_num at hres
  exact hres.symm

end TauCeti

namespace Polynomial

/-- The reduction of `X⁵ + 20X - 16` modulo `3` is irreducible. -/
theorem irreducible_X_pow_five_add_twenty_mul_X_sub_sixteen_zmod_three :
    Irreducible (X ^ 5 + 20 * X - 16 : (ZMod 3)[X]) := by
  let f : (ZMod 3)[X] := X ^ 5 + 20 * X - 16
  have hf : f.Monic := by dsimp [f]; monicity!
  have hdeg : f.natDegree = 5 := by dsimp [f]; compute_degree!
  have hne : f ≠ 1 := by intro h; simp [h] at hdeg
  rw [hf.irreducible_iff_lt_natDegree_lt hne]
  intro q hq hqdeg hdvd
  rw [hdeg, Finset.mem_Ioc] at hqdeg
  obtain hq1 | hq2 : q.natDegree = 1 ∨ q.natDegree = 2 := by omega
  · rw [hq.eq_X_add_C hq1, ← sub_neg_eq_add, ← C_neg, dvd_iff_isRoot] at hdvd
    have hroot : ∀ x : ZMod 3, ¬ f.IsRoot x := by
      intro x
      simp only [f, IsRoot.def, eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_ofNat]
      fin_cases x <;> decide
    exact hroot _ hdvd
  · have hqeq : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      have h := eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le hq2.le)
      have hc : q.coeff 2 = 1 := by simpa [hq2] using hq.coeff_natDegree
      simpa [hc] using h
    have hdvd' : X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) ∣
        X ^ 5 + C (20 : ZMod 3) * X + C (-16 : ZMod 3) := by
      rw [hqeq] at hdvd
      simpa only [f, C_neg, C_ofNat, sub_eq_add_neg] using hdvd
    rw [X_sq_add_C_mul_X_add_C_dvd_X_pow_five_add_iff] at hdvd'
    -- None of the nine coefficient pairs in the prime field satisfies both equations.
    have hno : ∀ a b : ZMod 3,
        ¬ (a ^ 4 - 3 * a ^ 2 * b + b ^ 2 + 20 = 0 ∧
          a ^ 3 * b - 2 * a * b ^ 2 + -16 = 0) := by decide
    exact hno _ _ hdvd'

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
