/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Examples

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# A cyclic quintic certificate

The polynomial `X⁵ + X⁴ - 4X³ - 3X² + 3X + 1` is irreducible modulo `2`.
Together with its second root `X² - 2` in the root field, this supplies a
cyclic-route certificate and proves that its Galois group has label `5T1`.
This polynomial defines the LMFDB number field `5.5.14641.1`.

## Main results

* `TauCeti.factorDegrees_cyclicQuintic_two`: the irreducible reduction at `2`.
* `TauCeti.QuinticCertificate.check_cyclicQuintic`: the certificate checks.
* `TauCeti.hasGaloisLabel_cyclicQuintic`: the Galois label is `5T1`.
-/

public section
noncomputable section

open Polynomial

namespace TauCeti

private theorem cyclicQuintic_mod_two_no_root (c : ZMod 2) :
    c ^ 5 + c ^ 4 + c ^ 2 + c + 1 ≠ 0 := by
  fin_cases c <;> decide

private theorem cyclicQuintic_mod_two_no_quadratic (a b : ZMod 2) :
    ¬ (X ^ 2 + C a * X + C b : (ZMod 2)[X]) ∣
      (X ^ 5 + X ^ 4 + X ^ 2 + X + 1) := by
  intro hdvd
  let q : (ZMod 2)[X] := X ^ 2 + C a * X + C b
  let g : (ZMod 2)[X] := X ^ 5 + X ^ 4 + X ^ 2 + X + 1
  have hdvd' : q ∣ g := hdvd
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals
    first
    | have hq : eval (0 : ZMod 2) q = 0 := by simp [q]
      have hg : eval (0 : ZMod 2) g ≠ 0 := by
        simpa only [g, eval_add, eval_pow, eval_X, eval_one] using
          cyclicQuintic_mod_two_no_root 0
      exact hg (eval_eq_zero_of_dvd_of_eval_eq_zero hdvd' hq)
    | have hq : eval (1 : ZMod 2) q = 0 := by
        simp only [q, eval_add, eval_pow, eval_X, eval_C, eval_mul]
        decide
      have hg : eval (1 : ZMod 2) g ≠ 0 := by
        simpa only [g, eval_add, eval_pow, eval_X, eval_one] using
          cyclicQuintic_mod_two_no_root 1
      exact hg (eval_eq_zero_of_dvd_of_eval_eq_zero hdvd' hq)
    | have hident : g = q * (X ^ 3 + X) + 1 := by
        have hidentity : (X ^ 5 + X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]) =
            (X ^ 2 + X + 1) * (X ^ 3 + X) + 1 := by
          linear_combination -(X ^ 3 : (ZMod 2)[X]) *
            (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)
        simpa [g, q] using hidentity
      have hmul : q ∣ q * (X ^ 3 + X) := dvd_mul_right _ _
      have hone := dvd_sub hdvd' hmul
      rw [hident, add_sub_cancel_left] at hone
      have hdeg : q.natDegree = 2 := by dsimp [q]; compute_degree!
      have hle := natDegree_le_of_dvd hone (by simp : (1 : (ZMod 2)[X]) ≠ 0)
      rw [hdeg, natDegree_one] at hle
      omega

/-- The reduction of the cyclic quintic modulo `2` is irreducible. -/
theorem irreducible_cyclicQuintic_mod_two :
    Irreducible (X ^ 5 + X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  let g : (ZMod 2)[X] := X ^ 5 + X ^ 4 + X ^ 2 + X + 1
  have hgmonic : g.Monic := by dsimp [g]; monicity!
  have hgdeg : g.natDegree = 5 := by dsimp [g]; compute_degree!
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hgdeg
    omega
  rw [hgmonic.irreducible_iff_lt_natDegree_lt hg1]
  intro q hq hdeg hdvd
  have hdeg' : q.natDegree = 1 ∨ q.natDegree = 2 := by
    rw [hgdeg] at hdeg
    simp only [Finset.mem_Ioc] at hdeg
    omega
  rcases hdeg' with hdeg' | hdeg'
  · rw [hq.eq_X_add_C hdeg'] at hdvd
    rw [← sub_neg_eq_add, ← Polynomial.C_neg, Polynomial.dvd_iff_isRoot,
      Polynomial.IsRoot.def] at hdvd
    simp only [g, eval_add, eval_pow, eval_X, eval_one] at hdvd
    exact (cyclicQuintic_mod_two_no_root _) hdvd
  · let a := q.coeff 1
    let b := q.coeff 0
    have hqeq : q = X ^ 2 + C a * X + C b := by
      rw [Polynomial.eq_quadratic_of_degree_le_two
        (Polynomial.degree_le_of_natDegree_le hdeg'.le)]
      have hc : q.coeff 2 = 1 := by simpa [hdeg'] using hq.coeff_natDegree
      rw [hc]
      simp [a, b]
    rw [hqeq] at hdvd
    exact (cyclicQuintic_mod_two_no_quadratic a b) hdvd

/-- The cyclic quintic has a single irreducible factor of degree five modulo `2`. -/
theorem factorDegrees_cyclicQuintic_two :
    (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).factorDegrees 2 = {5} := by
  rw [Polynomial.factorDegrees_eq_singleton_iff]
  have hmap : (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).map
      (Int.castRingHom (ZMod 2)) = (X ^ 5 + X ^ 4 + X ^ 2 + X + 1 : (ZMod 2)[X]) := by
    norm_num
    linear_combination (-2 * X ^ 3 - 2 * X ^ 2 + X : (ZMod 2)[X]) *
      (CharTwo.two_eq_zero : (2 : (ZMod 2)[X]) = 0)
  rw [hmap]
  constructor
  · exact irreducible_cyclicQuintic_mod_two
  · compute_degree!

/-- The cyclic-route certificate for the cyclic quintic checks. -/
theorem QuinticCertificate.check_cyclicQuintic :
    (QuinticCertificate.cyclic 2 (X ^ 2 - 2)).check
      (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1) = true := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).Monic := by
    monicity!
  have hirr : Irreducible ((X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).map
      (Int.castRingHom (ZMod 2))) :=
    (Polynomial.factorDegrees_eq_singleton_iff.mp factorDegrees_cyclicQuintic_two).1
  have hgood : IsGoodPrime (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1) 2 :=
    (isGoodPrime_iff _ 2).mpr <|
      (hf.separable_map_zmod_iff_not_dvd_discr 2).mp
        (PerfectField.separable_of_irreducible hirr)
  rw [QuinticCertificate.check_eq_true_iff, QuinticCertificate.verifies_cyclic_iff]
  exact ⟨HasFactorDegrees.mk hgood factorDegrees_cyclicQuintic_two,
    hasSecondRootInRootField_cyclicQuintic⟩

/-- The cyclic quintic `X⁵ + X⁴ - 4X³ - 3X² + 3X + 1` has Galois label `5T1`. -/
theorem hasGaloisLabel_cyclicQuintic :
    HasGaloisLabel
      ((X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).map
        (Int.castRingHom ℚ)) (⟨0, by simp⟩ : TransitiveGroupIndex 5) := by
  have hf : (X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1 : ℤ[X]).Monic := by
    monicity!
  have h := QuinticCertificate.check_sound hf QuinticCertificate.check_cyclicQuintic
  rwa [QuinticCertificate.label_cyclic] at h

end TauCeti
