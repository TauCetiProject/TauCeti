/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Field.ULift

/-!
# Perfect fields

This file records a perfectness criterion from the degrees of finite extensions.

## Main results

* `TauCeti.perfectField_of_forall_finrank_eq_one_of_not_dvd`
-/

public section

namespace TauCeti

universe u v

open IntermediateField

open Polynomial in
/-- If every finite extension of `R` whose degree is not divisible by a prime `p` is trivial and
the characteristic exponent of `R` differs from `p`, then `R` is perfect. -/
theorem perfectField_of_forall_finrank_eq_one_of_not_dvd
    {R : Type u} [Field R]
    {p : ℕ} [Fact p.Prime]
    (hnotdvd : ∀ (F : Type (max u v)) [Field F] [Algebra R F] [FiniteDimensional R F],
      ¬ p ∣ Module.finrank R F → Module.finrank R F = 1)
    (hchar_ne_p : ringExpChar R ≠ p) :
    PerfectField R := by
  by_cases hqone : ringExpChar R = 1
  · have hExpChar : ExpChar R 1 := hqone ▸ ringExpChar.expChar R
    have hCharZero : CharZero R := @charZero_of_expChar_one' R inferInstance hExpChar
    exact @PerfectField.ofCharZero R inferInstance hCharZero
  · have hchar_ne_one : ringExpChar R ≠ 1 := hqone
    let q := ringExpChar R
    have hqp : q ≠ p := by simpa [q] using hchar_ne_p
    let : ExpChar R q := ringExpChar.expChar R
    have hqprime : q.Prime := (expChar_is_prime_or_one R q).resolve_right
      (by simpa [q] using hchar_ne_one)
    let R' := ULift.{v, u} R
    let Ω := AlgebraicClosure R'
    suffices Function.Surjective (frobenius R q) by
      exact (PerfectRing.ofSurjective R q ‹_›).toPerfectField
    intro a
    by_contra h
    have ha : ∀ b : R, b ^ q ≠ a := by
      intro b hb
      apply h
      exact ⟨b, by rw [frobenius_def]; exact hb⟩
    let f : Polynomial R := X ^ q - C a
    have hirr : Irreducible f := by
      simpa [f] using X_pow_sub_C_irreducible_of_prime hqprime ha
    have hmonic : f.Monic := by simpa [f] using monic_X_pow_sub_C a hqprime.ne_zero
    let g : Polynomial Ω := f.map (algebraMap R Ω)
    have hmonicΩ : (f.map (algebraMap R Ω)).Monic := hmonic.map (algebraMap R Ω)
    have hfnat : f.natDegree = q := by
      simpa only [f] using (natDegree_X_pow_sub_C (n := q) (r := a))
    have hdeg : g.degree ≠ 0 := by
      unfold g
      rw [degree_eq_natDegree hmonicΩ.ne_zero,
        natDegree_map_eq_of_injective (algebraMap R Ω).injective, hfnat]
      exact_mod_cast Nat.ne_of_gt hqprime.pos
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero Ω g hdeg
    have hyR : aeval y f = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      unfold g at hy
      simpa only [aeval_def, eval₂_eq_eval_map, Algebra.algebraMap_self, Polynomial.map_id] using hy
    have hmin := minpoly.eq_of_irreducible_of_monic hirr hyR hmonic
    let F := R⟮y⟯
    have hyIntegral : IsIntegral R y := ⟨f, hmonic, by simpa [aeval_def] using hyR⟩
    let : FiniteDimensional R F := IntermediateField.adjoin.finiteDimensional hyIntegral
    have hFdeg : Module.finrank R F = q := by
      rw [IntermediateField.adjoin.finrank hyIntegral, ← hmin]
      simpa only [f] using (natDegree_X_pow_sub_C (n := q) (r := a))
    have hFnotdvd : ¬ p ∣ Module.finrank R F := by
      rw [hFdeg]
      intro hdiv
      exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqprime).mp hdiv).symm
    have hFone := hnotdvd F hFnotdvd
    rw [hFdeg] at hFone
    exact hqprime.ne_one hFone

end TauCeti

end
