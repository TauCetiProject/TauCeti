/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Perfect
public import TauCeti.Algebra.CharP.ExpChar

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
/-- If every finite extension of `R` whose degree is not divisible by a prime `p` is trivial,
and the characteristic exponent of `R` is a prime distinct from `p`, then `R` is perfect. -/
theorem perfectField_of_forall_finrank_eq_one_of_not_dvd
    {R : Type u} {E : Type v} [Field R] [Field E] [Algebra R E] [FiniteDimensional R E]
    {p : ℕ} [Fact p.Prime]
    (hnotdvd : ∀ (F : Type v) [Field F] [Algebra R F] [FiniteDimensional R F],
      ¬ p ∣ Module.finrank R F → Module.finrank R F = 1)
    (hchar_ne_p : ringExpChar R ≠ p) (hchar_ne_one : ringExpChar R ≠ 1) :
    PerfectField R := by
  let q := ringExpChar R
  have hqp : q ≠ p := by simpa [q] using hchar_ne_p
  let : ExpChar R q := ringExpChar.expChar R
  have hqprime : q.Prime :=
    ExpChar.prime_of_ne_one R q (by simpa [q] using hchar_ne_one)
  let Ω := AlgebraicClosure E
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
  have hmonicΩ : g.Monic := by
    dsimp [g]
    exact hmonic.map (algebraMap R Ω)
  have hdeg : g.degree ≠ 0 := by
    change (f.map (algebraMap R Ω)).degree ≠ 0
    rw [degree_eq_natDegree hmonicΩ.ne_zero,
      natDegree_map_eq_of_injective (algebraMap R Ω).injective]
    unfold f
    rw [natDegree_X_pow_sub_C]
    intro hz
    exact hqprime.ne_zero (by exact_mod_cast hz)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero Ω g hdeg
  have hyR : aeval y f = 0 := by
    change eval₂ (algebraMap R Ω) y f = 0
    rw [eval₂_eq_eval_map]
    simpa [aeval_def, g] using hy
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hyR hmonic
  let F := R⟮y⟯
  let : FiniteDimensional R F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  have hFdeg : Module.finrank R F = q := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y), ← hmin]
    change (X ^ q - C a).natDegree = q
    exact natDegree_X_pow_sub_C
  have hFnotdvd : ¬ p ∣ Module.finrank R F := by
    rw [hFdeg]
    intro hdiv
    exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqprime).mp hdiv).symm
  have hFone := hnotdvd F hFnotdvd
  rw [hFdeg] at hFone
  exact hqprime.ne_one hFone

end TauCeti

end
