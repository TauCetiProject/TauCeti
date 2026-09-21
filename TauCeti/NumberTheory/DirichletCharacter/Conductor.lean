/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Products of characters with coprime conductors

The conductor of a product of Dirichlet characters with pairwise coprime conductors is the
product of their conductors. In particular, primitive characters at pairwise coprime levels
remain primitive after lifting to the product level and multiplying. This applies to the
quadratic characters attached to the prime factors of a fundamental discriminant.
-/

public section

namespace TauCeti

open DirichletCharacter

/-- Multiplication cannot cancel any conductor factor when the two conductors are coprime. -/
theorem conductor_mul_eq_mul_of_coprime {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    {χ ψ : DirichletCharacter R N} (hcop : χ.conductor.Coprime ψ.conductor) :
    (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  apply Nat.dvd_antisymm
  · simpa only [hcop.lcm_eq_mul] using conductor_mul_dvd_lcm_conductor χ ψ
  · apply hcop.mul_dvd_of_dvd_of_dvd
    · apply hcop.dvd_of_dvd_mul_right
      have h := (conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹).trans
        (Nat.lcm_dvd_mul _ _)
      simpa only [mul_inv_cancel_right, conductor_inv] using h
    · apply hcop.symm.dvd_of_dvd_mul_right
      have h := (conductor_mul_dvd_lcm_conductor (ψ * χ) χ⁻¹).trans
        (Nat.lcm_dvd_mul _ _)
      rw [mul_inv_cancel_right, conductor_inv, mul_comm ψ χ] at h
      exact h

/-- The conductor of a finite product is the product of the pairwise coprime conductors. -/
theorem conductor_prod_eq_prod_of_pairwise_coprime {R ι : Type*} [CommMonoidWithZero R]
    {N : ℕ} [NeZero N] {s : Finset ι} {χ : ι → DirichletCharacter R N}
    (hcop : (s : Set ι).Pairwise fun i j ↦ (χ i).conductor.Coprime (χ j).conductor) :
    (∏ i ∈ s, χ i).conductor = ∏ i ∈ s, (χ i).conductor := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conductor_one]
  | @insert i s hi ih =>
    have hs := hcop.mono (by simp : (s : Set ι) ⊆ ↑(insert i s))
    have hc : (χ i).conductor.Coprime (∏ j ∈ s, (χ j).conductor) :=
      Nat.Coprime.prod_right fun j hj ↦ hcop (by simp) (by simp [hj])
        (by rintro rfl; exact hi hj)
    rw [Finset.prod_insert hi, conductor_mul_eq_mul_of_coprime (by rwa [ih hs]),
      ih hs, Finset.prod_insert hi]

end TauCeti
