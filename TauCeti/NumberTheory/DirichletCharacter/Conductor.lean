/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Dirichlet character conductors

An injective change of coefficient ring preserves the conductor and primitivity of a Dirichlet
character. The conductor of a product of Dirichlet characters with pairwise coprime conductors is
the product of their conductors. In particular, primitive characters at pairwise coprime levels
remain primitive after lifting to the product level and multiplying. This applies to the quadratic
characters attached to the prime factors of a fundamental discriminant.
-/

public section

namespace DirichletCharacter

/-! ### Injective changes of the coefficient ring -/

/-- Factoring a Dirichlet character through a lower level is unchanged by an injective change of
coefficient ring. -/
theorem factorsThrough_ringHomComp_iff {R R' : Type*} [CommRing R] [CommRing R']
    {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Function.Injective f) :
    FactorsThrough (χ.ringHomComp f) d ↔ FactorsThrough χ d := by
  by_cases hd : d ∣ n
  · rw [factorsThrough_iff_ker_unitsMap hd, factorsThrough_iff_ker_unitsMap hd]
    constructor
    · intro h u hu
      specialize h hu
      rw [MonoidHom.mem_ker] at h ⊢
      apply Units.ext
      apply hf
      simpa using congrArg ((↑) : R'ˣ → R') h
    · intro h u hu
      specialize h hu
      rw [MonoidHom.mem_ker] at h ⊢
      apply Units.ext
      simpa using congrArg f (congrArg ((↑) : Rˣ → R) h)
  · exact ⟨fun h ↦ (hd h.dvd).elim, fun h ↦ (hd h.dvd).elim⟩

/-- An injective change of coefficient ring preserves the conductor of a Dirichlet character. -/
theorem conductor_ringHomComp {R R' : Type*} [CommRing R] [CommRing R']
    {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Function.Injective f) : conductor (χ.ringHomComp f) = conductor χ := by
  apply congrArg sInf
  ext d
  exact factorsThrough_ringHomComp_iff χ f hf

/-- An injective change of coefficient ring preserves primitivity of a Dirichlet character. -/
theorem isPrimitive_ringHomComp_iff {R R' : Type*} [CommRing R] [CommRing R']
    {n : ℕ} [NeZero n] (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Function.Injective f) : IsPrimitive (χ.ringHomComp f) ↔ IsPrimitive χ := by
  rw [isPrimitive_def, isPrimitive_def, conductor_ringHomComp χ f hf]

end DirichletCharacter

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

/-- The conductor of a finite product is the product of the pairwise coprime conductors,
provided the product is nonempty or the level is nonzero. -/
theorem conductor_prod_eq_prod_of_pairwise_coprime {R ι : Type*} [CommMonoidWithZero R]
    {N : ℕ} {s : Finset ι} {χ : ι → DirichletCharacter R N}
    (hcop : (s : Set ι).Pairwise fun i j ↦ (χ i).conductor.Coprime (χ j).conductor)
    (hlevel : s.Nonempty ∨ N ≠ 0) :
    (∏ i ∈ s, χ i).conductor = ∏ i ∈ s, (χ i).conductor := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : NeZero N := ⟨hlevel.resolve_left (by simp)⟩
    simp [conductor_one]
  | @insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp
    have hs := hcop.mono (by simp : (s : Set ι) ⊆ ↑(insert i s))
    have hc : (χ i).conductor.Coprime (∏ j ∈ s, (χ j).conductor) :=
      Nat.Coprime.prod_right fun j hj ↦ hcop (by simp) (by simp [hj])
        (by rintro rfl; exact hi hj)
    rw [Finset.prod_insert hi,
      conductor_mul_eq_mul_of_coprime (by rwa [ih hs (Or.inl hsne)]),
      ih hs (Or.inl hsne), Finset.prod_insert hi]

end TauCeti
