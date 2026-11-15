/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Dirichlet character conductors

Inversion preserves primitivity, and a primitive character is trivial exactly at level one. A
change of coefficient ring that is injective on the range of a Dirichlet character (in particular,
any ring homomorphism into a ring with `2 ≠ 0` on a quadratic character) preserves factorization
through a lower level, hence the conductor and primitivity of the character. The conductor of a
product of Dirichlet characters with pairwise coprime conductors is the product of their conductors.
-/

public section

namespace DirichletCharacter

/-- A primitive character is principal exactly when its level is one. -/
theorem IsPrimitive.eq_one_iff {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter R n} (hχ : χ.IsPrimitive) : χ = 1 ↔ n = 1 := by
  rw [eq_one_iff_conductor_eq_one, (isPrimitive_def _).mp hχ]

/-! ### Changes of the coefficient ring -/

/-- Factoring a Dirichlet character through a lower level is unchanged by a change of coefficient
ring that is injective on the character's range. -/
theorem factorsThrough_ringHomComp_iff {R R' : Type*} [CommRing R] [CommRing R']
    {n d : ℕ} [NeZero n] (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Set.InjOn f (Set.range χ)) :
    FactorsThrough (χ.ringHomComp f) d ↔ FactorsThrough χ d := by
  by_cases hd : d ∣ n
  · rw [factorsThrough_iff_ker_unitsMap hd, factorsThrough_iff_ker_unitsMap hd]
    suffices (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker by rw [this]
    ext u
    have h1 : f (χ u) = 1 ↔ χ u = 1 := by
      simpa only [map_one] using hf.eq_iff (x := χ u) (y := 1) ⟨u, rfl⟩ ⟨1, map_one χ⟩
    simp [Units.ext_iff, h1]
  · exact iff_of_false (mt FactorsThrough.dvd hd) (mt FactorsThrough.dvd hd)

/-- A change of coefficient ring that is injective on the character's range preserves the conductor
of a Dirichlet character. -/
theorem conductor_ringHomComp {R R' : Type*} [CommRing R] [CommRing R']
    {n : ℕ} (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Set.InjOn f (Set.range χ)) : conductor (χ.ringHomComp f) = conductor χ := by
  obtain rfl | _ := eq_zero_or_neZero n
  · simp only [conductor_eq_zero_iff_level_eq_zero.mpr]
  exact congrArg sInf (Set.ext fun _ ↦ factorsThrough_ringHomComp_iff χ f hf)

/-- A change of coefficient ring that is injective on the character's range preserves primitivity
of a Dirichlet character. -/
theorem isPrimitive_ringHomComp_iff {R R' : Type*} [CommRing R] [CommRing R']
    {n : ℕ} (χ : DirichletCharacter R n) (f : R →+* R')
    (hf : Set.InjOn f (Set.range χ)) : IsPrimitive (χ.ringHomComp f) ↔ IsPrimitive χ := by
  rw [isPrimitive_def, isPrimitive_def, conductor_ringHomComp χ f hf]

/-- For a quadratic Dirichlet character and a ring homomorphism into a ring where `2 ≠ 0`,
factoring through a lower level is unchanged by `ringHomComp`. -/
theorem _root_.MulChar.IsQuadratic.factorsThrough_ringHomComp_iff {R R' : Type*} [CommRing R]
    [CommRing R'] [NeZero (2 : R')] {n d : ℕ} [NeZero n] {χ : DirichletCharacter R n}
    (hχ : χ.IsQuadratic) (f : R →+* R') :
    FactorsThrough (χ.ringHomComp f) d ↔ FactorsThrough χ d :=
  DirichletCharacter.factorsThrough_ringHomComp_iff χ f (hχ.injOn_range f)

/-- Pushing a quadratic Dirichlet character along any ring homomorphism into a ring where `2 ≠ 0`
preserves its conductor. -/
theorem _root_.MulChar.IsQuadratic.conductor_ringHomComp {R R' : Type*} [CommRing R]
    [CommRing R'] [NeZero (2 : R')] {n : ℕ} {χ : DirichletCharacter R n} (hχ : χ.IsQuadratic)
    (f : R →+* R') : conductor (χ.ringHomComp f) = conductor χ :=
  DirichletCharacter.conductor_ringHomComp χ f (hχ.injOn_range f)

/-- Pushing a quadratic Dirichlet character along any ring homomorphism into a ring where `2 ≠ 0`
preserves primitivity. -/
theorem _root_.MulChar.IsQuadratic.isPrimitive_ringHomComp_iff {R R' : Type*} [CommRing R]
    [CommRing R'] [NeZero (2 : R')] {n : ℕ} {χ : DirichletCharacter R n} (hχ : χ.IsQuadratic)
    (f : R →+* R') : IsPrimitive (χ.ringHomComp f) ↔ IsPrimitive χ :=
  DirichletCharacter.isPrimitive_ringHomComp_iff χ f (hχ.injOn_range f)

/-! ### Products with coprime conductors -/

/-- The conductor of a product of two Dirichlet characters with coprime conductors is the product
of their conductors. -/
theorem conductor_mul_of_coprime {R : Type*} [CommMonoidWithZero R] {N : ℕ}
    {χ ψ : DirichletCharacter R N} (hcop : χ.conductor.Coprime ψ.conductor) :
    (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  -- Each factor's conductor divides that of the product, since `χ = (χ * ψ) * ψ⁻¹`.
  have key {χ ψ : DirichletCharacter R N} (h : χ.conductor.Coprime ψ.conductor) :
      χ.conductor ∣ (χ * ψ).conductor := by
    refine h.dvd_of_dvd_mul_right ?_
    simpa only [mul_inv_cancel_right, conductor_inv] using
      (conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹).trans (Nat.lcm_dvd_mul _ _)
  refine Nat.dvd_antisymm ((conductor_mul_dvd_lcm_conductor χ ψ).trans (Nat.lcm_dvd_mul _ _)) ?_
  exact hcop.mul_dvd_of_dvd_of_dvd (key hcop) (mul_comm ψ χ ▸ key hcop.symm)

/-- The conductor of a finite product of Dirichlet characters with pairwise coprime conductors is
the product of their conductors, provided the index set is nonempty or the level is nonzero. -/
theorem conductor_prod_of_pairwise_coprime {R ι : Type*} [CommMonoidWithZero R]
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
    have ih := ih (hcop.mono (by simp)) (Or.inl hsne)
    have hc : (χ i).conductor.Coprime (∏ j ∈ s, (χ j).conductor) :=
      Nat.Coprime.prod_right fun j hj ↦ hcop (by simp) (by simp [hj])
        (ne_of_mem_of_not_mem hj hi).symm
    rw [Finset.prod_insert hi, conductor_mul_of_coprime (ih ▸ hc), ih, Finset.prod_insert hi]

end DirichletCharacter
