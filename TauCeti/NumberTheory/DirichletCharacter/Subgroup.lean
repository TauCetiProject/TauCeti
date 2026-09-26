/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.NumberTheory.DirichletCharacter.Conductor

/-!
# Conductors of groups of Dirichlet characters

The conductor of a finite group of Dirichlet characters is the least common multiple of the
conductors of its members. At a nonzero original level, its divisibility characterization says
that among divisors of the original level it is the least level, in the divisibility order, through
which every character in the group factors.

This file provides the divisibility characterization of the group conductor, its monotonicity,
its value on a cyclic character group, and its invariance under an injective change of coefficient
ring. The last result lets integer-valued quadratic character groups be used inside the
complex-valued character correspondence for cyclotomic fields.

## Main results

* `Subgroup.dirichletConductor_dvd_iff`: the group conductor divides `m` exactly when every
  member's conductor divides `m`.
* `Subgroup.dirichletConductor_dvd_iff_forall_factorsThrough`: at a divisor of the original level,
  this means that every member factors through that level.
* `Subgroup.dirichletConductor_sup`: the conductor of the supremum of two finite character groups
  is the least common multiple of their conductors.
* `Subgroup.dirichletConductor_closure_singleton`: a cyclic character group has the conductor of
  its generator.
* `Subgroup.dirichletConductor_map_ringHomComp`: injectively changing the coefficient ring
  preserves the group conductor.
-/

public section

namespace Subgroup

open DirichletCharacter

section Basic

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ}

/-- The conductor of a subgroup of Dirichlet characters: the least common multiple of the
conductors of all its members. -/
noncomputable def dirichletConductor (Y : Subgroup (DirichletCharacter R n)) [Finite Y] : ℕ := by
  letI : Fintype Y := Fintype.ofFinite Y
  exact Finset.lcm Finset.univ fun χ : Y ↦ conductor χ.1

/-- The conductor of every character in a subgroup divides the subgroup conductor. -/
theorem conductor_dvd_dirichletConductor (Y : Subgroup (DirichletCharacter R n))
    [Finite Y] {χ : DirichletCharacter R n} (hχ : χ ∈ Y) : conductor χ ∣ Y.dirichletConductor := by
  let _ : Fintype Y := Fintype.ofFinite Y
  exact Finset.dvd_lcm (f := fun ψ : Y ↦ conductor ψ.1) (Finset.mem_univ ⟨χ, hχ⟩)

/-- A subgroup conductor divides `m` exactly when every character in the subgroup has conductor
dividing `m`. -/
@[simp]
theorem dirichletConductor_dvd_iff (Y : Subgroup (DirichletCharacter R n)) [Finite Y] {m : ℕ} :
    Y.dirichletConductor ∣ m ↔ ∀ χ ∈ Y, conductor χ ∣ m := by
  let _ : Fintype Y := Fintype.ofFinite Y
  simp only [dirichletConductor, Finset.lcm_dvd_iff, Finset.mem_univ, forall_const,
    Subtype.forall]

/-- The conductor of a subgroup of level-`n` characters divides `n`. -/
theorem dirichletConductor_dvd_level
    (Y : Subgroup (DirichletCharacter R n)) [Finite Y] : Y.dirichletConductor ∣ n :=
  Y.dirichletConductor_dvd_iff.mpr fun χ _ ↦ χ.conductor_dvd_level

/-- The conductor of a subgroup at a nonzero level is nonzero. -/
theorem dirichletConductor_ne_zero [NeZero n]
    (Y : Subgroup (DirichletCharacter R n)) [Finite Y] : Y.dirichletConductor ≠ 0 := by
  intro h
  exact NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ Y.dirichletConductor_dvd_level))

/-- If `m` divides the original level, the subgroup conductor divides `m` exactly when every
character in the subgroup factors through level `m`. -/
theorem dirichletConductor_dvd_iff_forall_factorsThrough [NeZero n]
    (Y : Subgroup (DirichletCharacter R n)) [Finite Y] {m : ℕ} (hmn : m ∣ n) :
    Y.dirichletConductor ∣ m ↔ ∀ χ ∈ Y, FactorsThrough χ m := by
  rw [dirichletConductor_dvd_iff]
  exact forall_congr' fun χ ↦ forall_congr' fun _ ↦
    (mem_conductorSet_iff_conductor_dvd χ hmn).symm

/-- Group conductors are monotone for subgroup inclusion, in the divisibility order. -/
theorem dirichletConductor_dvd_of_le {Y Z : Subgroup (DirichletCharacter R n)}
    [Finite Y] [Finite Z] (hYZ : Y ≤ Z) :
    Y.dirichletConductor ∣ Z.dirichletConductor :=
  Y.dirichletConductor_dvd_iff.mpr fun _ hχ ↦ Z.conductor_dvd_dirichletConductor (hYZ hχ)

local instance finite_sup {Y Z : Subgroup (DirichletCharacter R n)}
    [Finite Y] [Finite Z] : Finite ↥(Y ⊔ Z) := by
  let f : Y × Z → ↥(Y ⊔ Z) := fun ⟨⟨χ, hχ⟩, ⟨ψ, hψ⟩⟩ ↦
    ⟨χ * ψ, mul_mem (le_sup_left (a := Y) hχ) (le_sup_right (a := Y) hψ)⟩
  exact Finite.of_surjective f fun ⟨χ, hχ⟩ ↦ by
    obtain ⟨ψ, hψ, ξ, hξ, rfl⟩ := Subgroup.mem_sup.mp hχ
    exact ⟨⟨⟨ψ, hψ⟩, ⟨ξ, hξ⟩⟩, rfl⟩

/-- The conductor of the supremum of two finite character groups is the least common multiple of
their conductors. -/
@[simp]
theorem dirichletConductor_sup (Y Z : Subgroup (DirichletCharacter R n))
    [Finite Y] [Finite Z] :
    (Y ⊔ Z).dirichletConductor = Nat.lcm Y.dirichletConductor Z.dirichletConductor := by
  apply Nat.dvd_antisymm
  · rw [dirichletConductor_dvd_iff]
    intro χ hχ
    obtain ⟨ψ, hψ, ξ, hξ, rfl⟩ := Subgroup.mem_sup.mp hχ
    exact (conductor_mul_dvd_lcm_conductor ψ ξ).trans (Nat.lcm_dvd_iff.mpr
      ⟨(Y.conductor_dvd_dirichletConductor hψ).trans (Nat.dvd_lcm_left _ _),
        (Z.conductor_dvd_dirichletConductor hξ).trans (Nat.dvd_lcm_right _ _)⟩)
  · rw [Nat.lcm_dvd_iff]
    exact ⟨dirichletConductor_dvd_of_le le_sup_left,
      dirichletConductor_dvd_of_le le_sup_right⟩

/-- The trivial character group has conductor one. -/
@[simp]
theorem dirichletConductor_bot [NeZero n] :
    dirichletConductor (⊥ : Subgroup (DirichletCharacter R n)) = 1 := by
  apply Nat.dvd_antisymm
  · rw [dirichletConductor_dvd_iff]
    intro χ hχ
    rw [Subgroup.mem_bot] at hχ
    simpa [hχ] using conductor_one (R := R) (n := n)
  · exact one_dvd _

local instance finite_closure_singleton {χ : DirichletCharacter R n} :
    Finite ↥(closure {χ}) := by
  rw [← Subgroup.zpowers_eq_closure χ]
  exact Set.finite_coe_iff.mpr
    ((orderOf_pos_iff.mp (MulChar.orderOf_pos χ)).finite_zpowers)

/-- The subgroup generated by one Dirichlet character has the conductor of that character. -/
@[simp]
theorem dirichletConductor_closure_singleton (χ : DirichletCharacter R n) :
    dirichletConductor (closure {χ}) = conductor χ := by
  apply Nat.dvd_antisymm
  · rw [dirichletConductor_dvd_iff]
    intro ψ hψ
    obtain ⟨k, rfl⟩ := Subgroup.mem_closure_singleton.mp hψ
    exact conductor_zpow_dvd χ k
  · exact conductor_dvd_dirichletConductor _ (Subgroup.mem_closure_singleton_self χ)

end Basic

section RingHom

variable {R R' : Type*} [CommRing R] [CommRing R'] {n : ℕ} [NeZero n]

local instance finite_map {Y : Subgroup (DirichletCharacter R n)} [Finite Y]
    {f : R →+* R'} : Finite ↥(Y.map (MulChar.ringHomCompHom f)) := by
  let g : Y → ↥(Y.map (MulChar.ringHomCompHom f)) := fun ⟨χ, hχ⟩ ↦
    ⟨MulChar.ringHomCompHom f χ, Subgroup.mem_map_of_mem _ hχ⟩
  exact Finite.of_surjective g fun ⟨ψ, hψ⟩ ↦ by
    obtain ⟨χ, hχ, rfl⟩ := hψ
    exact ⟨⟨χ, hχ⟩, rfl⟩

/-- An injective change of coefficient ring preserves the conductor of a character subgroup. -/
theorem dirichletConductor_map_ringHomComp (Y : Subgroup (DirichletCharacter R n))
    [Finite Y] (f : R →+* R') (hf : Function.Injective f) :
    (Y.map (MulChar.ringHomCompHom f)).dirichletConductor = Y.dirichletConductor := by
  apply Nat.dvd_antisymm
  · rw [dirichletConductor_dvd_iff]
    intro ψ hψ
    obtain ⟨χ, hχ, rfl⟩ := hψ
    simpa only [MulChar.ringHomCompHom_apply,
      DirichletCharacter.conductor_ringHomComp χ f hf] using
      Y.conductor_dvd_dirichletConductor hχ
  · rw [dirichletConductor_dvd_iff]
    intro χ hχ
    have h := (Y.map (MulChar.ringHomCompHom f)).conductor_dvd_dirichletConductor
      (Subgroup.mem_map_of_mem (MulChar.ringHomCompHom f) hχ)
    simpa only [MulChar.ringHomCompHom_apply,
      DirichletCharacter.conductor_ringHomComp χ f hf] using h

end RingHom

end Subgroup
