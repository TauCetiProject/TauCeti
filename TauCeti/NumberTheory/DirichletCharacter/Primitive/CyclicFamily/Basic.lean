/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Cyclic families of primitive Dirichlet characters

The cyclic family of a primitive character consists of the primitive sources of its powers.
Even though a power can have smaller conductor than the generator, different powers at the
original level have different primitive sources: lifting back to that level recovers the power.
This lets one index a sum over the family by exponents modulo the order of the generator.

The family is the one in Levent Alpöge's formalization of the Riemann hypothesis for
Dirichlet L-functions (`Formalism.HC.Level.cyc` and `Formalism.HC.Level.ofSub`, in
`ExplicitFormulaErrorOfHostConditions.lean` in the [published source][alpoege-rh]).

[alpoege-rh]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open DirichletCharacter

namespace TauCeti.PrimitiveDirichletCharacter

open scoped Classical in
/-- The cyclic family of `ψ`: the primitive sources of the powers of `ψ.character`. -/
noncomputable def cyclicFamily (ψ : PrimitiveDirichletCharacter) :
    Finset PrimitiveDirichletCharacter :=
  (Finset.range (orderOf ψ.character)).image fun l ↦ of (ψ.character ^ l)

open scoped Classical in
/-- The cyclic family as the image of the standard range of exponents. -/
theorem cyclicFamily_def (ψ : PrimitiveDirichletCharacter) :
    ψ.cyclicFamily = (Finset.range (orderOf ψ.character)).image (fun l ↦ of (ψ.character ^ l)) :=
  (rfl)

variable {ψ κ : PrimitiveDirichletCharacter}

/-- Membership in the cyclic family, with the exponent chosen in its standard range. -/
theorem mem_cyclicFamily_iff :
    κ ∈ ψ.cyclicFamily ↔ ∃ l < orderOf ψ.character, of (ψ.character ^ l) = κ := by
  simp only [cyclicFamily_def, Finset.mem_image, Finset.mem_range]

/-- The primitive source of any integer power belongs to the cyclic family. -/
@[simp]
theorem of_zpow_mem_cyclicFamily (ψ : PrimitiveDirichletCharacter) (l : ℤ) :
    of (ψ.character ^ l) ∈ ψ.cyclicFamily := by
  classical
  have hl : ψ.character ^ l ∈ Subgroup.zpowers ψ.character := Subgroup.zpow_mem_zpowers _ _
  obtain ⟨n, hn, hn'⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hl)
  exact mem_cyclicFamily_iff.mpr ⟨n, Finset.mem_range.mp hn, congrArg of hn'⟩

/-- Membership in the cyclic family is equivalent to being the primitive source of a power. -/
theorem mem_cyclicFamily_iff_exists_zpow :
    κ ∈ ψ.cyclicFamily ↔ ∃ l : ℤ, of (ψ.character ^ l) = κ := by
  constructor
  · intro h
    obtain ⟨l, -, rfl⟩ := mem_cyclicFamily_iff.mp h
    exact ⟨l, by rw [zpow_natCast]⟩
  · rintro ⟨l, rfl⟩
    exact of_zpow_mem_cyclicFamily ψ l

/-- The primitive source of any natural power belongs to the cyclic family. -/
@[simp]
theorem of_pow_mem_cyclicFamily (ψ : PrimitiveDirichletCharacter) (l : ℕ) :
    of (ψ.character ^ l) ∈ ψ.cyclicFamily := by
  simpa only [zpow_natCast] using of_zpow_mem_cyclicFamily ψ (l : ℤ)

/-- The trivial character belongs to every cyclic family. -/
@[simp]
theorem one_mem_cyclicFamily (ψ : PrimitiveDirichletCharacter) : 1 ∈ ψ.cyclicFamily := by
  simpa using of_pow_mem_cyclicFamily ψ 0

/-- The generator belongs to its own cyclic family. -/
@[simp]
theorem mem_cyclicFamily_self (ψ : PrimitiveDirichletCharacter) : ψ ∈ ψ.cyclicFamily := by
  simpa using of_pow_mem_cyclicFamily ψ 1

/-- The cyclic family of the trivial character has just one member. -/
@[simp]
theorem cyclicFamily_one : (1 : PrimitiveDirichletCharacter).cyclicFamily = {1} := by
  classical
  ext κ
  simp [mem_cyclicFamily_iff_exists_zpow, eq_comm]

/-- Inversion preserves membership in a cyclic family. -/
@[simp]
theorem inv_mem_cyclicFamily : κ⁻¹ ∈ ψ.cyclicFamily ↔ κ ∈ ψ.cyclicFamily := by
  have h {η : PrimitiveDirichletCharacter} (hη : η ∈ ψ.cyclicFamily) :
      η⁻¹ ∈ ψ.cyclicFamily := by
    obtain ⟨l, rfl⟩ := mem_cyclicFamily_iff_exists_zpow.mp hη
    simpa only [zpow_neg, of_inv] using of_zpow_mem_cyclicFamily ψ (-l)
  exact ⟨fun hκ ↦ by simpa only [inv_inv] using h hκ, h⟩

/-- The conductor of every member divides the conductor of the generator. -/
theorem level_dvd_of_mem_cyclicFamily (h : κ ∈ ψ.cyclicFamily) :
    (κ.level : ℕ) ∣ (ψ.level : ℕ) := by
  obtain ⟨l, -, rfl⟩ := mem_cyclicFamily_iff.mp h
  exact level_of_dvd _

/-- Exponents modulo the order of `ψ.character` index its cyclic family without repetition. -/
noncomputable def cyclicFamilyEquiv (ψ : PrimitiveDirichletCharacter) :
    ZMod (orderOf ψ.character) ≃ ↥ψ.cyclicFamily := by
  haveI : NeZero (orderOf ψ.character) := ⟨(orderOf_pos _).ne'⟩
  refine Equiv.ofBijective (fun l ↦ ⟨of (ψ.character ^ l.val), of_pow_mem_cyclicFamily ψ l.val⟩)
    ⟨?_, ?_⟩
  · intro l m hlm
    obtain ⟨_, heq⟩ := of_eq_iff.mp (congrArg Subtype.val hlm)
    rw [changeLevel_character_of] at heq
    exact ZMod.val_injective _ (pow_injOn_Iio_orderOf l.val_lt m.val_lt heq.symm)
  · rintro ⟨κ, hκ⟩
    obtain ⟨l, hl, heq⟩ := mem_cyclicFamily_iff.mp hκ
    exact ⟨l, Subtype.ext (by simpa only [ZMod.val_natCast_of_lt hl] using heq)⟩

/-- The member indexed by an exponent is the primitive source of the corresponding power. -/
@[simp]
theorem coe_cyclicFamilyEquiv_apply (ψ : PrimitiveDirichletCharacter)
    (l : ZMod (orderOf ψ.character)) :
    (ψ.cyclicFamilyEquiv l : PrimitiveDirichletCharacter) = of (ψ.character ^ l.val) :=
  (rfl)

/-- An integer exponent indexes the primitive source of that power, without taking a
representative explicitly. -/
@[simp]
theorem cyclicFamilyEquiv_intCast (ψ : PrimitiveDirichletCharacter) (l : ℤ) :
    ψ.cyclicFamilyEquiv (l : ZMod (orderOf ψ.character)) =
      ⟨of (ψ.character ^ l), of_zpow_mem_cyclicFamily ψ l⟩ := by
  have : NeZero (orderOf ψ.character) := ⟨(orderOf_pos _).ne'⟩
  apply Subtype.ext
  simp only [coe_cyclicFamilyEquiv_apply, ← zpow_natCast, ZMod.val_intCast, zpow_mod_orderOf]

/-- The cyclic family has as many members as the order of its generating character. -/
@[simp]
theorem card_cyclicFamily (ψ : PrimitiveDirichletCharacter) :
    ψ.cyclicFamily.card = orderOf ψ.character := by
  have : NeZero (orderOf ψ.character) := ⟨(orderOf_pos _).ne'⟩
  rw [← Fintype.card_coe, ← Fintype.card_congr ψ.cyclicFamilyEquiv, ZMod.card]

end TauCeti.PrimitiveDirichletCharacter
