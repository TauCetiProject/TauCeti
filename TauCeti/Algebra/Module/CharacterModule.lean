/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.Circle

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Character modules of finite abelian groups

The characters `CharacterModule M = M →+ AddCircle (1 : ℚ)` of an abelian group `M` separate its
points, and when `M` is finite its character module is finite with as many elements as `M`:

* `TauCeti.CharacterModule.eval_injective`: evaluation embeds `M` in its double character module;
* an instance `Finite (CharacterModule M)` for finite `M`;
* `TauCeti.natCard_characterModule`: `Nat.card (CharacterModule M) = Nat.card M`.
-/

public section

namespace TauCeti

/-- The character module of a finite abelian group is finite. -/
instance (M : Type*) [AddCommGroup M] [Finite M] : Finite (CharacterModule M) :=
  Finite.of_injective (fun c : CharacterModule M ↦ expCircle.compAddMonoidHom c)
    (expCircle.compAddMonoidHom_injective_right (AddChar.injective_iff.2
      fun _ hx ↦ expCircle_eq_one_iff.mp hx))

private theorem card_characterModule_le (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) ≤ Nat.card M := by
  cases nonempty_fintype M
  have : Fintype (CharacterModule M) := Fintype.ofFinite _
  have hle := Fintype.card_le_of_injective
    (fun c : CharacterModule M ↦ expCircle.compAddMonoidHom c)
    (expCircle.compAddMonoidHom_injective_right (AddChar.injective_iff.2
      fun _ hx ↦ expCircle_eq_one_iff.mp hx))
  rw [AddChar.card_eq] at hle
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hle

/-- Evaluation `m ↦ (c ↦ c m)`, Mathlib's `AddMonoidHom.eval`, embeds an abelian group in its
double character module: the characters of `M` separate its points. -/
theorem CharacterModule.eval_injective (M : Type*) [AddCommGroup M] :
    Function.Injective (AddMonoidHom.eval : M →+ CharacterModule (CharacterModule M)) := by
  intro x y hxy
  have h : ∀ c : CharacterModule M, c (x - y) = 0 := fun c ↦ by
    have hc : c x = c y := DFunLike.congr_fun hxy c
    rw [map_sub, hc, sub_self]
  exact sub_eq_zero.mp (CharacterModule.eq_zero_of_character_apply h)

/-- The cardinality of the character module equals the cardinality of the group. -/
@[simp]
theorem natCard_characterModule (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) = Nat.card M := by
  cases nonempty_fintype M
  have : Fintype (CharacterModule M) := Fintype.ofFinite _
  have : Fintype (CharacterModule (CharacterModule M)) := Fintype.ofFinite _
  have h1 : Fintype.card M ≤ Fintype.card (CharacterModule (CharacterModule M)) :=
    Fintype.card_le_of_injective _ (CharacterModule.eval_injective M)
  have h2 : Fintype.card (CharacterModule (CharacterModule M)) ≤
      Fintype.card (CharacterModule M) := by
    have hle := card_characterModule_le (CharacterModule M)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hle
  have h3 : Fintype.card (CharacterModule M) ≤ Fintype.card M := by
    have hle := card_characterModule_le M
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hle
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact le_antisymm h3 (h1.trans h2)

end TauCeti
