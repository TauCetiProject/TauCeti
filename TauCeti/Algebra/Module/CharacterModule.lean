/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule

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

/-- The canonical embedding of `AddCircle (1 : ℚ)` into `AddCircle (1 : ℝ)`. -/
private noncomputable def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (Rat.castHom ℝ).toAddMonoidHom)
    (fun x hx ↦ by
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        map_zsmul]
      have : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
          ((Rat.castHom ℝ).toAddMonoidHom (1 : ℚ)) = 0 := by
        simp only [RingHom.toAddMonoidHom_eq_coe]
        rw [QuotientAddGroup.coe_mk', QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
        exact ⟨1, by simp⟩
      rw [this, smul_zero])

private theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | H a =>
  induction b using QuotientAddGroup.induction_on with | H b =>
  have hdiff : ratAddCircleToReal (QuotientAddGroup.mk a - QuotientAddGroup.mk b) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hab
  rw [← QuotientAddGroup.mk_sub] at hdiff
  simp only [ratAddCircleToReal, QuotientAddGroup.lift_mk', AddMonoidHom.coe_comp,
    Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    QuotientAddGroup.coe_mk'] at hdiff
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff] at hdiff
  obtain ⟨n, hn⟩ := hdiff
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-n, ?_⟩
  rw [zsmul_eq_mul, mul_one] at hn ⊢
  have hn' : (n : ℝ) = ((a - b : ℚ) : ℝ) := hn
  have hn'' : (n : ℚ) = a - b := by exact_mod_cast hn'
  have : (-n : ℚ) = -a + b := by
    rw [hn'']
    ring
  exact this

/-- The injective map from `CharacterModule M` to `AddChar M Circle`. -/
private noncomputable def characterModuleToAddChar (M : Type*) [AddCommGroup M] :
    CharacterModule M → AddChar M Circle := fun c ↦
  { toFun := fun m ↦ AddCircle.toCircle (ratAddCircleToReal (c m))
    map_zero_eq_one' := by simp
    map_add_eq_mul' := fun x y ↦ by
      simp only [map_add, AddCircle.toCircle_add] }

private theorem characterModuleToAddChar_injective (M : Type*) [AddCommGroup M] :
    Function.Injective (characterModuleToAddChar M) := by
  intro c₁ c₂ h
  ext m
  have h_eq : AddCircle.toCircle (ratAddCircleToReal (c₁ m)) =
      AddCircle.toCircle (ratAddCircleToReal (c₂ m)) := by
    exact DFunLike.congr_fun h m
  have h_real := AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero h_eq
  exact ratAddCircleToReal_injective h_real

/-- The character module of a finite abelian group is finite. -/
instance (M : Type*) [AddCommGroup M] [Finite M] : Finite (CharacterModule M) := by
  have : Finite (AddChar M Circle) :=
    Finite.of_equiv (AddChar M ℂ) AddChar.circleEquivComplex.symm.toEquiv
  exact Finite.of_injective (characterModuleToAddChar M) (characterModuleToAddChar_injective M)

private theorem card_characterModule_le (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) ≤ Nat.card M := by
  cases nonempty_fintype M
  have : Fintype (AddChar M Circle) :=
    Fintype.ofEquiv (AddChar M ℂ) AddChar.circleEquivComplex.symm.toEquiv
  have : Fintype (CharacterModule M) := Fintype.ofFinite _
  have hle := Fintype.card_le_of_injective (characterModuleToAddChar M)
    (characterModuleToAddChar_injective M)
  have hequiv : Fintype.card (AddChar M Circle) = Fintype.card (AddChar M ℂ) :=
    Fintype.card_congr AddChar.circleEquivComplex.toEquiv
  rw [hequiv, AddChar.card_eq] at hle
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
@[simp high]
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
