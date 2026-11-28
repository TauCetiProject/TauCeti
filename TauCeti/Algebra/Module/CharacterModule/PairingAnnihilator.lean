/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.Module.CharacterModule

import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Annihilators of `ℚ/ℤ`-valued biadditive pairings

For a biadditive pairing `b : A →+ B →+ C` of abelian groups and an additive subgroup `L ≤ A`,
the annihilator `TauCeti.pairingAnnihilator b L` is the subgroup `{y : B | ∀ x ∈ L, b x y = 0}`.
When `C` is identified with `ℚ/ℤ` via `AddCircle (1 : ℚ) ≃+ C`, Pontryagin duality for finite
abelian groups (`TauCeti.natCard_characterModule`) yields the index divisibility between the right
and left kernels of a pairing and the annihilator cardinality identity
`#L^⊥ · #L = #B · #(b.ker ⊓ L)`.

## Main definitions and results

* `TauCeti.pairingAnnihilator`: the right annihilator subgroup of `L ≤ A` under `b : A →+ B →+ C`.
* `TauCeti.mem_pairingAnnihilator`: membership characterization of `pairingAnnihilator`.
* `TauCeti.index_ker_flip_dvd`: for `e : AddCircle (1 : ℚ) ≃+ C` and `β : A →+ B →+ C`,
  `β.flip.ker.index ∣ β.ker.index`.
* `TauCeti.natCard_pairingAnnihilator_mul_natCard`: for `e : AddCircle (1 : ℚ) ≃+ C`,
  `Nat.card (pairingAnnihilator b L) * Nat.card L = Nat.card B * Nat.card ↥(b.ker ⊓ L)`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, file
  `src/Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean` (declarations
  `pairingAnnihilator`, `index_ker_flip_dvd`, `card_pairingAnnihilator_mul_card`); Apache 2.0,
  Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- For a biadditive pairing `b : A →+ B →+ C` and a subgroup `L` of `A`, the right annihilator
subgroup `{y : B | ∀ x ∈ L, b x y = 0}`. -/
def pairingAnnihilator (b : A →+ B →+ C) (L : AddSubgroup A) : AddSubgroup B :=
  (b.comp L.subtype).flip.ker.copy {y : B | ∀ x ∈ L, b x y = 0} <| by
    ext y
    simp [AddMonoidHom.ext_iff]

/-- An element `y : B` lies in `pairingAnnihilator b L` iff `b x y = 0` for all `x ∈ L`. -/
@[simp]
theorem mem_pairingAnnihilator {b : A →+ B →+ C} {L : AddSubgroup A} {y : B} :
    y ∈ pairingAnnihilator b L ↔ ∀ x ∈ L, b x y = 0 :=
  Iff.rfl

/-- For a biadditive pairing `β : A →+ B →+ C` with `AddCircle (1 : ℚ) ≃+ C`, the index in `B` of
the right kernel divides the index in `A` of the left kernel. -/
theorem index_ker_flip_dvd (e : AddCircle (1 : ℚ) ≃+ C) (β : A →+ B →+ C) :
    β.flip.ker.index ∣ β.ker.index := by
  by_cases h_fin : Finite (A ⧸ β.ker)
  · let f : B →+ CharacterModule (A ⧸ β.ker) :=
      (QuotientAddGroup.kerLift β).flip.compr₂ e.symm.toAddMonoidHom
    have h_ker_le : f.ker ≤ β.flip.ker := by
      intro y hy
      rw [AddMonoidHom.mem_ker] at hy ⊢
      ext x
      have hx : f y (QuotientAddGroup.mk x) = 0 :=
        DFunLike.congr_fun hy (QuotientAddGroup.mk x)
      exact (map_eq_zero_iff e.symm e.symm.injective).mp hx
    calc
      β.flip.ker.index ∣ f.ker.index := AddSubgroup.index_dvd_of_le h_ker_le
      _ ∣ Nat.card (CharacterModule (A ⧸ β.ker)) :=
        AddSubgroup.card_dvd_of_injective (QuotientAddGroup.kerLift f)
          (QuotientAddGroup.kerLift_injective f)
      _ = β.ker.index := by
        rw [natCard_characterModule, AddSubgroup.index]
  · rw [AddSubgroup.index_eq_zero_iff_infinite.mpr (not_finite_iff_infinite.mp h_fin)]
    exact dvd_zero _

/-- For a biadditive pairing `b : A →+ B →+ C` with `AddCircle (1 : ℚ) ≃+ C` and
`L : AddSubgroup A`, `#L^⊥ · #L = #B · #(b.ker ⊓ L)` (with `Nat.card = 0` for infinite groups). -/
theorem natCard_pairingAnnihilator_mul_natCard (b : A →+ B →+ C) (e : AddCircle (1 : ℚ) ≃+ C)
    (L : AddSubgroup A) :
    Nat.card (pairingAnnihilator b L) * Nat.card L = Nat.card B * Nat.card ↥(b.ker ⊓ L) := by
  let β : L →+ B →+ C := b.comp L.subtype
  have h_index : β.flip.ker.index = b.ker.relIndex L :=
    dvd_antisymm (index_ker_flip_dvd e β) (index_ker_flip_dvd e β.flip)
  have h_left : Nat.card ↥(b.ker ⊓ L) * b.ker.relIndex L = Nat.card L := by
    simpa only [bot_inf_eq, AddSubgroup.relIndex_bot_left] using
      AddSubgroup.relIndex_inf_mul_relIndex (⊥ : AddSubgroup A) b.ker L
  rw [show pairingAnnihilator b L = β.flip.ker from β.flip.ker.copy_eq _ _, ← h_left,
    ← β.flip.ker.card_mul_index, h_index]
  ring

end TauCeti
