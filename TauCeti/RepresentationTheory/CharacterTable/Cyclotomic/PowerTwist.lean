/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.RepresentationTheory.CharacterTable.Cyclotomic.Action

/-!
# Power-map twists of irreducible characters

For a finite group `G` and `j` coprime to `|G|`, the function `χ^{(j)} : g ↦ χ(g ^ j)` is an
irreducible character whenever `χ` is (`TauCeti.pow_mem_irreducibleCharacters`), over any
algebraically closed field of characteristic zero. It is the image of `χ` under the
cyclotomic Galois action of the automorphism `ζ ↦ ζ ^ j` of the `|G|`-th cyclotomic field,
embedded in the coefficient field.

## Main results

* `TauCeti.pow_mem_irreducibleCharacters`: `χ^{(j)}` is irreducible for `j` coprime to `|G|`.
-/

public section

open IntermediateField

namespace TauCeti

variable {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Finite G]

/-- **Power maps preserve irreducible characters.** For `j` coprime to `|G|`, the function
`g ↦ χ(g ^ j)` is an irreducible character of `G` whenever `χ` is. -/
theorem pow_mem_irreducibleCharacters {χ : G → k} (hχ : χ ∈ irreducibleCharacters k G) {j : ℕ}
    (hj : j.Coprime (Nat.card G)) : (fun g => χ (g ^ j)) ∈ irreducibleCharacters k G := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨ζ, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k (Nat.card G)
  have := hζ₀.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hζ := IsCyclotomicExtension.zeta_spec (Nat.card G) ℚ ℚ⟮ζ⟯
  have hG : Monoid.exponent G ∣ Nat.card G := Group.exponent_dvd_nat_card
  have hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos (Nat.card G))
  let σ := (IsCyclotomicExtension.autEquivPow ℚ⟮ζ⟯ hirr).symm (ZMod.unitOfCoprime j hj)
  have hσ : (hζ.autToPow ℚ σ : ZMod (Nat.card G)).val = j % Nat.card G := by
    rw [← IsCyclotomicExtension.autEquivPow_apply _ hirr, MulEquiv.apply_symm_apply,
      ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  convert (hζ.cyclotomicIrreducibleCharacterAction (L := k) hG σ ⟨χ, hχ⟩).property using 1
  funext g
  rw [IsPrimitiveRoot.cyclotomicIrreducibleCharacterAction_apply, hσ, pow_mod_natCard]

end TauCeti
