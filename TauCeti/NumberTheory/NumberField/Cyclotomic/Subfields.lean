/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Subgroups
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.NormNum.Prime

/-!
# The subfields of the fifth cyclotomic field

The fifth cyclotomic field has exactly three intermediate fields over `ℚ`. The unique middle
field has degree two and is fixed by the automorphisms whose cyclotomic exponents are `±1`.
The calculation uses the Galois correspondence and Mathlib's isomorphism from its Galois group
to `(ZMod 5)ˣ`.

The middle field is specified intrinsically as a fixed field, so the result applies to every
model of the fifth cyclotomic field.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 1.
-/

public section

open IntermediateField IsCyclotomicExtension.Rat
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

private theorem card_gal_five : Nat.card (Gal(K/ℚ)) = 4 := by
  rw [Nat.card_congr (galEquivZMod 5 K).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime (by norm_num : Nat.Prime 5)]

private noncomputable def orderTwoSubgroup : Subgroup (Gal(K/ℚ)) :=
  Subgroup.zpowers ((galEquivZMod 5 K).symm (-1 : (ZMod 5)ˣ))

private theorem card_orderTwoSubgroup : Nat.card (orderTwoSubgroup (K := K)) = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [orderTwoSubgroup, Nat.card_zpowers, MulEquiv.orderOf_eq, ← orderOf_units,
    Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod 5) 5, ite_eq_right (by norm_num)]

/-- The unique quadratic intermediate field of the fifth cyclotomic field, defined as the fixed
field of the order-two subgroup with cyclotomic exponents `±1`. -/
noncomputable def fifthCyclotomicQuadraticSubfield : IntermediateField ℚ K :=
  fixedField (Subgroup.zpowers ((galEquivZMod 5 K).symm (-1 : (ZMod 5)ˣ)))

/-- An element lies in the quadratic subfield exactly when the automorphism with cyclotomic
exponent `-1` fixes it. -/
@[simp]
theorem mem_fifthCyclotomicQuadraticSubfield_iff (x : K) :
    x ∈ fifthCyclotomicQuadraticSubfield ↔
      ((galEquivZMod 5 K).symm (-1 : (ZMod 5)ˣ)) x = x := by
  let κ := (galEquivZMod 5 K).symm (-1 : (ZMod 5)ˣ)
  -- Keep `galEquivZMod` opaque: rewriting the two local definitions unfolds its equivalence.
  change x ∈ fixedField (Subgroup.zpowers κ) ↔ κ x = x
  rw [mem_fixedField_iff]
  constructor
  · intro hx
    exact hx κ (Subgroup.mem_zpowers κ)
  · intro hx σ hσ
    have hκ : κ ∈ MulAction.stabilizer (Gal(K/ℚ)) x := by
      simpa [MulAction.mem_stabilizer_iff] using hx
    have hle := Subgroup.zpowers_le_of_mem hκ
    have hs := hle hσ
    simpa [MulAction.mem_stabilizer_iff] using hs

/-- The middle field of a fifth cyclotomic field has degree two over `ℚ`. -/
@[simp]
theorem finrank_fifthCyclotomicQuadraticSubfield :
    Module.finrank ℚ (fifthCyclotomicQuadraticSubfield (K := K)) = 2 := by
  have hrel : Module.finrank (fifthCyclotomicQuadraticSubfield (K := K)) K = 2 :=
    (IntermediateField.finrank_fixedField_eq_card (orderTwoSubgroup (K := K))).trans
      (card_orderTwoSubgroup (K := K))
  have htot : Module.finrank ℚ K = 4 := by
    rw [IsCyclotomicExtension.Rat.finrank 5 K,
      Nat.totient_prime (by norm_num : Nat.Prime 5)]
  have htower := Module.finrank_mul_finrank ℚ
    (fifthCyclotomicQuadraticSubfield (K := K)) K
  rw [hrel, htot] at htower
  omega

/-- There are exactly three subfields of the fifth cyclotomic field over `ℚ`. -/
@[simp]
theorem card_intermediateField_fifthCyclotomic :
    Nat.card (IntermediateField ℚ K) = 3 := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {5} ℚ K
  have : IsCyclic (ZMod 5)ˣ := ZMod.isCyclic_units_prime (by norm_num : Nat.Prime 5)
  calc
    Nat.card (IntermediateField ℚ K) = Nat.card ((Subgroup (Gal(K/ℚ)))ᵒᵈ) :=
      Nat.card_congr IsGalois.intermediateFieldEquivSubgroup.toEquiv
    _ = Nat.card (Subgroup (Gal(K/ℚ))) := rfl
    _ = Nat.card (Subgroup (ZMod 5)ˣ) :=
      Nat.card_congr (galEquivZMod 5 K).mapSubgroup.toEquiv
    _ = 3 := card_subgroups_of_card_eq_four (by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime (by norm_num : Nat.Prime 5)])

end TauCeti.NumberField

namespace IntermediateField

open TauCeti TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

/-- Every subfield of a fifth cyclotomic field is the base field, the unique quadratic subfield,
or the full field. -/
theorem eq_bot_or_eq_fifthCyclotomicQuadraticSubfield_or_eq_top
    (F : IntermediateField ℚ K) :
    F = ⊥ ∨ F = fifthCyclotomicQuadraticSubfield ∨ F = ⊤ := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {5} ℚ K
  have : IsCyclic (ZMod 5)ˣ := ZMod.isCyclic_units_prime (by norm_num : Nat.Prime 5)
  have : IsCyclic (Gal(K/ℚ)) :=
    isCyclic_of_injective (galEquivZMod 5 K).toMonoidHom (galEquivZMod 5 K).injective
  rcases subgroup_eq_bot_or_eq_or_eq_top_of_card_eq_two (card_gal_five (K := K))
      (orderTwoSubgroup (K := K)) (card_orderTwoSubgroup (K := K)) F.fixingSubgroup with h | h | h
  · right; right
    rw [← IsGalois.fixedField_fixingSubgroup F, h, fixedField_bot]
  · right; left
    rw [← IsGalois.fixedField_fixingSubgroup F, h, orderTwoSubgroup,
      fifthCyclotomicQuadraticSubfield]
  · left
    rw [← IsGalois.fixedField_fixingSubgroup F, h, IsGalois.fixedField_top]

/-- The middle field is the only degree-two subfield of a fifth cyclotomic field. -/
theorem eq_fifthCyclotomicQuadraticSubfield_of_finrank_eq_two
    (F : IntermediateField ℚ K) (hF : Module.finrank ℚ F = 2) :
    F = fifthCyclotomicQuadraticSubfield := by
  rcases F.eq_bot_or_eq_fifthCyclotomicQuadraticSubfield_or_eq_top with h | h | h
  · rw [h, IntermediateField.finrank_bot] at hF
    omega
  · exact h
  · rw [h, IntermediateField.finrank_top', IsCyclotomicExtension.Rat.finrank 5 K,
      Nat.totient_prime (by norm_num : Nat.Prime 5)] at hF
    omega

end IntermediateField
