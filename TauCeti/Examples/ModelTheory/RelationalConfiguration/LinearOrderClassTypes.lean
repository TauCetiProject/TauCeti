/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Examples: the coded linear orders meet uncountably many isomorphism classes

Adding the diagonal to the relation of a coded strict well-order gives a coded linear order. By
`exists_mem_wellOrderClass_type_eq`, every order type `β` with `ω ≤ β < ω₁` is the type of a coded
strict well-order on `ℕ`, and isomorphic codes with the diagonal added have strict parts of the
same type. So `β ↦` the class of the reflexive closure of a code of type `β` is injective on the
uncountable interval `[ω, ω₁)`, and `linearOrderClass` meets uncountably many classes of
`isoSetoid Language.order ℕ`.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration Set
open scoped Ordinal

namespace TauCeti.Examples.ModelTheory.LinearOrderClassTypes

/-- **The coded linear orders on `ℕ` meet uncountably many isomorphism classes.** -/
theorem not_countable_image_mk_linearOrderClass :
    ¬ ((Quotient.mk (isoSetoid Language.order ℕ)) '' linearOrderClass).Countable := by
  intro h
  -- A code of type `β` for each `β ∈ [ω, ω₁)`.
  have hcode (β : (Ico ω ω₁ : Set Ordinal.{0})) :=
    exists_mem_wellOrderClass_type_eq (V := ℕ) (L := Language.order) leSymb
      (β := (β : Ordinal.{0})) β.property.1 β.property.2
  choose c hc htype using hcode
  let f : (Ico ω ω₁ : Set Ordinal.{0}) →
      (Quotient.mk (isoSetoid Language.order ℕ)) '' linearOrderClass :=
    fun β =>
      have := mem_wellOrderClass.1 (hc β)
      ⟨Quotient.mk _ (addDiag (c β)), addDiag (c β), addDiag_mem_linearOrderClass, rfl⟩
  have hf : Function.Injective f := fun β γ hβγ => by
    have := type_eq_of_isoSetoid_addDiag (hc β) (hc γ)
      (Quotient.exact (congrArg Subtype.val hβγ))
    exact Subtype.ext ((htype β).symm.trans (this.trans (htype γ)))
  have : Countable (Ico ω ω₁ : Set Ordinal.{0}) := by
    have := h.to_subtype
    exact hf.countable
  exact not_countable_Ico_omega_one Ordinal.omega0_lt_omega_one (countable_coe_iff.1 this)

end TauCeti.Examples.ModelTheory.LinearOrderClassTypes
