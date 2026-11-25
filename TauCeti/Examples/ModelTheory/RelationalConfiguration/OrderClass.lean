/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Examples: coded linear orders and coded trees

The code of `(ℕ, ≤)` is a coded linear order and a coded tree (one infinite branch). The code of
`(ℕ, <)` is not a coded linear order, as it is irreflexive, and the code of `(ℕ, ≥)` is not a
coded tree, as it has no least element. The coded trees on `ℕ` do not form a closed class.

The coded linear orders on `ℕ` meet uncountably many isomorphism classes. Adding the diagonal to
the relation of a coded strict well-order gives a coded linear order. By
`exists_mem_wellOrderClass_type_eq`, every order type `β` with `ω ≤ β < ω₁` is the type of a coded
strict well-order on `ℕ`, and isomorphic codes with the diagonal added have strict parts of the
same type. So `β ↦` the class of the reflexive closure of a code of type `β` is injective on the
uncountable interval `[ω, ω₁)`, and `linearOrderClass` meets uncountably many classes of
`isoSetoid Language.order ℕ`.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration Set
open scoped Ordinal

-- The code of `(ℕ, ≤)` is a coded linear order.
example : @ofStructure Language.order ℕ (orderStructure ℕ) ∈ linearOrderClass :=
  ofStructure_mem_linearOrderClass

-- The code of `(ℕ, ≤)` is a coded tree.
example : @ofStructure Language.order ℕ (orderStructure ℕ) ∈ treeClass :=
  ofStructure_mem_treeClass strictMono_id

-- The code of `(ℕ, <)` is not a coded linear order: it is irreflexive.
example : ofRel (fun x y : ℕ => x < y) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  exact lt_irrefl 0 (h.refl 0)

-- The code of `(ℕ, ≥)` is not a coded tree: it has no least element.
example : ofRel (fun x y : ℕ => y ≤ x) ∉ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  intro h
  obtain ⟨a, ha⟩ := h.exists_forall
  exact Nat.not_succ_le_self a (ha (a + 1))

-- The coded trees on `ℕ` do not form a closed class.
example : ¬ IsClosed (treeClass (V := ℕ)) :=
  not_isClosed_treeClass

namespace TauCeti.Examples.ModelTheory.OrderClass

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

end TauCeti.Examples.ModelTheory.OrderClass
