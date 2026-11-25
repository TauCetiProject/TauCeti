/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.ModelTheory.RelationalConfiguration.WellOrder
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

/-- The code obtained by adding the diagonal to the relation of `c`, written as the order
`x = y ∨ r x y` of Mathlib's `partialOrderOfSO`. -/
noncomputable def addDiag (c : RelationalConfiguration Language.order ℕ) :
    RelationalConfiguration Language.order ℕ :=
  ofRel fun x y => x = y ∨ codeRel leSymb c x y

/-- The relation of `addDiag c` is the relation of `c` with the diagonal added. -/
@[simp]
theorem codeRel_addDiag (c : RelationalConfiguration Language.order ℕ) (x y : ℕ) :
    codeRel leSymb (addDiag c) x y ↔ x = y ∨ codeRel leSymb c x y := by
  rw [addDiag, codeRel_ofRel]

/-- Adding the diagonal to a coded strict well-order gives a coded linear order: its relation is
the order of Mathlib's `linearOrderOfSTO`. -/
theorem addDiag_mem_linearOrderClass {c : RelationalConfiguration Language.order ℕ}
    (hc : c ∈ wellOrderClass leSymb) : addDiag c ∈ linearOrderClass := by
  rw [mem_wellOrderClass] at hc
  classical
  have h : codeRel leSymb (addDiag c) = (linearOrderOfSTO (codeRel leSymb c)).le := by
    ext x y
    exact codeRel_addDiag c x y
  rw [mem_linearOrderClass, h]
  let := linearOrderOfSTO (codeRel leSymb c)
  infer_instance

/-- Isomorphic codes with the diagonal added come from coded strict well-orders of the same
type. -/
theorem type_eq_of_isoSetoid_addDiag {c d : RelationalConfiguration Language.order ℕ}
    (hc : c ∈ wellOrderClass leSymb) (hd : d ∈ wellOrderClass leSymb)
    (h : isoSetoid Language.order ℕ (addDiag c) (addDiag d)) :
    @Ordinal.type ℕ (codeRel leSymb c) (mem_wellOrderClass.1 hc) =
      @Ordinal.type ℕ (codeRel leSymb d) (mem_wellOrderClass.1 hd) := by
  have := mem_wellOrderClass.1 hc
  have := mem_wellOrderClass.1 hd
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  -- `σ` carries the reflexive closure of `codeRel leSymb c` to that of `codeRel leSymb d`.
  have hrefl (x y : ℕ) :
      σ x = σ y ∨ codeRel leSymb d (σ x) (σ y) ↔ x = y ∨ codeRel leSymb c x y := by
    have := codeRel_perm_smul leSymb σ (addDiag c) (σ x) (σ y)
    rw [hσ] at this
    simpa using this
  refine RelIso.ordinalType_congr ⟨σ, fun {x y} => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun h => absurd h (irrefl _), fun h => absurd h (irrefl _)⟩
  · have hσxy : σ x ≠ σ y := σ.injective.ne hxy
    simpa [hxy, hσxy] using hrefl x y

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
    fun β => ⟨Quotient.mk _ (addDiag (c β)), addDiag (c β), addDiag_mem_linearOrderClass (hc β),
      rfl⟩
  have hf : Function.Injective f := fun β γ hβγ => by
    have := type_eq_of_isoSetoid_addDiag (hc β) (hc γ)
      (Quotient.exact (congrArg Subtype.val hβγ))
    exact Subtype.ext ((htype β).symm.trans (this.trans (htype γ)))
  have : Countable (Ico ω ω₁ : Set Ordinal.{0}) := by
    have := h.to_subtype
    exact hf.countable
  exact not_countable_Ico_omega0_omega_one (countable_coe_iff.1 this)

end TauCeti.Examples.ModelTheory.LinearOrderClassTypes
