/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Option
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting bijections with a prescribed value

For two finite sets of the same size, fixing the image of one point leaves `(n - 1)!`
bijections. This is the pointed version of `Fintype.card_equiv`, useful when counting
labellings of a transitive action with a distinguished point.
-/

public section

namespace Nat

/-- There are `(n - 1)!` bijections between two finite sets of size `n` taking a specified
point to a specified point. -/
theorem card_equiv_apply_eq {α β : Type*} [Finite α] [Finite β] (a : α) (b : β)
    (h : Nat.card α = Nat.card β) :
    Nat.card {e : α ≃ β // e a = b} = (Nat.card α - 1).factorial := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let E : (α ≃ β) ≃ (Option {z : α // z ≠ a} ≃ β) :=
    Equiv.equivCongr (Equiv.optionSubtypeNe a).symm (Equiv.refl β)
  let E' : {e : α ≃ β // e a = b} ≃
      {e : Option {z : α // z ≠ a} ≃ β // e none = b} :=
    E.subtypeEquiv (fun e ↦ by simp [E])
  rw [Nat.card_congr (E'.trans (Equiv.optionSubtype b)), Nat.card_eq_fintype_card]
  have hc : Fintype.card {z : α // z ≠ a} = Fintype.card {z : β // z ≠ b} := by
    simpa [Fintype.card_subtype_compl, Nat.card_eq_fintype_card] using
      congrArg (fun n ↦ n - 1) h
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hc)]
  simp [Fintype.card_subtype_compl, Nat.card_eq_fintype_card]

end Nat
