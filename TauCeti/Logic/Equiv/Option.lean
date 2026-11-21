/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Extending a matching of the complements of two points

A relation between two index types that holds along an equivalence of the complements of two
points, and also holds at those two points, is realised by an equivalence of the whole types
(`Equiv.exists_equiv_forall_of_equiv_subtype_ne`).

Conversely, `Equiv.optionSubtype` identifies the equivalences sending one point to another with
the equivalences of their complements, so between two types with `m + 1` elements there are `m!`
equivalences sending a given point to a given point (`Nat.card_subtype_equiv_apply_eq`).
-/

public section

namespace Equiv

/-- A relation `R` between two types that holds along an equivalence of the complements of `i₀`
and `j₀` and also holds at `i₀, j₀` is realised by an equivalence of the whole types. -/
theorem exists_equiv_forall_of_equiv_subtype_ne {ι κ : Type*}
    {R : ι → κ → Prop} {i₀ : ι} {j₀ : κ} (e : {i // i ≠ i₀} ≃ {j // j ≠ j₀}) (h₀ : R i₀ j₀)
    (h : ∀ i : {i // i ≠ i₀}, R i (e i)) : ∃ e' : ι ≃ κ, ∀ i, R i (e' i) := by
  classical
  refine ⟨(Equiv.optionSubtypeNe i₀).symm.trans
    ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe j₀)), fun i ↦ ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · have hnone : ((Equiv.optionSubtypeNe i).symm.trans
        ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe j₀))) i = j₀ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self]
      rfl
    rwa [hnone]
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi,
      Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]
    exact h ⟨i, hi⟩

end Equiv

open Equiv in
/-- Between two finite types of the same cardinality, the equivalences sending `a` to `b` are
counted by the factorial of the number of remaining points. -/
theorem Nat.card_subtype_equiv_apply_eq {α β : Type*} [Finite α]
    (hαβ : Nat.card α = Nat.card β) (a : α) (b : β) :
    Nat.card {e : α ≃ β // e a = b} = (Nat.card α - 1).factorial := by
  classical
  have : Finite β := Nat.finite_of_card_ne_zero (by
    have := Nat.card_pos_iff.2 ⟨⟨a⟩, ‹_›⟩; omega)
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  let E : {e : α ≃ β // e a = b} ≃ ({x // x ≠ a} ≃ {y // y ≠ b}) :=
    ((equivCongr (optionSubtypeNe a) (Equiv.refl β)).symm.subtypeEquiv (fun e ↦ by simp)).trans
      (optionSubtype b)
  have hb : Fintype.card {x // x ≠ a} = Fintype.card {y // y ≠ b} := by
    simpa [Fintype.card_subtype_compl, Nat.card_eq_fintype_card] using congrArg (· - 1) hαβ
  rw [Nat.card_congr E, Nat.card_eq_fintype_card,
    Fintype.card_equiv (Fintype.equivOfCardEq hb), Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype_compl]
