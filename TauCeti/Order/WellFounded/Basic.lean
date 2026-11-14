/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WellFounded

/-!
# Choices by well-founded recursion

A function can be built one point at a time along a well-founded relation `r`, when the
admissible values at a point only depend on the values already chosen at its `r`-predecessors.
This is the existence statement behind such constructions, with the recursion itself hidden: it
runs along the transitive closure of `r`, so `r` need not be transitive.

Dually, a nonempty finite set has an element that is `r`-related to no element of the set, the
starting point of a descent that removes such elements one at a time.

## Main results

* `WellFounded.exists_forall_of_forall_exists`: if an admissible value exists at every point as
  soon as the values at its `r`-predecessors are admissible, then some function takes admissible
  values everywhere.
* `WellFounded.exists_mem_forall_not_rel`: a nonempty finite set has an element `a` with `r a b`
  for no `b` in the set.
-/

public section

namespace WellFounded

universe u v

open Relation

/-- **Choices by well-founded recursion.** Let `V F x v` say that `v` is an admissible value at
`x`, in a type `X x`, for a dependent function `F`, depending only on the values of `F` at the
`r`-predecessors of `x`. If an admissible value exists at `x` as soon as `F` takes admissible
values at all `r`-predecessors of `x`, then some function takes admissible values everywhere. -/
theorem exists_forall_of_forall_exists {α : Type u} {X : α → Sort v} [∀ x, Nonempty (X x)]
    {r : α → α → Prop} (hr : WellFounded r) (V : (∀ x, X x) → ∀ x, X x → Prop)
    (hV : ∀ ⦃x v⦄ ⦃F F' : ∀ x, X x⦄, (∀ y, r y x → F y = F' y) → V F x v → V F' x v)
    (hex : ∀ x (F : ∀ x, X x), (∀ y, r y x → V F y (F y)) → ∃ v, V F x v) :
    ∃ G : ∀ x, X x, ∀ x, V G x (G x) := by
  classical
  -- Recurse along the transitive closure, extending the earlier values arbitrarily.
  let F (x : α) (IH : ∀ y, TransGen r y x → X y) : ∀ y, X y := fun y ↦
    if hy : TransGen r y x then IH y hy else Classical.arbitrary (X y)
  let step (x : α) (IH : ∀ y, TransGen r y x → X y) : X x :=
    if hc : ∀ y, r y x → V (F x IH) y (F x IH y) then (hex x _ hc).choose
    else Classical.arbitrary (X x)
  refine ⟨hr.transGen.fix step, fun x ↦ hr.transGen.induction
    (C := fun x ↦ V (hr.transGen.fix step) x (hr.transGen.fix step x)) x fun x ih ↦ ?_⟩
  have hF : ∀ y, TransGen r y x →
      F x (fun y _ ↦ hr.transGen.fix step y) y = hr.transGen.fix step y :=
    fun y hy ↦ dite_eq_left hy
  have hc : ∀ y, r y x → V (F x fun y _ ↦ hr.transGen.fix step y) y
      (F x (fun y _ ↦ hr.transGen.fix step y) y) := fun y hy ↦ by
    rw [hF y (.single hy)]
    exact hV (fun z hz ↦ (hF z (.head hz (.single hy))).symm) (ih y (.single hy))
  rw [hr.transGen.fix_eq step x]
  dsimp only [step]
  rw [dite_eq_left hc]
  exact hV (fun y hy ↦ hF y (.single hy)) (hex x _ hc).choose_spec

/-- **Maximal elements for a well-founded relation.** A nonempty finite set contains an element `a`
that is related to no element of the set: `r a b` fails for every `b` in it. This is the converse
direction of `WellFounded.has_min`, and it needs finiteness: on `ℕ` with `<`, the whole set has no
such element. -/
theorem exists_mem_forall_not_rel {α : Type u} {r : α → α → Prop} (hr : WellFounded r)
    {s : Set α} (hs : s.Finite) (hne : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, ¬r a b := by
  -- On the finite set `s`, the converse of the transitive closure of `r` is a strict order,
  -- hence well-founded, and a minimal element for it is related to nothing in `s`.
  have := hs.to_subtype
  let rel : s → s → Prop := fun a b ↦ TransGen r b.1 a.1
  have : IsTrans s rel := ⟨fun _ _ _ hab hbc ↦ hbc.trans hab⟩
  have : Std.Irrefl rel := ⟨fun a ↦ hr.transGen.irrefl.irrefl a.1⟩
  obtain ⟨a, -, ha⟩ := (Finite.wellFounded_of_trans_of_irrefl rel).has_min Set.univ
    ⟨⟨hne.some, hne.some_mem⟩, Set.mem_univ _⟩
  exact ⟨a.1, a.2, fun b hb hab ↦ ha ⟨b, hb⟩ (Set.mem_univ _) (.single hab)⟩

end WellFounded
