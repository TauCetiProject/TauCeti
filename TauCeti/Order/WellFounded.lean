/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.WellFounded

/-!
# Choices by well-founded recursion

A function can be built one point at a time along a well-founded relation `r`, when the
admissible values at a point only depend on the values already chosen at its `r`-predecessors.
This is the existence statement behind such constructions, with the recursion itself hidden: it
runs along the transitive closure of `r`, so `r` need not be transitive.

## Main results

* `WellFounded.exists_forall_of_forall_exists`: if an admissible value exists at every point as
  soon as the values at its `r`-predecessors are admissible, then some function takes admissible
  values everywhere.
-/

public section

namespace WellFounded

universe u v

open Relation

/-- **Choices by well-founded recursion.** Let `V F x v` say that `v` is an admissible value at
`x` for a function `F`, depending only on the values of `F` at the `r`-predecessors of `x`. If an
admissible value exists at `x` as soon as `F` takes admissible values at all `r`-predecessors of
`x`, then some function takes admissible values everywhere. -/
theorem exists_forall_of_forall_exists {α : Type u} {X : Sort v} [Nonempty X]
    {r : α → α → Prop} (hr : WellFounded r) (V : (α → X) → α → X → Prop)
    (hV : ∀ ⦃x v⦄ ⦃F F' : α → X⦄, (∀ y, r y x → F y = F' y) → V F x v → V F' x v)
    (hex : ∀ x (F : α → X), (∀ y, r y x → V F y (F y)) → ∃ v, V F x v) :
    ∃ G : α → X, ∀ x, V G x (G x) := by
  classical
  -- Recurse along the transitive closure, extending the earlier values arbitrarily.
  let F (x : α) (IH : ∀ y, TransGen r y x → X) : α → X := fun y ↦
    if hy : TransGen r y x then IH y hy else Classical.arbitrary X
  let step (x : α) (IH : ∀ y, TransGen r y x → X) : X :=
    if hc : ∀ y, r y x → V (F x IH) y (F x IH y) then (hex x _ hc).choose
    else Classical.arbitrary X
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

end WellFounded
