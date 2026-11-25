/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Transitive
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

/-!
# Topologically mixing maps

A map `T : X → X` of a topological space is *topologically mixing* if for all nonempty open sets
`U` and `V`, the set `T^[n] '' U ∩ V` is nonempty for all large `n`. Topological transitivity of a
map is Mathlib's `MulAction.IsTopologicallyTransitive` for the `ℕ`-action `IterateMulAct T` of its
iterates.

## Main definitions

* `TauCeti.IsTopologicallyMixing T` — `T` is topologically mixing.

## Main results

* `TauCeti.IsTopologicallyMixing.isTopologicallyTransitive` — a topologically mixing map is
  topologically transitive.
* `TauCeti.isTopologicallyTransitive_not` and `TauCeti.not_isTopologicallyMixing_not` — the swap
  `Bool.not` of the discrete two-point space is topologically transitive but not topologically
  mixing: `T^[n] '' {false} ∩ {false}` is empty for every odd `n`.
-/

public section

namespace TauCeti

open Filter Set MulAction

variable {X : Type*} [TopologicalSpace X]

/-- A map `T : X → X` is *topologically mixing* if for all nonempty open sets `U` and `V`,
`T^[n] '' U ∩ V` is nonempty for all large `n`. -/
def IsTopologicallyMixing (T : X → X) : Prop :=
  ∀ ⦃U V : Set X⦄, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
    ∀ᶠ n in atTop, (T^[n] '' U ∩ V).Nonempty

/-- A topologically mixing map is topologically transitive: the action of its iterates is
topologically transitive. -/
theorem IsTopologicallyMixing.isTopologicallyTransitive {T : X → X}
    (hT : IsTopologicallyMixing T) : IsTopologicallyTransitive (IterateMulAct T) X := by
  refine ⟨fun hU hU₀ hV hV₀ ↦ ?_⟩
  obtain ⟨n, hn⟩ := (hT hU hU₀ hV hV₀).exists
  exact ⟨IterateMulAct.mk n, hn⟩

section Swap

private lemma iterate_not_odd (k : ℕ) (b : Bool) : Bool.not^[2 * k + 1] b = !b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, Function.iterate_add_apply, ih]
    simp

/-- The swap of two points is topologically transitive. -/
theorem isTopologicallyTransitive_not :
    IsTopologicallyTransitive (IterateMulAct Bool.not) Bool := by
  refine ⟨fun {U V} _ ⟨u, hu⟩ _ ⟨v, hv⟩ ↦ ?_⟩
  by_cases h : u = v
  · exact ⟨IterateMulAct.mk 0, v, ⟨u, hu, h⟩, hv⟩
  · refine ⟨IterateMulAct.mk 1, v, ⟨u, hu, ?_⟩, hv⟩
    cases u <;> cases v <;> simp_all [IterateMulAct.mk_smul]

/-- The swap of two points is not topologically mixing: `T^[n] '' {false} ∩ {false}` is empty for
every odd `n`. -/
theorem not_isTopologicallyMixing_not : ¬ IsTopologicallyMixing Bool.not := by
  intro h
  obtain ⟨n, hn⟩ := (h (isOpen_discrete {false}) (singleton_nonempty _)
    (isOpen_discrete {false}) (singleton_nonempty _)).exists_forall_of_atTop
  have := hn (2 * n + 1) (by omega)
  rw [image_singleton, iterate_not_odd] at this
  simp at this

end Swap

end TauCeti
