/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Transitive
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.Parity

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

/-- The characterization of topological mixing: for all nonempty open sets `U` and `V`,
`T^[n] '' U ∩ V` is nonempty for all large `n`. -/
theorem isTopologicallyMixing_iff {T : X → X} :
    IsTopologicallyMixing T ↔ ∀ ⦃U V : Set X⦄, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∀ᶠ n in atTop, (T^[n] '' U ∩ V).Nonempty :=
  Iff.rfl

/-- A topologically mixing map is topologically transitive: the action of its iterates is
topologically transitive. -/
theorem IsTopologicallyMixing.isTopologicallyTransitive {T : X → X}
    (hT : IsTopologicallyMixing T) : IsTopologicallyTransitive (IterateMulAct T) X := by
  refine ⟨fun hU hU₀ hV hV₀ ↦ ?_⟩
  obtain ⟨n, hn⟩ := (hT hU hU₀ hV hV₀).exists
  refine ⟨IterateMulAct.mk n, ?_⟩
  simpa only [← image_smul, IterateMulAct.mk_smul] using hn

section Swap

/-- The swap of two points is topologically transitive. -/
theorem isTopologicallyTransitive_not :
    IsTopologicallyTransitive (IterateMulAct Bool.not) Bool := by
  refine ⟨fun {U V} _ ⟨u, hu⟩ _ ⟨v, hv⟩ ↦ ?_⟩
  by_cases h : u = v
  · refine ⟨IterateMulAct.mk 0, v, mem_smul_set.2 ⟨u, hu, ?_⟩, hv⟩
    rw [IterateMulAct.mk_smul, Function.iterate_zero_apply, h]
  · refine ⟨IterateMulAct.mk 1, v, mem_smul_set.2 ⟨u, hu, ?_⟩, hv⟩
    rw [IterateMulAct.mk_smul, Function.iterate_one]
    cases u <;> cases v <;> simp_all

/-- The swap of two points is not topologically mixing: `T^[n] '' {false} ∩ {false}` is empty for
every odd `n`. -/
theorem not_isTopologicallyMixing_not : ¬ IsTopologicallyMixing Bool.not := by
  intro h
  obtain ⟨n, hn⟩ := (h (isOpen_discrete {false}) (singleton_nonempty _)
    (isOpen_discrete {false}) (singleton_nonempty _)).exists_forall_of_atTop
  have := hn (2 * n + 1) (by omega)
  rw [image_singleton, Bool.involutive_not.iterate_two_mul_add_one] at this
  simp at this

end Swap

end TauCeti
