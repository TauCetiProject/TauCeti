/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic

/-!
# Congruence of meagre sets modulo the residual filter

A set `s` in a topological space `X` is meagre (`IsMeagre s`) when its complement belongs to the
`residual` filter. Consequently, meagreness is invariant under eventual equality
`s =ᶠ[residual X] t` (written `s =ᵇ t` when `Mathlib.Topology.Baire.BaireMeasurable` is open).

## Main results

* `IsMeagre.congr`: if `s` is meagre and `s =ᶠ[residual X] t`, then `t` is meagre.
* `TauCeti.isMeagre_congr`: if `s =ᶠ[residual X] t`, then `IsMeagre s ↔ IsMeagre t`.
-/

public section

open Filter Set

/-- Meagreness transfers across eventual equality with respect to `residual X`. -/
theorem IsMeagre.congr {X : Type*} [TopologicalSpace X] {s t : Set X} (hs : IsMeagre s)
    (h : s =ᶠ[residual X] t) : IsMeagre t := by
  rw [IsMeagre, ← eventually_mem_set] at hs ⊢
  exact hs.mp (h.compl.mem_iff.mono fun _ hiff hx => hiff.1 hx)

namespace TauCeti

/-- Meagreness is invariant under eventual equality with respect to `residual X`. -/
theorem isMeagre_congr {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s =ᶠ[residual X] t) : IsMeagre s ↔ IsMeagre t :=
  ⟨fun hs => hs.congr h, fun ht => ht.congr h.symm⟩

end TauCeti
