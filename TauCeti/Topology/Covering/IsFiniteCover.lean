/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Homeomorph

/-!
# Finite covers

A map `p : N → M` is a *finite cover* when it is a surjective covering map with finite fibres,
that is, `N` is a finite-sheeted covering space of `M` with every sheet count positive.
Surjectivity is imposed because Mathlib's `IsCoveringMap` allows empty fibres: without it the
inclusion of one component of a disconnected space would count as a finite cover.

This is the unbundled form, a predicate on a map between types with their topologies. Finite
covering spaces in the bundled sense, as objects of `TopCat / X`, are
`TauCeti.FiniteCoveringSpace`.

## Main definitions

* `TauCeti.IsFiniteCover p`: `p` is a surjective covering map with finite fibres.

## Main results

* `Homeomorph.isFiniteCover`, `TauCeti.IsFiniteCover.id`: homeomorphisms, and in particular the
  identity, are finite covers.
* `TauCeti.IsFiniteCover.homeomorph_comp`: a finite cover followed by a homeomorphism is a finite
  cover.
* `TauCeti.IsFiniteCover.connectedSpace`, `TauCeti.IsFiniteCover.infinite`: the base of a finite
  cover by a connected, respectively infinite, space is connected, respectively infinite.
-/

public section

namespace TauCeti

variable {N M M' : Type*} [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace M']
  {p : N → M}

/-- A map `p : N → M` is a **finite cover** if it is a surjective covering map with finite
fibres. -/
structure IsFiniteCover (p : N → M) : Prop where
  /-- A finite cover is a covering map. -/
  isCoveringMap : IsCoveringMap p
  /-- A finite cover is surjective. -/
  surjective : Function.Surjective p
  /-- Every fibre of a finite cover is finite. -/
  finite_fiber (x : M) : Finite (p ⁻¹' {x})

/-- A homeomorphism is a finite cover, with one-point fibres. -/
theorem _root_.Homeomorph.isFiniteCover (e : N ≃ₜ M) : IsFiniteCover e where
  isCoveringMap := e.isCoveringMap
  surjective := e.surjective
  finite_fiber _ := (Set.subsingleton_singleton.preimage e.injective).finite.to_subtype

namespace IsFiniteCover

/-- The identity of a space is a finite cover. -/
protected theorem id : IsFiniteCover (@id N) where
  isCoveringMap := .id
  surjective := Function.surjective_id
  finite_fiber x := Set.finite_singleton x

/-- A finite cover followed by a homeomorphism of the base is a finite cover. -/
theorem homeomorph_comp (hp : IsFiniteCover p) (e : M ≃ₜ M') : IsFiniteCover (e ∘ p) where
  isCoveringMap := hp.isCoveringMap.homeomorph_comp e
  surjective := e.surjective.comp hp.surjective
  finite_fiber x := by
    rw [Set.preimage_comp, ← e.image_symm, Set.image_singleton]
    exact hp.finite_fiber _

/-- The base of a finite cover by a connected space is connected. -/
theorem connectedSpace [ConnectedSpace N] (hp : IsFiniteCover p) : ConnectedSpace M :=
  hp.surjective.connectedSpace hp.isCoveringMap.continuous

/-- The base of a finite cover by an infinite space is infinite: a finite cover of a finite space
is finite. -/
theorem infinite [Infinite N] (hp : IsFiniteCover p) : Infinite M := by
  by_contra hM
  have : Finite M := not_infinite_iff_finite.mp hM
  have := hp.finite_fiber
  exact Set.infinite_univ (α := N) <| by
    simpa using Set.finite_univ.preimage' fun x _ ↦ Set.toFinite (p ⁻¹' {x})

end IsFiniteCover

end TauCeti
