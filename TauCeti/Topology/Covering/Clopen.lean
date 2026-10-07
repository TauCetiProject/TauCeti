/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Covering.Basic

/-!
# Covering maps and clopen sets

A covering map `p : E → ↥s` onto a subspace of `X` is also a covering map `E → X` as soon as `s`
is clopen: over a point of `s` an evenly covered neighbourhood in `↥s` is one in `X` because `s`
is open, and over a point outside `s` the open set `sᶜ` has empty preimage, which
`IsEvenlyCovered.of_preimage_eq_empty` accepts as an evenly covered neighbourhood with empty
fibre.

Openness alone is not enough: for `s` open but not closed, a point of `frontier s` has every
neighbourhood meeting `s`, so no neighbourhood of it is evenly covered by a surjection onto `s`.
Mathlib's `IsCoveringMap` allows empty fibres, which is exactly what makes the clopen statement
work without assuming `p` surjective or `s = X`.

The number of points in a fibre of a covering map is locally constant: an evenly covered
neighbourhood identifies the fibres over all of its points. So for any type `α`, the set of points
whose fibre is in bijection with `α` is clopen.

## Main declarations

* `IsCoveringMap.subtypeVal_comp`: the composite of a covering map onto a clopen
  subspace with the subspace inclusion is a covering map.
* `IsCoveringMap.isClopen_setOf_nonempty_fiber_equiv`: the points whose fibre is in bijection
  with a given type form a clopen set.
* `IsCoveringMap.nonempty_fiber_equiv`: over a preconnected base all fibres are in bijection, and
  `IsCoveringMap.surjective`: a covering map from a nonempty space onto a preconnected space is
  surjective.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {s : Set X}

/-- **A covering map onto a clopen subspace is a covering map into the ambient space.** Points of
`s` inherit their evenly covered neighbourhoods through the open inclusion, and points outside
`s` are evenly covered by `sᶜ` with empty fibre. -/
theorem _root_.IsCoveringMap.subtypeVal_comp {p : E → s} (hp : IsCoveringMap p) (hs : IsClopen s) :
    IsCoveringMap (Subtype.val ∘ p) := by
  intro x
  by_cases hx : x ∈ s
  · exact ((hp ⟨x, hx⟩).subtypeVal_comp _ hs.isOpen).to_isEvenlyCovered_preimage
  · refine IsEvenlyCovered.to_isEvenlyCovered_preimage
      (IsEvenlyCovered.of_preimage_eq_empty Empty (hs.isClosed.isOpen_compl.mem_nhds hx) ?_)
    exact Set.eq_empty_of_forall_notMem fun e he => he (p e).2

/-- **The number of points in a fibre of a covering map is locally constant.** Over an evenly
covered neighbourhood all fibres are in bijection, so both the points whose fibre is in bijection
with `α` and the points whose fibre is not are open. -/
theorem _root_.IsCoveringMap.isClopen_setOf_nonempty_fiber_equiv {p : E → X} (hp : IsCoveringMap p)
    (α : Type*) : IsClopen {x : X | Nonempty (p ⁻¹' {x} ≃ α)} := by
  have key : ∀ y : X, ∃ U : Set X, y ∈ U ∧ IsOpen U ∧
      ∀ z ∈ U, Nonempty (p ⁻¹' {z} ≃ p ⁻¹' {y}) := by
    intro y
    obtain ⟨hd, U, hyU, hU, hfU, H, hH⟩ := hp y
    exact ⟨U, hyU, hU, fun z hz =>
      ⟨(IsEvenlyCovered.fiberHomeomorph ⟨hd, U, hz, hU, hfU, H, hH⟩).toEquiv.symm⟩⟩
  refine ⟨?_, isOpen_iff_forall_mem_open.2 fun y ⟨ν⟩ => ?_⟩
  · refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun y hy => ?_)
    obtain ⟨U, hyU, hU, hUy⟩ := key y
    exact ⟨U, fun z hz ⟨ν⟩ => hy ⟨(hUy z hz).some.symm.trans ν⟩, hU, hyU⟩
  · obtain ⟨U, hyU, hU, hUy⟩ := key y
    exact ⟨U, fun z hz => ⟨(hUy z hz).some.trans ν⟩, hU, hyU⟩

/-- **Over a preconnected base, all fibres of a covering map are in bijection.** The points whose
fibre is in bijection with the fibre over `y` form a clopen set containing `y`, hence everything. -/
theorem _root_.IsCoveringMap.nonempty_fiber_equiv [PreconnectedSpace X] {p : E → X}
    (hp : IsCoveringMap p) (x y : X) : Nonempty (p ⁻¹' {x} ≃ p ⁻¹' {y}) :=
  (hp.isClopen_setOf_nonempty_fiber_equiv (p ⁻¹' {y})).connectedComponent_subset
    (x := y) ⟨Equiv.refl _⟩
    (by simp only [PreconnectedSpace.connectedComponent_eq_univ, Set.mem_univ])

/-- **A covering map from a nonempty space onto a preconnected space is surjective:** every fibre
is in bijection with the fibre through a given point. -/
theorem _root_.IsCoveringMap.surjective [PreconnectedSpace X] [Nonempty E] {p : E → X}
    (hp : IsCoveringMap p) : Function.Surjective p := fun x => by
  obtain ⟨e⟩ := ‹Nonempty E›
  obtain ⟨ν⟩ := hp.nonempty_fiber_equiv x (p e)
  exact ⟨(ν.symm ⟨e, rfl⟩).1, (ν.symm ⟨e, rfl⟩).2⟩

end TauCeti
