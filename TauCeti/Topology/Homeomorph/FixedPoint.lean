/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# The fixed-point property is invariant under homeomorphisms

A topological space has the fixed-point property when every continuous self-map has a fixed point.
Conjugating a self-map by a homeomorphism `h : X ≃ₜ Y` matches the fixed points of the two maps,
so `X` has the fixed-point property exactly when `Y` does
(`Homeomorph.forall_exists_isFixedPt_iff`). This transports Brouwer's fixed-point theorem from
the disk to every space homeomorphic to it.
-/

public section

open Function

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homeomorphic spaces have the fixed-point property together: every continuous self-map of `X`
has a fixed point exactly when every continuous self-map of `Y` does. -/
theorem forall_exists_isFixedPt_iff (h : X ≃ₜ Y) :
    (∀ f : C(X, X), ∃ x, IsFixedPt f x) ↔ ∀ g : C(Y, Y), ∃ y, IsFixedPt g y := by
  constructor
  · intro hX g
    obtain ⟨x, hx⟩ := hX ((h.symm : C(Y, X)).comp (g.comp h))
    exact ⟨h x, h.symm_apply_eq.1 hx⟩
  · intro hY f
    obtain ⟨y, hy⟩ := hY ((h : C(X, Y)).comp (f.comp h.symm))
    exact ⟨h.symm y, h.eq_symm_apply.2 hy⟩

end Homeomorph
