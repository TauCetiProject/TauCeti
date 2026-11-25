/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import TauCeti.Order.Monotone.Basic

/-!
# Order properties of homeomorphisms

The inverse of a strictly decreasing homeomorphism out of a linear order is strictly decreasing
(`Homeomorph.strictAnti_symm`). This is the homeomorphism form of `Equiv.strictAnti_symm`.
-/

public section

namespace Homeomorph

/-- The inverse of a strictly antitone homeomorphism out of a linear order is strictly antitone. -/
theorem strictAnti_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LinearOrder X]
    [Preorder Y] {h : X ≃ₜ Y} (hh : StrictAnti h) : StrictAnti h.symm := by
  rw [← coe_toEquiv] at hh
  rw [← coe_symm_toEquiv]
  exact Equiv.strictAnti_symm hh

end Homeomorph
