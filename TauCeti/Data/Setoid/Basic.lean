/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Basic

/-!
# Setoid helpers

This file records small generic additions to Mathlib's `Setoid` API.

## Main declarations

* `TauCeti.Setoid.map_of_le_mk`: the quotient map induced by a setoid inequality sends a
  representative to the same representative in the larger quotient.
* `Setoid.setOf_rel_eq_iff`: two elements have the same class exactly when they are related.
-/

public section

namespace TauCeti

namespace Setoid

/-- The quotient map induced by a setoid inequality sends a representative to the same
representative in the larger quotient. -/
@[simp]
lemma map_of_le_mk {α : Type*} {s t : Setoid α} (h : s ≤ t) (x : α) :
    _root_.Setoid.map_of_le h (Quotient.mk'' x : Quotient s) =
      (Quotient.mk'' x : Quotient t) :=
  Quotient.map'_mk'' id h x

end Setoid

end TauCeti

namespace Setoid

/-- Two elements have the same class exactly when they are related. -/
theorem setOf_rel_eq_iff {α : Type*} {r : Setoid α} {x y : α} :
    {x' | r x x'} = {y' | r y y'} ↔ r x y :=
  ⟨fun h => (Set.ext_iff.mp h y).mpr (r.refl' y), fun h =>
    Set.ext fun _ => ⟨fun hx => r.trans' (r.symm' h) hx, fun hy => r.trans' h hy⟩⟩

end Setoid
