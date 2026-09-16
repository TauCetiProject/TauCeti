/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Evaluating the homeomorphism between equal sets

This file records how Mathlib's `Homeomorph.setCongr`, the homeomorphism between the subtypes of
two equal sets, acts on points.

## Main results

* `Homeomorph.setCongr_apply`: `setCongr` retypes a point without moving it.
-/

public section

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]

/-- `Homeomorph.setCongr` retypes a point without moving it. This is the homeomorphism counterpart
of Mathlib's `Set.equivOfEq_apply`, which does not match through the homeomorphism constructor. -/
@[simp]
theorem setCongr_apply {s t : Set X} (h : s = t) (x : s) :
    setCongr h x = ⟨x, h ▸ x.2⟩ :=
  rfl

end Homeomorph
