/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Defs

/-!
# Lemmas about homeomorphisms

This file records small general-purpose facts about homeomorphisms.
-/

public section

namespace TauCeti

open Topology

variable {M : Type*} [TopologicalSpace M]
  {N : Type*} [TopologicalSpace N]
  {Z : Type*}

namespace Homeomorph

/-- A homeomorphism transports eventual equality at a neighbourhood filter. -/
@[simp]
theorem eventuallyEq_comp_iff (e : M ≃ₜ N) (f g : N → Z) (x : M) :
    (f ∘ e =ᶠ[𝓝 x] g ∘ e) ↔ (f =ᶠ[𝓝 (e x)] g) := by
  rw [← e.map_nhds_eq x]
  exact Filter.eventuallyEq_map.symm

end Homeomorph

end TauCeti
