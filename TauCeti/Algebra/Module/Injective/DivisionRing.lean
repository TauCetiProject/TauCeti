/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Modules over a division ring are injective

Every module over a division ring is injective. By Baer's criterion it suffices to extend maps
from left ideals, and a left ideal of a division ring is zero or the whole ring.
-/

@[expose] public section

universe u v

/-- **Every module over a division ring is injective.** -/
instance Module.Injective.of_divisionRing (D : Type u) [DivisionRing D] (M : Type v)
    [AddCommGroup M] [Module D M] : Module.Injective D M :=
  Module.Baer.injective fun I g ↦ by
    rcases Ideal.eq_bot_or_top I with rfl | rfl
    · refine ⟨0, fun x hx ↦ ?_⟩
      obtain rfl := (Submodule.mem_bot D).1 hx
      rw [(Submodule.mk_eq_zero _ hx).2 rfl, map_zero, map_zero]
    · exact ⟨g ∘ₗ (LinearEquiv.ofTop (⊤ : Ideal D) rfl).symm.toLinearMap, fun _ _ ↦ rfl⟩
