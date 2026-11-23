/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import TauCeti.Order.Hereditary

/-!
# Order-hereditary proper cones

This file records basic order-heredity (`TauCeti.IsHereditary`) facts for `ProperCone`: the
bottom cone `⊥` (in a `T₁` partially ordered space) and the positive cone `ProperCone.positive R E`
are hereditary.
-/

public section

namespace ProperCone

open TauCeti

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid E] [TopologicalSpace E] [Module R E] [PartialOrder E]

/-- The bottom proper cone is hereditary in any `T₁` partially ordered space. -/
@[simp]
theorem isHereditary_bot [T1Space E] : IsHereditary (⊥ : ProperCone R E) := by
  rw [isHereditary_def]
  intro a b ha hab hb
  rw [ProperCone.mem_bot] at hb ⊢
  exact le_antisymm (hab.trans_eq hb) ha

/-- The positive cone `ProperCone.positive R E` is hereditary. -/
@[simp]
theorem isHereditary_positive [IsOrderedAddMonoid E] [PosSMulMono R E] [OrderClosedTopology E] :
    IsHereditary (ProperCone.positive R E) :=
  isHereditary_def.mpr fun _ _ ha _ _ => ha

end ProperCone
