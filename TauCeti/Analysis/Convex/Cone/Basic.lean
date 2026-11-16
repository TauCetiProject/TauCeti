/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import TauCeti.Order.Interval.Set.OrdConnected

/-!
# Order-connected proper subcones of the positive cone

In an ordered topological module `E`, a proper cone `C ≤ ProperCone.positive R E` contains `0` and
consists of nonnegative elements, so its underlying set satisfies `Set.OrdConnected` if and only if
`0 ≤ a ≤ b` and `b ∈ C` imply `a ∈ C`.

## Main results

* `ProperCone.ordConnected_iff_of_le_positive`: hereditary downward-closure characterization of
  `(C : Set E).OrdConnected` for `C ≤ ProperCone.positive R E`.
* `ProperCone.ordConnected_positive`: `(ProperCone.positive R E : Set E)` is order-connected.
-/

public section

namespace ProperCone

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E]
  [TopologicalSpace E] [Module R E] [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono R E]
  [OrderClosedTopology E]

/-- A proper cone contained in the positive cone of an ordered topological module is order-connected
if and only if `0 ≤ a ≤ b` and `b ∈ C` imply `a ∈ C`. -/
theorem ordConnected_iff_of_le_positive {C : ProperCone R E} (hC : C ≤ ProperCone.positive R E) :
    (C : Set E).OrdConnected ↔ ∀ ⦃a b : E⦄, 0 ≤ a → a ≤ b → b ∈ C → a ∈ C :=
  Set.ordConnected_iff_of_subset_Ici C.zero_mem fun _ hx ↦ ProperCone.mem_positive.mp (hC hx)

/-- The positive cone `ProperCone.positive R E` of an ordered topological module is
order-connected. -/
instance ordConnected_positive : (ProperCone.positive R E : Set E).OrdConnected := by
  have h : (ProperCone.positive R E : Set E) = Set.Ici 0 := Set.ext fun _ ↦ ProperCone.mem_positive
  rw [h]
  infer_instance

end ProperCone
