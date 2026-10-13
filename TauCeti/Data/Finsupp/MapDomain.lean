/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic

/-!
# Injective relabeling as extension by zero

For an injective index map, pushing forward a finitely supported function is ordinary
function extension by zero, over any additive commutative monoid.
-/

public section

namespace Finsupp

/-- Pushing a finitely supported function along an injection extends its values by zero
outside the image. -/
theorem coe_mapDomain_eq_extend {α β M : Type*} [AddCommMonoid M]
    {e : α → β} (he : Function.Injective e) (x : α →₀ M) :
    (mapDomain e x : β → M) = Function.extend e x 0 := by
  classical
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp [he]
  · simp [mapDomain_of_notMem_range _ _ hj, Function.extend_apply' _ _ _ hj]

end Finsupp
