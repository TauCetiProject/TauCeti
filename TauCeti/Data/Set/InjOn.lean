/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Injectivity on sets of maps with a single collapse

A map `α` out of a linear order whose only identification of two distinct points is
`α k = α k'` is injective on a set exactly when the set does not contain both `k` and `k'`
(`Set.injOn_iff_of_collapse`).  Codegeneracies of `SimplexCategory` are maps of this kind.
-/

public section

namespace Set

/-- If the only pair of points `a < b` identified by `α` is `k < k'`, then `α` is injective on a
set `U` exactly when `U` does not contain both `k` and `k'`. -/
theorem injOn_iff_of_collapse {κ ι : Type*} [LinearOrder κ] {α : κ → ι} {k k' : κ}
    (hkk' : k < k') (hk : α k = α k') (hcol : ∀ a b, a < b → α a = α b → a = k ∧ b = k')
    (U : Set κ) : InjOn α U ↔ ¬(k ∈ U ∧ k' ∈ U) := by
  refine ⟨fun hU hkU ↦ hkk'.ne (hU hkU.1 hkU.2 hk), fun hU a ha b hb hab ↦ ?_⟩
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · obtain ⟨rfl, rfl⟩ := hcol a b hlt hab
    exact absurd ⟨ha, hb⟩ hU
  · rfl
  · obtain ⟨rfl, rfl⟩ := hcol b a hgt hab.symm
    exact absurd ⟨hb, ha⟩ hU

end Set
