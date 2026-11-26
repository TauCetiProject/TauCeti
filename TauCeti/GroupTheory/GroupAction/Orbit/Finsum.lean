/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Finite sums over an orbit

Translation by an element `g` of a group `G` acting on `α` permutes each `G`-orbit, so a finite
sum over an orbit is unchanged when its summand is precomposed with `x ↦ g • x`.

## Main results

* `TauCeti.MulAction.finsum_mem_orbit_smul`: `∑ᶠ x ∈ orbit G a, f (g • x) = ∑ᶠ x ∈ orbit G a, f x`.
-/

public section

namespace TauCeti.MulAction

open _root_.MulAction

/-- **Translation permutes an orbit.** For `g ∈ G`, precomposing the summand with `x ↦ g • x`
does not change its finite sum over the `G`-orbit of `a`. -/
theorem finsum_mem_orbit_smul {G α M : Type*} [Group G] [MulAction G α] [AddCommMonoid M]
    (g : G) (a : α) (f : α → M) :
    ∑ᶠ x ∈ orbit G a, f (g • x) = ∑ᶠ x ∈ orbit G a, f x := by
  have h := (MulAction.injective g).injOn.bijOn_image (s := orbit G a)
  rw [Set.image_smul, smul_orbit] at h
  exact finsum_mem_eq_of_bijOn _ h fun _ _ ↦ rfl

end TauCeti.MulAction
