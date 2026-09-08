/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Properties

/-!
# Open subsets of schemes

This file records general-purpose facts about open subsets of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.isClosed_singleton_of_coheight_eq_one` states that a
  codimension-one point is closed on a scheme whose points all have codimension at most one;
* `TauCeti.AlgebraicGeometry.Scheme.instNonemptyTop` states that the whole space is a nonempty open
  subset of any nonempty scheme.
-/

open Order TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- On a scheme whose points all have codimension at most one, a codimension-one point is
closed. -/
public theorem isClosed_singleton_of_coheight_eq_one {X : Scheme.{u}}
    (hdim : ∀ y : X, coheight y ≤ 1)
    {x : X} (hx : coheight x = 1) : IsClosed ({x} : Set X) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
  -- `y ∈ closure {x}` says `x ⤳ y`, which is exactly `y ≤ x` in the specialization preorder; a
  -- strict such `y` would be a proper specialization of `x`, hence of codimension at least two.
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  rcases eq_or_ne y x with rfl | hne
  · exact Set.mem_singleton _
  refine absurd (hdim y) (not_le.mpr ?_)
  have hlt : y < x :=
    ⟨hyx, fun hxy ↦ hne (Inseparable.eq (inseparable_iff_specializes_and.mpr ⟨hxy, hyx⟩))⟩
  simpa [hx] using Order.coheight_strictAnti hlt (by simp [hx])

namespace Scheme

/-- The whole space is a nonempty open subset of a nonempty scheme. -/
public instance instNonemptyTop {X : Scheme.{u}} [Nonempty X] :
    Nonempty ((⊤ : X.Opens) : Type u) :=
  let ⟨x⟩ := ‹Nonempty X›
  ⟨⟨x, trivial⟩⟩

end Scheme

end AlgebraicGeometry

end TauCeti
