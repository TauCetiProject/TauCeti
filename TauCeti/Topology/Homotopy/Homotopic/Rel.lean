/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Shrinking the fixed set of a relative homotopy

A homotopy relative to a set `S` fixes every point of `S` at all times, so it is also a homotopy
relative to every subset of `S`. This lets relative homotopies obtained relative to different sets
be composed relative to a common subset.

## Main declarations

* `ContinuousMap.HomotopyRel.mono`: a homotopy relative to `S` as a homotopy relative to `T ⊆ S`.
* `ContinuousMap.HomotopicRel.mono`: maps homotopic relative to `S` are homotopic relative to
  every `T ⊆ S`.
-/

public section

open unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ : C(X, Y)} {S T : Set X}

/-- A homotopy relative to `S` is a homotopy relative to every subset of `S`. -/
def HomotopyRel.mono (F : HomotopyRel f₀ f₁ S) (hTS : T ⊆ S) : HomotopyRel f₀ f₁ T where
  toFun := F
  continuous_toFun := F.continuous
  map_zero_left := F.apply_zero
  map_one_left := F.apply_one
  prop' t _ hx := F.prop t _ (hTS hx)

/-- Shrinking the fixed set does not change the homotopy. -/
@[simp]
lemma HomotopyRel.mono_apply (F : HomotopyRel f₀ f₁ S) (hTS : T ⊆ S) (x : I × X) :
    F.mono hTS x = F x :=
  (rfl)

/-- Maps homotopic relative to `S` are homotopic relative to every subset of `S`. -/
theorem HomotopicRel.mono (h : HomotopicRel f₀ f₁ S) (hTS : T ⊆ S) : HomotopicRel f₀ f₁ T :=
  h.map (·.mono hTS)

end ContinuousMap
