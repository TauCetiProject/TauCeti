/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Restricting the codomain of a continuous map

A continuous map `f : C(X, Y)` taking all its values in a set `s ⊆ Y` restricts to a continuous
map `f.codRestrict s hs : C(X, s)`, the bundled form of `Set.codRestrict` and
`Continuous.codRestrict`. Followed by the inclusion `ContinuousMap.subtypeVal s`, it is `f` again.

## Main declarations

* `ContinuousMap.codRestrict`: the restriction of the codomain of a continuous map to a set
  containing its range.
* `ContinuousMap.subtypeVal_comp_codRestrict`: the restriction followed by the inclusion of the
  set is the original map.
-/

public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The restriction of the codomain of a continuous map `f : C(X, Y)` to a set `s` containing
all its values. -/
def codRestrict (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) : C(X, s) :=
  ⟨s.codRestrict f hs, f.continuous.codRestrict hs⟩

/-- The values of the restriction of the codomain of `f` are those of `f`. -/
@[simp]
theorem coe_codRestrict_apply (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) (x : X) :
    (f.codRestrict s hs x : Y) = f x :=
  (rfl)

/-- The restriction of the codomain of `f`, followed by the inclusion of the set, is `f`. -/
@[simp]
theorem subtypeVal_comp_codRestrict (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) :
    (subtypeVal s).comp (f.codRestrict s hs) = f :=
  ext fun _ ↦ rfl

end ContinuousMap
