/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Extending continuous functions on subtypes

A continuous function `g` on a subtype `A` of a space extends along `Subtype.val`, with any
fallback off `A`, to a function on the ambient space that is continuous on `A` and agrees with `g`
there. The extension is not asserted to be continuous away from the subset. When `A` is open,
the extension agrees near each point of `A` with every function that agrees with `g` on `A`.

## Main results

* `Continuous.continuousOn_extend_subtypeVal`: the extension of a continuous function on `A` is
  continuous on `A`.
* `Continuous.exists_continuousOn_eq`: a continuous function on `A` with values in a nonempty
  space extends to a function continuous on `A`.
* `IsOpen.extend_subtypeVal_eventuallyEq`: near a point of an open set `A`, the extension of `g`
  agrees with every function that agrees with `g` on `A`.
-/

public section

open Function Topology

/-- Extending a continuous function on a subtype along `Subtype.val`, with any fallback, gives a
function that is continuous on the subset. -/
theorem Continuous.continuousOn_extend_subtypeVal {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {A : Set X} {g : A → Y} (hg : Continuous g) (e : X → Y) :
    ContinuousOn (extend Subtype.val g e) A := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact hg.congr fun a => (Subtype.val_injective.extend_apply g e a).symm

/-- A continuous function on a subtype of a space extends to a function that is continuous on the
subset and agrees with it there. -/
theorem Continuous.exists_continuousOn_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty Y] {A : Set X} {s : A → Y} (hs : Continuous s) :
    ∃ r : X → Y, ContinuousOn r A ∧ ∀ a : A, r a = s a :=
  ⟨extend Subtype.val s fun _ => Classical.arbitrary Y, hs.continuousOn_extend_subtypeVal _,
    Subtype.val_injective.extend_apply _ _⟩

/-- Near a point of an open set `A`, the extension of a function `g` on `A` along `Subtype.val`,
with any fallback, agrees with every function `u` that agrees with `g` on `A`. -/
theorem IsOpen.extend_subtypeVal_eventuallyEq {X Y : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) {g : A → Y} (e : X → Y) {u : X → Y} (hu : ∀ a : A, u a = g a) {x : X}
    (hx : x ∈ A) : extend Subtype.val g e =ᶠ[𝓝 x] u :=
  Filter.eventually_of_mem (hA.mem_nhds hx) fun y hy => by
    rw [hu ⟨y, hy⟩]
    exact Subtype.val_injective.extend_apply g e ⟨y, hy⟩
