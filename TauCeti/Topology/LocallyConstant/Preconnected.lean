/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Locally constant functions on a preconnected set

A function that is locally constant along a preconnected set takes the same value everywhere on
it. Mathlib's `IsLocallyConstant.apply_eq_of_preconnectedSpace` says this for a locally constant
function on a preconnected *space*; the statement below is the relative form, for a preconnected
subset `s` of an ambient space, with local constancy expressed by the `𝓝[s]` neighbourhood filter
rather than by passing to the subtype.

## Main declarations

* `IsPreconnected.apply_eq_of_eventually_eq`: a function whose value is locally constant along a
  preconnected set is constant along it.

The example at the end of the file spells the statement out on the interval `[0, 1] ⊆ ℝ`, where it
says that a map into a discrete space continuous on `[0, 1]` cannot take two different values
there. That is the obstruction to extending a discrete-valued map off a closed subspace of a
space that is not totally disconnected.
-/

public section

open Filter Topology

namespace IsPreconnected

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A function that is locally constant along a preconnected set is constant along it.

This is `IsLocallyConstant.apply_eq_of_preconnectedSpace` transported to the subspace `s`, and
the special case of `IsPreconnected.induction₂` for the relation `f y = f x`. -/
theorem apply_eq_of_eventually_eq {Y : Type*} {f : X → Y} (hs : IsPreconnected s)
    (hf : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, f u = f t) {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b :=
  hs.induction₂ (fun x y => f y = f x) hf (fun _ _ _ _ _ _ hxy hyz => hyz.trans hxy)
    (fun _ _ _ _ => Eq.symm) hb ha

end IsPreconnected

/-- On the preconnected set `[0, 1] ⊆ ℝ`, a map into a discrete space that is continuous there
takes the same value at `0` and at `1`; continuity on a discrete-valued map is local constancy. -/
example {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {a b : Y} (hab : a ≠ b) :
    ¬ ∃ g : ℝ → Y, ContinuousOn g (Set.Icc 0 1) ∧ g 0 = a ∧ g 1 = b := by
  rintro ⟨g, hg, rfl, rfl⟩
  -- The singleton `{g t}` is open, so its preimage is a neighbourhood of `t` within `[0, 1]`.
  have h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ u in 𝓝[Set.Icc (0 : ℝ) 1] t, g u = g t := fun t ht =>
    (hg t ht).preimage_mem_nhdsWithin ((isOpen_discrete {g t}).mem_nhds rfl)
  exact hab (isPreconnected_Icc.apply_eq_of_eventually_eq h (by norm_num) (by norm_num))
