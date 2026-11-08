/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Closures, closed images, and pointwise quotients

Mathlib relates `closure` to a pointwise product when one factor is *open* — `IsOpen.mul_closure`
and its neighbours in `Mathlib/Topology/Algebra/Group/Pointwise.lean` — and to a pointwise scalar
product when the action is jointly continuous, in `smul_set_closure_subset`. The containment for
division, which needs neither openness nor a group structure, is not there.

It is what a Baire argument needs. Such an argument produces a set whose *closure* has interior,
and the step from there to a neighbourhood of the identity runs through `D / D` for that closure
`D`; without this containment there is no way back from `closure s / closure t` to a closure.

Multiplication and addition carry a closed relation to a closed set if its second coordinate
lies in a compact set. This applies to bounded displacements in proper normed spaces, even when
the first coordinate ranges over a noncompact set.

## Main results

* `TauCeti.closure_div_closure_subset`, with its additive form
  `TauCeti.closure_sub_closure_subset`.
* `IsClosed.image_mul_of_snd_subset`, with its additive form
  `IsClosed.image_add_of_snd_subset`.
-/

public section

open Set Pointwise

namespace TauCeti

variable {G : Type*} [TopologicalSpace G] [Div G] [ContinuousDiv G]

/-- **Division carries closures into the closure of the quotient.** Neither set need be open,
unlike in the `IsOpen.mul_closure` family, and `G` need only carry a continuous division — no
group structure, and in particular no inverse. -/
@[to_additive /-- **Subtraction carries closures into the closure of the difference.** Neither set
need be open, and `G` need only carry a continuous subtraction — no group structure, and in
particular no negation. -/]
theorem closure_div_closure_subset (s t : Set G) : closure s / closure t ⊆ closure (s / t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    map_mem_closure₂ continuous_div' ha hb fun _ hx _ hy ↦ div_mem_div hx hy

end TauCeti

/-- The products of a closed relation form a closed set if the second coordinate is contained
in a compact set. -/
@[to_additive /-- The sums of a closed relation form a closed set if the second coordinate is
contained in a compact set. -/]
theorem IsClosed.image_mul_of_snd_subset {G : Type*} [TopologicalSpace G]
    [Group G] [ContinuousDiv G] {s : Set (G × G)} (hs : IsClosed s)
    {C : Set G} (hC : IsCompact C) (hsub : Prod.snd '' s ⊆ C) :
    IsClosed ((fun p : G × G ↦ p.1 * p.2) '' s) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  convert isClosedMap_fst_of_compactSpace _
    (hs.preimage (f := fun p : G × C ↦ (p.1 / p.2, (p.2 : G))) (by fun_prop)) using 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1 * p.2, ⟨p.2, hsub ⟨p, hp, rfl⟩⟩), by simpa, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(p.1 / p.2, p.2), hp, by simp⟩

end
