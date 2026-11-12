/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Negation and the chosen limit

`limUnder f G` is the limit of `G` along `f` when it exists and an arbitrary fixed junk value
otherwise. Negating `G` negates the limit when it exists, and does not change the junk value when
it does not exist, since `G` and `-G` converge together. Hence vanishing of the chosen limit is
preserved by negation, with no convergence hypothesis.

## Main results

* `Filter.limUnder_neg_eq_zero`: if the chosen limit of `G` along a filter that is not trivial is
  `0`, so is that of `-G`, in a Hausdorff additive group with continuous negation.
-/

public section

open Filter Topology

/-- In a Hausdorff additive group with continuous negation, if the chosen limit of `G` along a
nontrivial filter is `0`, so is the chosen limit of `-G`. If `G` converges, `-G` converges to the
negative of the limit. Otherwise neither converges, and both chosen limits are the same junk
value. -/
theorem Filter.limUnder_neg_eq_zero {α X : Type*} [AddGroup X] [TopologicalSpace X]
    [ContinuousNeg X] [T2Space X] {f : Filter α} [f.NeBot] {G : α → X}
    (hG : limUnder f G = 0) : limUnder f (fun x ↦ -G x) = 0 := by
  by_cases hex : ∃ L, Tendsto G f (𝓝 L)
  · obtain ⟨L, hL⟩ := hex
    rw [hL.limUnder_eq] at hG
    rw [hG] at hL
    simpa using hL.neg.limUnder_eq
  · have hex' : ¬ ∃ L, Tendsto (fun x ↦ -G x) f (𝓝 L) :=
      fun ⟨L, hL⟩ ↦ hex ⟨-L, by simpa using hL.neg⟩
    rwa [limUnder_of_not_tendsto hex', ← limUnder_of_not_tendsto hex]
