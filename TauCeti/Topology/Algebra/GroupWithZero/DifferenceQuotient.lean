/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Continuity of difference quotients at an isolated point

The difference quotient `(f x - f μ) / (x - μ)` of a function `f` continuous on a set `S` is
continuous on `S` as soon as `μ` is an isolated point of `S` or does not lie in its closure: away
from `μ` it is a quotient by a nonzero continuous function, and near `μ` the set `S` is the single
point `μ`.

## Main results

* `ContinuousOn.sub_div_sub_of_eventually_imp_eq`: the difference quotient of a function continuous
  on a set `S` at a point `μ` that is not an accumulation point of `S` is continuous on `S`.
-/

public section

open Filter Topology

/-- The difference quotient `(f x - f μ) / (x - μ)` of a function `f` continuous on a set `S` is
continuous on `S` as soon as no point of `S` other than `μ` lies near `μ`, that is, when `μ` is an
isolated point of `S` or does not lie in its closure. -/
theorem ContinuousOn.sub_div_sub_of_eventually_imp_eq {R : Type*} [Field R] [TopologicalSpace R]
    [ContinuousMul R] [ContinuousSub R] [ContinuousInv₀ R] {f : R → R} {S : Set R} {μ : R}
    (hf : ContinuousOn f S) (hμ : ∀ᶠ x in 𝓝 μ, x ∈ S → x = μ) :
    ContinuousOn (fun x ↦ (f x - f μ) / (x - μ)) S := by
  intro x hx
  rcases eq_or_ne x μ with rfl | hxμ
  · -- Near `x = μ` the set `S` is the single point `μ`.
    have hpure : 𝓝[S] x ≤ pure x := by
      rw [le_pure_iff, mem_nhdsWithin_iff_eventually]
      exact hμ
    exact (tendsto_pure_nhds _ x).mono_left hpure
  · exact ((hf x hx).sub continuousWithinAt_const).div
      (continuousWithinAt_id.sub continuousWithinAt_const) (sub_ne_zero.2 hxμ)
