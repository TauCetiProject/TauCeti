/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Algebraic operations on smooth maps

This file complements Mathlib's algebraic structures on spaces of smooth maps with the pointwise
evaluation of finite sums.

## Main results

* `ContMDiffMap.coe_sum`: the coercion of a finite sum of smooth maps is the sum of the coercions.
-/

public section

open scoped ContDiff Manifold

namespace ContMDiffMap

/-- The coercion of a finite sum of smooth maps into a commutative additive Lie group is the
pointwise sum. -/
@[simp]
theorem coe_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
    {G : Type*} [AddCommMonoid G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffAdd I' n G]
    {ι : Type*} (s : Finset ι) (f : ι → C^n⟮I, N; I', G⟯) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum coeFnAddMonoidHom f s

end ContMDiffMap
