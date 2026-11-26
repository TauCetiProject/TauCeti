/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Points of finite order are dense in the circle

The points of finite order of the circle group are the rational rotations `exp (2π i q)`,
`q ∈ ℚ` (`Circle.isOfFinOrder_exp_two_pi_mul_iff`). Since the rationals are dense in the real
line and `x ↦ exp (2π i x)` is a continuous surjection onto the circle, they are dense
(`Circle.dense_setOf_isOfFinOrder`). Coordinatewise, the points of finite order of a finite power
of the circle are dense too (`Circle.dense_setOf_isOfFinOrder_pi`): an element of a finite product
has finite order as soon as each coordinate has.

Density of the points of finite order is what lets one test a closed condition on a torus at its
points of finite order only. For instance, a closed subgroup containing every point of finite order
of a torus contains the whole torus.

## Main results

* `Circle.dense_setOf_isOfFinOrder`: the points of finite order of the circle are dense.
* `Circle.dense_setOf_isOfFinOrder_pi`: the points of finite order of a finite power of the circle
  are dense.
-/

public section

open Set

namespace Circle

/-- **Rational rotations are dense.** The points of finite order of the circle group, the rotations
`exp (2π i q)` by rational `q`, are dense in the circle. -/
theorem dense_setOf_isOfFinOrder : Dense {c : Circle | IsOfFinOrder c} := by
  -- `q ↦ exp (2π i q)` has dense range: `ℚ` is dense in `ℝ`, and `x ↦ exp (2π i x)` is a
  -- continuous surjection.
  have hsurj : Function.Surjective fun x : ℝ ↦ exp (2 * Real.pi * x) := fun c ↦ by
    obtain ⟨y, rfl⟩ := exp_surjective c
    exact ⟨y / (2 * Real.pi), by field_simp⟩
  have hd : DenseRange fun q : ℚ ↦ exp (2 * Real.pi * q) :=
    hsurj.denseRange.comp Rat.denseRange_cast (by fun_prop)
  exact hd.mono (range_subset_iff.2 fun q ↦
    isOfFinOrder_exp_two_pi_mul_iff.2 (Rat.not_irrational q))

/-- **Points of finite order are dense in a finite power of the circle.** -/
theorem dense_setOf_isOfFinOrder_pi {ι : Type*} [Finite ι] :
    Dense {c : ι → Circle | IsOfFinOrder c} :=
  (dense_pi univ fun _ _ ↦ dense_setOf_isOfFinOrder).mono fun _ hc ↦
    IsOfFinOrder.pi fun i ↦ mem_univ_pi.1 hc i

end Circle
