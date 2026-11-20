/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Congruence of distributive Haar characters across group actions

Two elements `g : G` and `h : H` of possibly different groups acting continuously and distributively
on the same locally compact topological additive group `A` have the same distributive Haar
character whenever their actions agree pointwise on `A`.

## Main results

* `MeasureTheory.distribHaarChar_eq_of_smul_eq`: if `∀ a : A, g • a = h • a`, then
  `distribHaarChar A g = distribHaarChar A h`.
-/

public section

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Pointwise

namespace MeasureTheory

/-- If two elements of possibly different groups act continuously and distributively on the same
locally compact topological additive group `A` by the same map, then they have the same
distributive Haar character. -/
theorem distribHaarChar_eq_of_smul_eq {G H A : Type*} [Group G] [Group H] [AddCommGroup A]
    [DistribMulAction G A] [DistribMulAction H A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [ContinuousConstSMul G A] [ContinuousConstSMul H A] {g : G} {h : H}
    (hgh : ∀ a : A, g • a = h • a) :
    distribHaarChar A g = distribHaarChar A h := by
  borelize A
  let K : PositiveCompacts A := Classical.arbitrary (PositiveCompacts A)
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := addHaarMeasure K) (s := (K : Set A))
    (by simp [addHaarMeasure_self]) (by simp [addHaarMeasure_self]) ?_
  have hsmul : g • (K : Set A) = h • (K : Set A) := by
    ext x
    simp [Set.mem_smul_set, hgh]
  rw [hsmul, ← distribHaarChar_mul (addHaarMeasure K) h (K : Set A)]

end MeasureTheory
