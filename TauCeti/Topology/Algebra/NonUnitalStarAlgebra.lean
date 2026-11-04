/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Left ideal absorption on topological closures of nonunital star subalgebras

In a semitopological nonunital star algebra `A`, separate continuity of multiplication passes left
ideal absorption from a dense subset of `A` and a nonunital star subalgebra `I` to all of `A` and
`I.topologicalClosure`.

## Main results

* `NonUnitalStarSubalgebra.mul_mem_topologicalClosure_of_dense`: if a dense subset of `A`
  multiplies `I` on the left into `I.topologicalClosure`, then all of `A` multiplies
  `I.topologicalClosure` on the left into `I.topologicalClosure`.
* `NonUnitalStarSubalgebra.mul_mem_topologicalClosure`: the topological closure of a left star
  ideal in a semitopological star algebra is closed under left multiplication by `A`.
-/

public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [NonUnitalSemiring A] [Module R A]
  [Star A] [ContinuousStar A] [ContinuousConstSMul R A] [IsSemitopologicalSemiring A]
  (I : NonUnitalStarSubalgebra R A)

/-- If a dense subset `s` of `A` multiplies `I` on the left into `I.topologicalClosure`, then all
of `A` multiplies `I.topologicalClosure` on the left into `I.topologicalClosure`. -/
theorem mul_mem_topologicalClosure_of_dense {s : Set A} (hs : Dense s)
    (hmul : ∀ a ∈ s, ∀ x ∈ I, a * x ∈ I.topologicalClosure) (a : A) {x : A}
    (hx : x ∈ I.topologicalClosure) : a * x ∈ I.topologicalClosure := by
  have hsI : ∀ b ∈ s, ∀ y ∈ I.topologicalClosure, b * y ∈ I.topologicalClosure := fun b hb _ hy =>
    (I.isClosed_topologicalClosure.preimage (continuous_const_mul b)).closure_subset_iff.2
      (hmul b hb) hy
  exact (I.isClosed_topologicalClosure.preimage (continuous_mul_const x)).closure_subset_iff.2
    (fun b hb => hsI b hb x hx) (hs a)

/-- The topological closure of a left star ideal in a semitopological star algebra is again closed
under left multiplication by ambient elements. -/
theorem mul_mem_topologicalClosure (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) {x : A}
    (hx : x ∈ I.topologicalClosure) : a * x ∈ I.topologicalClosure :=
  I.mul_mem_topologicalClosure_of_dense dense_univ
    (fun b _ y hy => I.le_topologicalClosure (hmul b y hy)) a hx

end NonUnitalStarSubalgebra
