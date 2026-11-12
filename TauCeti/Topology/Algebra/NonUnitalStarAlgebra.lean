/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# Carrier of the topological closure of a nonunital star subalgebra

This file provides the `@[simp]` lemma `NonUnitalStarSubalgebra.topologicalClosure_coe`
identifying the underlying set of `s.topologicalClosure` with `closure (s : Set A)`, matching
`StarSubalgebra.topologicalClosure_coe`.
-/

public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
  [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
  [ContinuousConstSMul R A] [IsSemitopologicalSemiring A]

/-- Coercing `s.topologicalClosure` to `Set A` gives the topological closure
`closure (s : Set A)`. -/
@[simp]
theorem topologicalClosure_coe (s : NonUnitalStarSubalgebra R A) :
    (s.topologicalClosure : Set A) = _root_.closure (s : Set A) :=
  (rfl)

end NonUnitalStarSubalgebra
