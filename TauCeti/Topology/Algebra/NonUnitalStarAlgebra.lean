/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.Subalgebra

/-!
# Topological closure and closed corner subalgebras of nonunital star subalgebras

This file provides `NonUnitalStarSubalgebra.topologicalClosure_coe` identifying the underlying set
of `s.topologicalClosure` with `closure (s : Set A)`, matching
`StarSubalgebra.topologicalClosure_coe`, as well as `IsClosed` instances for the fixed corner
`s.corner hp` and orthogonal corner `s.orthoCorner hp` of a closed nonunital star subalgebra.
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

section Corner
variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A] [T2Space A] [ContinuousMul A]
/-- The fixed corner `s.corner hp` of a closed nonunital `⋆`-subalgebra is closed. -/
instance isClosed_corner (s : NonUnitalStarSubalgebra R A) [hs : IsClosed (s : Set A)]
    {p : A} (hp : IsSelfAdjoint p) : IsClosed (s.corner hp : Set A) :=
  coe_corner s hp ▸ hs.and ((isClosed_eq (continuous_const.mul continuous_id) continuous_id).and
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id))
/-- The orthogonal corner `s.orthoCorner hp` of a closed nonunital `⋆`-subalgebra is closed. -/
instance isClosed_orthoCorner (s : NonUnitalStarSubalgebra R A) [hs : IsClosed (s : Set A)]
    {p : A} (hp : IsSelfAdjoint p) : IsClosed (s.orthoCorner hp : Set A) :=
  coe_orthoCorner s hp ▸ hs.and ((isClosed_eq (continuous_const.mul continuous_id)
    continuous_const).and (isClosed_eq (continuous_id.mul continuous_const) continuous_const))
end Corner
end NonUnitalStarSubalgebra
