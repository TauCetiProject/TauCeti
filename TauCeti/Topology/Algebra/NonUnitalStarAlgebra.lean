/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.NonUnitalSubalgebra

/-!
# Topological facts about nonunital star subalgebras

This file provides the `@[simp]` lemma `NonUnitalStarSubalgebra.topologicalClosure_coe`
identifying the underlying set of `s.topologicalClosure` with `closure (s : Set A)`, matching
`StarSubalgebra.topologicalClosure_coe`, and shows that the star subalgebra `L ∩ star L` of a
closed left ideal `L` is closed, `Submodule.isClosed_interStar`.
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

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Star R] [NonUnitalNonAssocSemiring A] [StarRing A]
  [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A]
  {L : Submodule R A} {hL : ∀ (a : A) {x : A}, x ∈ L → a * x ∈ L}

/-- For a closed left ideal `L`, the star subalgebra `L ∩ star L` is closed. -/
theorem isClosed_interStar (hLc : IsClosed (L : Set A)) : IsClosed (L.interStar hL : Set A) :=
  coe_interStar (hL := hL) ▸ hLc.inter (hLc.preimage continuous_star)

end Submodule
