/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The maximal pro-`p` quotient of the topological abelianization

Combining the universal properties of the topological abelianization and of the maximal pro-`p`
quotient: a continuous homomorphism from a topological group `G` to a commutative profinite
pro-`p` group factors through `TopologicalAbelianization G` and then through its maximal pro-`p`
quotient `G^ab(p)`. Hence it kills every element of `G` whose class in `G^ab(p)` is trivial.

## Main results

* `TauCeti.eq_one_of_maximalProPQuotient_mk_eq_one`: every continuous homomorphism to a
  commutative pro-`p` group kills the elements that die in the maximal pro-`p` abelian quotient.
-/

public section

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T1Space A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- Every continuous homomorphism from `G` to a commutative pro-`p` group kills the elements
that die in the maximal pro-`p` quotient of the topological abelianization of `G`. -/
theorem eq_one_of_maximalProPQuotient_mk_eq_one (hA : IsProP p A) (f : G →ₜ* A) {g : G}
    (hg : maximalProPQuotient.mk p (TopologicalAbelianization G)
      (g : TopologicalAbelianization G) = 1) : f g = 1 := by
  let fab := TopologicalAbelianization.lift f
  have h := congrArg (maximalProPQuotient.lift hA fab.toMonoidHom fab.continuous) hg
  rw [maximalProPQuotient.mk_apply, maximalProPQuotient.lift_mk, map_one] at h
  exact (TopologicalAbelianization.lift_mk f g).symm.trans h

end TauCeti
