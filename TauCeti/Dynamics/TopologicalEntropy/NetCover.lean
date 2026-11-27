/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Maximal dynamical nets are dynamical covers

A `(U, n)`-dynamical net of `F` of maximal cardinality is a `(U ○ U, n)`-dynamical cover of `F`
(`Dynamics.IsDynNetIn.isDynCoverOf_comp`). This is the argument of Mathlib's
`Dynamics.coverMincard_le_netMaxcard`, stated for the net itself so that weighted sums over the net
(as in topological pressure) can be compared with weighted sums over covers.
-/

public section

namespace Dynamics

open Set
open scoped SetRel

variable {X : Type*} {T : X → X} {U : SetRel X X} {n : ℕ}

/-- **Maximal nets are covers.** A `(U, n)`-dynamical net of `F` of maximal cardinality is a
`(U ○ U, n)`-dynamical cover of `F`. The proof is the argument of Mathlib's
`Dynamics.coverMincard_le_netMaxcard`: a point left uncovered could be added to the net. -/
theorem IsDynNetIn.isDynCoverOf_comp {F : Set X} [U.IsRefl] [U.IsSymm]
    {s : Finset X} (s_net : IsDynNetIn T F U n s) (s_card : (s.card : ℕ∞) = netMaxcard T F U n) :
    IsDynCoverOf T F (U ○ U) n s := by
  classical
  -- If `s` is not a cover, then we can add to `s` a point `x` which is not covered
  -- and get a new net. This contradicts the maximality of `s`.
  rw [IsDynCoverOf, SetRel.isCover_iff_subset_iUnion_ball]
  by_contra hcov
  obtain ⟨x, x_F, x_uncov⟩ := not_subset.1 hcov
  simp only [Finset.mem_coe, mem_iUnion, exists_prop, not_exists, not_and] at x_uncov
  have larger_net : IsDynNetIn T F U n (insert x s) := by
    refine ⟨insert_subset x_F s_net.1, pairwiseDisjoint_insert.2 ⟨s_net.2, ?_⟩⟩
    refine fun y y_s _ ↦ disjoint_left.2 fun z z_x z_y ↦ x_uncov y y_s ?_
    exact mem_ball_dynEntourage_comp T n x y (nonempty_of_mem ⟨z_x, z_y⟩)
  rw [← s.coe_insert x] at larger_net
  apply larger_net.card_le_netMaxcard.not_gt
  rw [← s_card, Nat.cast_lt]
  refine (lt_add_one s.card).trans_eq (s.card_insert_of_notMem fun x_s ↦ ?_).symm
  exact x_uncov x x_s (SetRel.ball_mono (dynEntourage_monotone T n SetRel.left_subset_comp) x <|
    SetRel.rfl (dynEntourage T U n))

end Dynamics
