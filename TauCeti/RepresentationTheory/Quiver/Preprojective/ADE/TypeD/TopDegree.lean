/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.ForkTopPower
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Corner

/-!
# The top surviving degree of the type-`D` preprojective algebra

For `n ≥ 3`, the terminal alternating word at the fork of the signless preprojective algebra
of `Dₙ` is homogeneous of path degree `2n - 4`, two less than the Coxeter number
`h = 2n - 2`. Since the fork word is nonzero over every field, the degree-`2n - 4` piece and
the corresponding fork corner are nonzero. In particular, an actual path of that length in
the diagram survives the preprojective quotient.

This supplies the lower half of the sharp top-degree calculation. The complementary assertion
that every path of length at least `2n - 3` vanishes is separate; the current general type-`D`
reduction only gives the coarser bound `4n`.

The terminal fork word and its nonvanishing are proved in
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.ForkTopPower`. The grading and
path-spanning description of graded corners come from
`TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Corner`.

## References

* C. M. Ringel, *The preprojective algebra of a quiver*, for the top degree of a finite-Dynkin
  preprojective algebra.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Q" => DoubledQuiver DG
local notation "c" => n - 3

attribute [local instance] signlessPreprojectiveGradedAlgebra

private theorem forkBacktrack_mem_grade_two (l : Bool) :
    signlessPreprojectiveDForkBacktrack (n := n) k l ∈
      signlessPreprojectiveGrade k Q 2 := by
  cases l
  · rw [signlessPreprojectiveDForkBacktrack_false]
    exact mul_mem_signlessPreprojectiveGrade k Q
      (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)
      (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)
  · rw [signlessPreprojectiveDForkBacktrack_true]
    exact mul_mem_signlessPreprojectiveGrade k Q
      (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)
      (signlessArrow_mem_signlessPreprojectiveGrade_one k _ _)

/-- The terminal alternating fork word of `Dₙ` is homogeneous of path degree `2n - 4`. -/
theorem signlessPreprojectiveDForkTopWord_mem_grade (hn : 3 ≤ n) :
    signlessPreprojectiveDForkWords k hn (.inr ()) ∈
      signlessPreprojectiveGrade k Q (2 * n - 4) := by
  rw [signlessPreprojectiveDForkTopWord_eq k hn]
  have hx := forkBacktrack_mem_grade_two (n := n) k true
  have hy := forkBacktrack_mem_grade_two (n := n) k false
  have hs : signlessPreprojectiveDForkBacktrack (n := n) k true +
      signlessPreprojectiveDForkBacktrack (n := n) k false ∈
        signlessPreprojectiveGrade k Q 2 := add_mem hx hy
  have hp := SetLike.pow_mem_graded c hs
  have hdegree : 2 + c • 2 = 2 * n - 4 := by
    rw [Nat.nsmul_eq_mul]
    have : n = c + 3 := by omega
    omega
  exact hdegree ▸ SetLike.mul_mem_graded hx hp

/-- The terminal fork word belongs to the degree-`2n - 4` corner at the fork vertex. -/
theorem signlessPreprojectiveDForkTopWord_mem_corner (hn : 3 ≤ n) :
    signlessPreprojectiveDForkWords k hn (.inr ()) ∈
      signlessPreprojectiveCorner k Q (2 * n - 4)
        (vertex DG (preprojectiveDForkVertex n hn))
        (vertex DG (preprojectiveDForkVertex n hn)) := by
  rw [mem_signlessPreprojectiveCorner_iff]
  refine ⟨signlessPreprojectiveDForkTopWord_mem_grade k hn, ?_⟩
  have hid : IsIdempotentElem (signlessPreprojectiveMk k Q
      (vertexIdempotent k (vertex DG (preprojectiveDForkVertex n hn)))) :=
    IsIdempotentElem.map
      (vertexIdempotent_mul_self (k := k) (vertex DG (preprojectiveDForkVertex n hn)))
      (signlessPreprojectiveMk k Q)
  exact (mem_cornerSubmodule_iff k hid hid).1
    (signlessPreprojectiveDForkWords_mem_cornerSubmodule k hn (.inr ()))

end CommRing

section Field

variable (k : Type*) [Field k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Q" => DoubledQuiver DG

/-- The path-degree `2n - 4` piece of the signless preprojective algebra of `Dₙ` is nonzero. -/
theorem signlessPreprojectiveGrade_D_top_ne_bot (hn : 3 ≤ n) :
    signlessPreprojectiveGrade k Q (2 * n - 4) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨signlessPreprojectiveDForkWords k hn (.inr ()),
    signlessPreprojectiveDForkTopWord_mem_grade k hn,
    signlessPreprojectiveDForkTopWord_ne_zero k hn⟩

/-- The degree-`2n - 4` corner at the fork of the signless preprojective algebra of `Dₙ`
is nonzero. -/
theorem signlessPreprojectiveCorner_D_fork_top_ne_bot (hn : 3 ≤ n) :
    signlessPreprojectiveCorner k Q (2 * n - 4)
      (vertex DG (preprojectiveDForkVertex n hn))
      (vertex DG (preprojectiveDForkVertex n hn)) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨signlessPreprojectiveDForkWords k hn (.inr ()),
    signlessPreprojectiveDForkTopWord_mem_corner k hn,
    signlessPreprojectiveDForkTopWord_ne_zero k hn⟩

/-- An actual path of length `2n - 4` survives in the signless preprojective algebra of `Dₙ`. -/
theorem exists_signlessPreprojectiveMk_D_path_top_ne_zero (hn : 3 ≤ n) :
    ∃ p : Quiver.TotalPath Q, p.2.2.length = 2 * n - 4 ∧
      signlessPreprojectiveMk k Q (ofPath p) ≠ 0 :=
  exists_signlessPreprojectiveMk_ofPath_ne_zero_of_ne_bot k Q
    (signlessPreprojectiveGrade_D_top_ne_bot k hn)

end Field

end TauCeti
