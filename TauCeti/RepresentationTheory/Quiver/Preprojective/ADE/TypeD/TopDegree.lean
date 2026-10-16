/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.ForkTopPower
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Corner
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic

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

private theorem signlessArrow_mem_grade_one {i j : Fin (DynkinType.D n).rank}
    (h : (DG).Adj i j) :
    signlessArrow k DG i j ∈ signlessPreprojectiveGrade k Q 1 := by
  rw [signlessArrow_of_adj k h]
  exact signlessPreprojectiveMk_mem_grade k Q (ofArrow_mem_grade_one _)

private theorem forkBacktrack_mem_grade_two (hn : 3 ≤ n) (l : Bool) :
    signlessPreprojectiveDForkBacktrack (n := n) k l ∈
      signlessPreprojectiveGrade k Q 2 := by
  let c' : Fin (DynkinType.D n).rank :=
    ⟨n - 3, by rw [DynkinType.rank_D]; omega⟩
  let l₁ : Fin (DynkinType.D n).rank :=
    ⟨n - 3 + 1, by rw [DynkinType.rank_D]; omega⟩
  let l₂ : Fin (DynkinType.D n).rank :=
    ⟨n - 3 + 2, by rw [DynkinType.rank_D]; omega⟩
  have h₁ : (DG).Adj l₁ c' := (diagramGraph_D_adj hn l₁ c').2 (by
    dsimp only [l₁, c']
    omega)
  have h₂ : (DG).Adj l₂ c' := (diagramGraph_D_adj hn l₂ c').2 (by
    dsimp only [l₂, c']
    omega)
  cases l with
  | false =>
      rw [signlessPreprojectiveDForkBacktrack_false]
      change signlessArrow k DG l₂ c' * signlessArrow k DG c' l₂ ∈ _
      simpa using mul_mem_signlessPreprojectiveGrade k Q
        (signlessArrow_mem_grade_one k h₂)
        (signlessArrow_mem_grade_one k h₂.symm)
  | true =>
      rw [signlessPreprojectiveDForkBacktrack_true]
      change signlessArrow k DG l₁ c' * signlessArrow k DG c' l₁ ∈ _
      simpa using mul_mem_signlessPreprojectiveGrade k Q
        (signlessArrow_mem_grade_one k h₁)
        (signlessArrow_mem_grade_one k h₁.symm)

/-- The terminal alternating fork word of `Dₙ` is homogeneous of path degree `2n - 4`. -/
theorem signlessPreprojectiveDForkTopWord_mem_grade (hn : 3 ≤ n) :
    signlessPreprojectiveDForkWords k hn (.inr ()) ∈
      signlessPreprojectiveGrade k Q (2 * n - 4) := by
  rw [signlessPreprojectiveDForkTopWord_eq k hn]
  have hx := forkBacktrack_mem_grade_two (n := n) k hn true
  have hy := forkBacktrack_mem_grade_two (n := n) k hn false
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
      signlessPreprojectiveMk k Q (ofPath p) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨y, hy, hytop⟩ :=
    (mem_signlessPreprojectiveGrade_iff k Q).1
      (signlessPreprojectiveDForkTopWord_mem_grade k hn)
  rw [grade_eq_span_range] at hy
  have hyzero : signlessPreprojectiveMk k Q y = 0 := by
    refine Submodule.span_induction (p := fun z _ => signlessPreprojectiveMk k Q z = 0)
      (fun z hz => ?_) (map_zero _) (fun x y _ _ hx hy => by rw [map_add, hx, hy, add_zero])
      (fun a x _ hx => by rw [map_smul, hx, smul_zero]) hy
    obtain ⟨⟨p, hp⟩, rfl⟩ := hz
    exact h p hp
  exact signlessPreprojectiveDForkTopWord_ne_zero k hn (hytop ▸ hyzero)

end Field

end TauCeti
