/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading

/-!
# The path-length grading of the signless preprojective algebra

The signless backtrack relators have degree two. Their two-sided ideal is therefore homogeneous,
so the path grading descends to the signless quotient. In particular, the positive-degree part
can be used as the kernel of a vertex augmentation in its Koszul complex.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) (R : Type u) [CommRing k] [Quiver.{v} R] [HasReverse R]
  [Finite R] [∀ x : R, Fintype (Quiver.Star x)]

/-- The signless preprojective ideal is homogeneous for path length: every defining relator
has degree two. -/
theorem isHomogeneous_signlessPreprojectiveIdeal :
    (signlessPreprojectiveIdeal k R).asIdeal.IsHomogeneous (grade k R) := by
  rw [signlessPreprojectiveIdeal_eq_span]
  refine TwoSidedIdeal.homogeneous_span _ fun x hx => ?_
  obtain ⟨v, rfl⟩ := hx
  exact ⟨2, signlessPreprojectiveRelator_mem_grade_two k v⟩

/-- The degree-`n` piece of the signless preprojective algebra, induced from the path algebra. -/
noncomputable def signlessPreprojectiveGrade (n : ℕ) :
    Submodule k (signlessPreprojectiveAlgebra k R) :=
  TauCeti.GradedAlgebra.quotientPiece (grade k R) (signlessPreprojectiveIdeal k R).asIdeal n

/-- A class of a homogeneous path-algebra element belongs to its induced graded piece. -/
theorem signlessPreprojectiveMk_mem_grade {n : ℕ} {y : pathAlgebra k R}
    (hy : y ∈ grade k R n) :
    signlessPreprojectiveMk k R y ∈ signlessPreprojectiveGrade k R n := by
  rw [signlessPreprojectiveGrade, signlessPreprojectiveMk_apply]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _ hy

/-- Membership in the induced graded piece is represented by a homogeneous path-algebra
element. -/
@[simp]
theorem mem_signlessPreprojectiveGrade_iff {n : ℕ} {x : signlessPreprojectiveAlgebra k R} :
    x ∈ signlessPreprojectiveGrade k R n ↔
      ∃ y ∈ grade k R n, signlessPreprojectiveMk k R y = x := by
  rw [signlessPreprojectiveGrade, TauCeti.GradedAlgebra.mem_quotientPiece_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, signlessPreprojectiveMk_apply k R y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (signlessPreprojectiveMk_apply k R y).symm⟩

/-- The signless quotient is the internal direct sum of its path-length pieces. -/
theorem isInternal_signlessPreprojectiveGrade :
    DirectSum.IsInternal (signlessPreprojectiveGrade k R) :=
  TauCeti.GradedAlgebra.isInternal_quotientPiece (grade k R)
    (signlessPreprojectiveIdeal k R).asIdeal (isHomogeneous_signlessPreprojectiveIdeal k R)

/-- Multiplication adds path lengths in the signless preprojective algebra. -/
theorem mul_mem_signlessPreprojectiveGrade {m n : ℕ}
    {x y : signlessPreprojectiveAlgebra k R}
    (hx : x ∈ signlessPreprojectiveGrade k R m)
    (hy : y ∈ signlessPreprojectiveGrade k R n) :
    x * y ∈ signlessPreprojectiveGrade k R (m + n) :=
  TauCeti.GradedAlgebra.mul_mem_quotientPiece _ _ hx hy

/-- The signless preprojective algebra, equipped with its induced path-length grading. -/
@[instance_reducible]
noncomputable def signlessPreprojectiveGradedAlgebra :
    GradedAlgebra (signlessPreprojectiveGrade k R) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece (grade k R)
    (signlessPreprojectiveIdeal k R).asIdeal (isHomogeneous_signlessPreprojectiveIdeal k R)

/-- Left multiplication by an arrow lands in the positive-degree part of the signless quotient. -/
theorem signlessPreprojectiveMk_ofArrow_mul_mem_iSup {i j : R} (b : i ⟶ j)
    (z : signlessPreprojectiveAlgebra k R) :
    signlessPreprojectiveMk k R (ofArrow b) * z ∈
      ⨆ n, signlessPreprojectiveGrade k R (n + 1) := by
  have hz : z ∈ ⨆ n, signlessPreprojectiveGrade k R n := by
    rw [(isInternal_signlessPreprojectiveGrade k R).submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction (motive := fun z =>
      signlessPreprojectiveMk k R (ofArrow b) * z ∈
        ⨆ n, signlessPreprojectiveGrade k R (n + 1)) _ hz
    (fun n z hz => ?_) (by rw [mul_zero]; exact zero_mem _)
    fun z z' hz hz' => by rw [mul_add]; exact add_mem hz hz'
  refine Submodule.mem_iSup_of_mem n ?_
  rw [add_comm]
  exact mul_mem_signlessPreprojectiveGrade k R
    (signlessPreprojectiveMk_mem_grade k R (ofArrow_mem_grade_one b)) hz

end TauCeti
