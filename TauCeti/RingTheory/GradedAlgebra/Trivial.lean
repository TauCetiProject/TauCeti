/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Opposite
public import TauCeti.Algebra.Module.GradedModule.Trivial

/-!
# The trivial grading of an algebra

The trivial grading `TauCeti.trivialGrading` of `TauCeti.Algebra.Module.GradedModule.Trivial`,
concentrated in degree zero, is an internal `GradedAlgebra` when the module is an algebra.  This
file records that instance, whose decomposition and degree projection come from the module-level
file, and the graded actions of the trivially graded base ring and of the opposite of a trivially
graded algebra.  It is the canonical target grading
for augmentations of integer-graded algebras, and the grading of the coefficients in degree-zero
examples.

## Main results

* `TauCeti.instGradedAlgebraTrivialGrading`: the trivial grading of an algebra is a graded algebra.
* `TauCeti.instGradedSMulTrivialGradingOpposite`: any action of the opposite of a trivially graded
  algebra on a trivially graded module is graded.
-/

public section

open DirectSum MulOpposite

namespace TauCeti

variable (R A : Type*) [CommSemiring R]


section Algebra

variable [Semiring A] [Algebra R A]

/-- The trivial grading is an internal grading: an element is its own degree-zero component, and
all higher components vanish. -/
instance instGradedAlgebraTrivialGrading : GradedAlgebra (trivialGrading R A) where
  one_mem := by simp
  mul_mem := by
    intro p q a b ha hb
    rcases (mem_trivialGrading_iff R A).mp ha with rfl | rfl
    · rcases (mem_trivialGrading_iff R A).mp hb with rfl | rfl <;> simp
    · simp
  __ := instDecompositionTrivialGrading R A

/-- Scalar multiplication by the trivially graded base ring preserves every homogeneous piece of
an internally graded algebra. -/
instance instGradedSMulTrivialGrading (𝒜 : ℤ → Submodule R A) :
    SetLike.GradedSMul (trivialGrading R R) 𝒜 where
  smul_mem := by
    intro p q r a hr ha
    rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
    · simpa using (𝒜 q).smul_mem r ha
    · simp

/-- The opposite of a trivially graded algebra acts on a trivially graded module compatibly with
the gradings, whatever the action is: everything sits in degree zero. -/
instance instGradedSMulTrivialGradingOpposite {M : Type*} [AddCommMonoid M] [Module R M]
    [Module Aᵐᵒᵖ M] :
    SetLike.GradedSMul (InternalGrading.ofDecomposition (trivialGrading R A)).opposite.piece
      (trivialGrading R M) where
  smul_mem {i j a x} ha hx := by
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece,
      mem_trivialGrading_iff] at ha
    rw [mem_trivialGrading_iff] at hx ⊢
    rcases ha with rfl | ha
    · rcases hx with rfl | rfl <;> simp
    · right
      rw [← op_unop a, ha]
      simp


end Algebra

end TauCeti
