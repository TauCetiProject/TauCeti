/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Trivial
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# The trivial grading of an algebra

The trivial grading `TauCeti.trivialGrading` of `TauCeti.Algebra.Module.GradedModule.Trivial`,
concentrated in degree zero, is an internal `GradedAlgebra` when the module is an algebra.  This
file records that instance, whose decomposition and degree projection come from the module-level
file.  This grading is the canonical target for augmentations of integer-graded algebras and the
grading of coefficients in degree-zero examples.

## Main results

* `TauCeti.instGradedAlgebraTrivialGrading`: the trivial grading of an algebra is a graded algebra.
* `TauCeti.isHomogeneous_algebraLinearMap`: the unit map `Algebra.linearMap R A` is homogeneous of
  degree zero into any family satisfying `SetLike.GradedOne`.
-/

public section

namespace TauCeti

section Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/-- The trivial grading is an internal grading: an element is its own degree-zero component, and
all nonzero-degree components vanish. -/
instance instGradedAlgebraTrivialGrading : GradedAlgebra (trivialGrading R A) where
  one_mem := by simp
  mul_mem := by
    intro p q a b ha hb
    rcases (mem_trivialGrading_iff R A).mp ha with rfl | rfl
    · rcases (mem_trivialGrading_iff R A).mp hb with rfl | rfl <;> simp
    · simp
  __ := instDecompositionTrivialGrading R A

/-- The unit map `Algebra.linearMap R A` of an `R`-algebra with a family of submodules containing
`1` in degree zero is homogeneous of degree zero from the trivial grading of `R`. -/
theorem isHomogeneous_algebraLinearMap {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [SetLike.GradedOne 𝒜] :
    TauCeti.LinearMap.IsHomogeneous (Algebra.linearMap R A) (trivialGrading R R) 𝒜 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p r hr
  rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
  · rw [zero_add, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact (𝒜 0).smul_mem r (SetLike.one_mem_graded 𝒜)
  · simp

end Algebra

end TauCeti
