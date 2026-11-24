/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# A graded symmetric-algebra presentation of a polynomial ring

The free module on the variables presents a multivariate polynomial algebra as a graded
quotient of its symmetric algebra. The presentation sends each free generator to the
corresponding variable and preserves the total-degree grading.
-/

public section

namespace MvPolynomial

attribute [local instance] gradedAlgebra

universe u v

variable (R : Type u) (σ : Type v) [CommSemiring R]

/-- The graded presentation sending each free module generator to its polynomial variable. -/
noncomputable def symmetricPresentation :
    TauCeti.SymmetricAlgebra.homogeneousSubmodule R (σ →₀ R) →+*ᵍ homogeneousSubmodule σ R :=
  SymmetricAlgebra.gradedLift R (homogeneousSubmodule σ R)
    (Finsupp.linearCombination R fun i : σ ↦
      (⟨X i, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)⟩ :
        homogeneousSubmodule σ R 1))

/-- The symmetric-algebra presentation generates every polynomial. -/
theorem symmetricPresentation_surjective : Function.Surjective (symmetricPresentation R σ) := by
  apply SymmetricAlgebra.gradedLift_surjective
  apply top_unique
  rw [← adjoin_range_X (R := R) (σ := σ)]
  apply Algebra.adjoin_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Finsupp.single i 1, by simp⟩

/-- A free module generator maps to the variable with the same index. -/
@[simp]
theorem symmetricPresentation_ι_single (i : σ) :
    symmetricPresentation R σ (SymmetricAlgebra.ι R (σ →₀ R) (Finsupp.single i 1)) = X i := by
  simp [symmetricPresentation]

/-- The graded symmetric-algebra presentation fixes the coefficient ring. -/
@[simp]
theorem symmetricPresentation_algebraMap (r : R) :
    symmetricPresentation R σ (algebraMap R (SymmetricAlgebra R (σ →₀ R)) r) = C r := by
  simp [symmetricPresentation]

end MvPolynomial
