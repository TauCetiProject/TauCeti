/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficientAdjoin
public import TauCeti.Algebra.Coalgebra.Comodule.Zero

/-!
# Matrix coefficients of zero comodules

This file packages the matrix-coefficient objects for zero comodules.  A comodule whose
underlying module is subsingleton has only the zero vector, so every matrix coefficient is
zero.  Consequently its coefficient set is `{0}`, its coefficient submodule is `⊥`, and, in
an algebra, its coefficient subalgebra is the bottom `R`-subalgebra.

These are small Layer 1 bookkeeping facts for the reductive-groups roadmap: matrix
coefficients are the coalgebra-side functions attached to representations, and the
finite-dimensional representation category needs their behavior on zero objects as part of
the additive API.

## Main declarations

* `TauCeti.Comodule.matrixCoefficient_eq_zero_of_subsingleton`.
* `TauCeti.Comodule.matrixCoefficientSubmodule_eq_bot_of_subsingleton`.
* `TauCeti.Comodule.matrixCoefficientSubalgebra_eq_bot_of_subsingleton`.
* `TauCeti.ComoduleCat.matrixCoefficient_zero` and
  `TauCeti.ComoduleCat.matrixCoefficientSet_zero`.
* `TauCeti.ComoduleCat.matrixCoefficientSubmodule_zero` and
  `TauCeti.ComoduleCat.matrixCoefficientSubalgebra_zero`.

## References

This is the standard zero-representation behavior of matrix coefficients.  It uses Tau
Ceti's existing matrix-coefficient API and zero comodule, supplying a prerequisite for
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1, "Comodules over a coalgebra/Hopf
algebra" and "The dictionary: representation of `G` ⇆ `A`-comodule; matrix coefficients."
-/

public section

namespace TauCeti

namespace Comodule

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}

section Submodule

variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- In a subsingleton comodule, every matrix coefficient is zero. -/
@[simp]
theorem matrixCoefficient_eq_zero_of_subsingleton [Subsingleton M] (φ : M →ₗ[R] R) (m : M) :
    matrixCoefficient (R := R) (C := C) φ m = 0 := by
  rw [Subsingleton.elim m (0 : M)]
  simp

/-- The coefficient set of a subsingleton comodule is `{0}`. -/
@[simp]
theorem matrixCoefficientSet_eq_singleton_zero_of_subsingleton [Subsingleton M] :
    matrixCoefficientSet (R := R) (C := C) (M := M) = ({0} : Set C) := by
  ext c
  rw [mem_matrixCoefficientSet_iff]
  constructor
  · rintro ⟨φ, m, rfl⟩
    simp
  · intro hc
    rw [Set.mem_singleton_iff.mp hc]
    exact ⟨0, 0, by simp⟩

/-- The coefficient submodule of a subsingleton comodule is bottom. -/
@[simp]
theorem matrixCoefficientSubmodule_eq_bot_of_subsingleton [Subsingleton M] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) = ⊥ := by
  rw [matrixCoefficientSubmodule_def, matrixCoefficientSet_eq_singleton_zero_of_subsingleton]
  simp

end Submodule

section Algebra

variable [CommSemiring R]
variable [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The coefficient subalgebra of a subsingleton comodule is bottom. -/
@[simp]
theorem matrixCoefficientSubalgebra_eq_bot_of_subsingleton [Subsingleton M] :
    matrixCoefficientSubalgebra (R := R) (C := C) (M := M) = ⊥ := by
  rw [matrixCoefficientSubalgebra_def, matrixCoefficientSet_eq_singleton_zero_of_subsingleton]
  simp

end Algebra

end Comodule

namespace ComoduleCat

universe u v w

variable (R : Type u) (C : Type v)

section Submodule

variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Matrix coefficients of the bundled zero comodule are zero. -/
@[simp]
theorem matrixCoefficient_zero
    (φ : (zero R C : ComoduleCat.{u, v, w} R C) →ₗ[R] R)
    (m : (zero R C : ComoduleCat.{u, v, w} R C)) :
    Comodule.matrixCoefficient (R := R) (C := C) φ m = 0 := by
  haveI := ComoduleCat.subsingleton_zero (R := R) (C := C)
  exact Comodule.matrixCoefficient_eq_zero_of_subsingleton (R := R) (C := C) φ m

/-- The coefficient set of the bundled zero comodule is `{0}`. -/
@[simp]
theorem matrixCoefficientSet_zero :
    Comodule.matrixCoefficientSet (R := R) (C := C)
        (M := (zero R C : ComoduleCat.{u, v, w} R C)) = ({0} : Set C) := by
  haveI := ComoduleCat.subsingleton_zero (R := R) (C := C)
  exact Comodule.matrixCoefficientSet_eq_singleton_zero_of_subsingleton (R := R) (C := C)
    (M := (zero R C : ComoduleCat.{u, v, w} R C))

/-- The coefficient submodule of the bundled zero comodule is bottom. -/
@[simp]
theorem matrixCoefficientSubmodule_zero :
    Comodule.matrixCoefficientSubmodule (R := R) (C := C)
        (M := (zero R C : ComoduleCat.{u, v, w} R C)) = ⊥ := by
  haveI := ComoduleCat.subsingleton_zero (R := R) (C := C)
  exact Comodule.matrixCoefficientSubmodule_eq_bot_of_subsingleton (R := R) (C := C)
    (M := (zero R C : ComoduleCat.{u, v, w} R C))

end Submodule

section Algebra

variable [CommSemiring R]
variable [Semiring C] [Algebra R C] [Coalgebra R C]

/-- The coefficient subalgebra of the bundled zero comodule is bottom. -/
@[simp]
theorem matrixCoefficientSubalgebra_zero :
    Comodule.matrixCoefficientSubalgebra (R := R) (C := C)
        (M := (zero R C : ComoduleCat.{u, v, w} R C)) = ⊥ := by
  haveI := ComoduleCat.subsingleton_zero (R := R) (C := C)
  exact Comodule.matrixCoefficientSubalgebra_eq_bot_of_subsingleton (R := R) (C := C)
    (M := (zero R C : ComoduleCat.{u, v, w} R C))

end Algebra

end ComoduleCat

end TauCeti
