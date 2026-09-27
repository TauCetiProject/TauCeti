/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Changing the functional in Scharlau transfer

Multiplying the input of a transfer functional by `a` has the same effect as tensoring the
original form with the quadratic line `⟨a⟩` before transfer. The identification uses the
canonical equivalence `L ⊗[L] V ≃ₗ[L] V`, so it works for every scalar `a`, including zero.
For a finite field extension, every pair of nonzero functionals differs in this way by a unit.

This change-of-functional formula controls the dependence on the functional when transfer is
descended to Witt classes.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

open scoped TensorProduct

namespace QuadraticMap

section CommRing

variable {K L V : Type*} [CommSemiring K] [CommRing L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [Invertible (2 : L)]

/-- Multiplication of the input of a functional is tensoring with a quadratic line before
Scharlau transfer. This is an isometry of forms over the base ring `K`. -/
theorem equivalent_scharlauTransfer_comp_mul_rankOneTensor
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (a : L) :
    (Q.scharlauTransfer (s.comp (LinearMap.mul K L a))).Equivalent
      ((QuadraticForm.tmul (a • (QuadraticMap.sq : QuadraticForm L L)) Q).scharlauTransfer s) := by
  rw [scharlauTransfer_comp_mul]
  exact ⟨(rankOneTensorIsometry Q a).symm.scharlauTransfer s⟩

end CommRing

section Field

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [Invertible (2 : L)]

/-- Any two nonzero functionals on a finite field extension give transfers related by tensoring
the original form with a one-dimensional form of unit coefficient. -/
theorem exists_unit_scharlauTransfer_equivalent_rankOneTensor [FiniteDimensional K L]
    (Q : QuadraticForm L V) (s t : L →ₗ[K] K) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ a : Lˣ, (Q.scharlauTransfer t).Equivalent
      ((QuadraticForm.tmul ((a : L) • (QuadraticMap.sq : QuadraticForm L L)) Q).scharlauTransfer
        s) := by
  obtain ⟨a, ha⟩ := Q.exists_unit_scharlauTransfer_eq s t hs ht
  refine ⟨a, ?_⟩
  rw [ha]
  exact ⟨(rankOneTensorIsometry Q a).symm.scharlauTransfer s⟩

end Field

end QuadraticMap
