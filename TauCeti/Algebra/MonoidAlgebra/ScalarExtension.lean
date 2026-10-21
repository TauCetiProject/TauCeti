/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Basis
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Scalar extension of a free module on a set

The coefficient map `R[X] → S[X]` exhibits the latter as scalar extension along `R → S`,
without requiring a multiplication on `X`. It preserves the coefficient sum, so it also
maps the sum-zero submodules used in permutation representations into one another.

The construction uses Mathlib's `Finsupp.mapRange.linearMap` and `IsBaseChange.finsuppPow`.
-/

public noncomputable section

namespace TauCeti

section ScalarMap

variable (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S] (X : Type*)

/-- Extend every coefficient along `R → S` in the free module on `X`. -/
def monoidAlgebraScalarMap : MonoidAlgebra R X →ₗ[R] MonoidAlgebra S X :=
  (MonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The coefficients of scalar extension are the images of the original coefficients. -/
@[simp]
theorem coeff_monoidAlgebraScalarMap (v : MonoidAlgebra R X) (x : X) :
    (monoidAlgebraScalarMap R S X v).coeff x = algebraMap R S (v.coeff x) := by
  simp [monoidAlgebraScalarMap]

/-- Scalar extension sends a basis vector to the same basis vector with extended coefficient. -/
@[simp]
theorem monoidAlgebraScalarMap_single (x : X) (r : R) :
    monoidAlgebraScalarMap R S X (MonoidAlgebra.single x r) =
      MonoidAlgebra.single x (algebraMap R S r) := by
  classical
  ext y
  by_cases h : x = y <;> simp [h]

/-- Scalar extension preserves augmentation, that is, the sum of all coefficients. -/
@[simp]
theorem sumCoords_monoidAlgebraScalarMap (v : MonoidAlgebra R X) :
    (MonoidAlgebra.basis X S).sumCoords (monoidAlgebraScalarMap R S X v) =
      algebraMap R S ((MonoidAlgebra.basis X R).sumCoords v) := by
  simp only [Module.Basis.coe_sumCoords, MonoidAlgebra.basis_repr]
  -- Unfold the coefficient equivalences and `Finsupp.mapRange.linearMap` in the scalar map
  -- definition to expose `mapRange`; the pointwise coefficient lemma does not rewrite the sum.
  change (Finsupp.mapRange (algebraMap R S) (map_zero _) v.coeff).sum (fun _ => id) =
    algebraMap R S (v.coeff.sum fun _ => id)
  rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
  exact (map_finsuppSum (algebraMap R S) v.coeff (fun _ => id)).symm

end ScalarMap

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] (X : Type*)

/-- The free module on `X` commutes with extension of scalars. -/
theorem isBaseChange_monoidAlgebraScalarMap : IsBaseChange S (monoidAlgebraScalarMap R S X) := by
  have h := (IsBaseChange.linearMap R S).finsuppPow X
  exact (IsBaseChange.iff_of_equiv_comm
    (MonoidAlgebra.coeffLinearEquiv R).symm
    (MonoidAlgebra.coeffLinearEquiv S).symm
    (LinearMap.ext fun v => by simp [monoidAlgebraScalarMap])).mp h

end TauCeti
