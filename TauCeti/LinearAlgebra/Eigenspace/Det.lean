/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvalues and the determinant

An endomorphism `f` of a finite free module over an integral domain has the eigenvalue `μ` exactly
when `det (f - μ • 1) = 0`. Mathlib states the same fact through the characteristic polynomial
(`Module.End.hasEigenvalue_iff_isRoot_charpoly`); the determinant form is the one to use for
continuity arguments, since the determinant of an operator depends continuously on it.

## Main results

* `Module.End.hasEigenvalue_iff_det_sub_eq_zero`: `f` has the eigenvalue `μ` if and only if
  `det (f - μ • 1) = 0`.
* `Module.End.det_smul_one_sub_ne_zero_iff`: the `μ`-eigenspace of `f` is trivial if and only if
  `det (μ • 1 - f) ≠ 0`.
-/

public section

namespace Module.End

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- An endomorphism `f` of a finite free module over an integral domain has the eigenvalue `μ`
exactly when `det (f - μ • 1) = 0`. -/
theorem hasEigenvalue_iff_det_sub_eq_zero (f : End R M) (μ : R) :
    f.HasEigenvalue μ ↔ LinearMap.det (f - μ • 1) = 0 := by
  rw [hasEigenvalue_iff, eigenspace_def, LinearMap.det_eq_zero_iff_ker_ne_bot]

/-- The `μ`-eigenspace of an endomorphism `f` of a finite free module over an integral domain is
trivial exactly when `det (μ • 1 - f) ≠ 0`. -/
theorem det_smul_one_sub_ne_zero_iff (f : End R M) (μ : R) :
    LinearMap.det (μ • 1 - f) ≠ 0 ↔ f.eigenspace μ = ⊥ := by
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, ← neg_sub, LinearMap.ker_neg,
    eigenspace_def]

end Module.End
