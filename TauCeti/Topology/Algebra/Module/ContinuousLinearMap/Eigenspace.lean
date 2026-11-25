/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Eigenvalues of continuous endomorphisms

For a continuous endomorphism `T` of a topological module, `T - μ • id` has trivial kernel exactly
when `μ` is not an eigenvalue of `T`.

## Main results

* `ContinuousLinearMap.ker_sub_smul_id_eq_bot_iff`: `T - μ • id` has trivial kernel exactly when
  `μ` is not an eigenvalue of `T`.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- `T - μ • id` has trivial kernel exactly when `μ` is not an eigenvalue of `T`. -/
theorem ker_sub_smul_id_eq_bot_iff {T : M →L[R] M} {μ : R} :
    LinearMap.ker ((T - μ • ContinuousLinearMap.id R M : M →L[R] M) : M →ₗ[R] M) = ⊥ ↔
      ¬Module.End.HasEigenvalue (T : M →ₗ[R] M) μ := by
  rw [Module.End.hasEigenvalue_iff, not_not]
  congr!
  ext x
  simp [sub_eq_zero]

end ContinuousLinearMap
