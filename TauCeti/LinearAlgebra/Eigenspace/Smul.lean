/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces of a scalar multiple

Scaling an endomorphism `f` by a nonzero scalar `c` scales its eigenvalues by `c` and leaves the
eigenspaces unchanged: the `c μ`-eigenspace of `c • f` is the `μ`-eigenspace of `f`. For example,
the eigenspaces of the acceleration operator `(κ / m) • H` of a spring system are those of its
force matrix `H`.
-/

public section

namespace Module.End

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.IsTorsionFree R M]

/-- The `c μ`-eigenspace of `c • f` is the `μ`-eigenspace of `f`, for `c ≠ 0`. -/
theorem eigenspace_smul (f : End R M) {c : R} (hc : c ≠ 0) (μ : R) :
    eigenspace (c • f) (c * μ) = eigenspace f μ := by
  ext x
  rw [mem_eigenspace_iff, mem_eigenspace_iff, LinearMap.smul_apply, mul_smul,
    smul_right_inj hc]

end Module.End
