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
force matrix `H`. Shifting `f` by a scalar multiple of the identity shifts its eigenvalues and
leaves the eigenspaces unchanged: the `μ`-eigenspace of `f - ρ • id` is the `(μ + ρ)`-eigenspace
of `f`.
-/

public section

namespace Module.End

section Shift

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Shifting an endomorphism by a scalar shifts its eigenspaces: the eigenspace of `f - ρ • id` at
`μ` is the eigenspace of `f` at `μ + ρ`. -/
@[simp]
theorem eigenspace_sub_smul_id (f : End R M) (ρ μ : R) :
    (f - ρ • LinearMap.id).eigenspace μ = f.eigenspace (μ + ρ) := by
  have h : f - ρ • LinearMap.id - μ • 1 = f - (μ + ρ) • 1 := by module
  simp only [eigenspace_def, h]

/-- Shifting an endomorphism by a scalar shifts its eigenspaces: the eigenspace of `f + ρ • id` at
`μ` is the eigenspace of `f` at `μ - ρ`. -/
@[simp]
theorem eigenspace_add_smul_id (f : End R M) (ρ μ : R) :
    (f + ρ • LinearMap.id).eigenspace μ = f.eigenspace (μ - ρ) := by
  have h : f + ρ • LinearMap.id - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [eigenspace_def, h]

end Shift

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.IsTorsionFree R M]

/-- The `c μ`-eigenspace of `c • f` is the `μ`-eigenspace of `f`, for `c ≠ 0`. -/
theorem eigenspace_smul (f : End R M) {c : R} (hc : c ≠ 0) (μ : R) :
    eigenspace (c • f) (c * μ) = eigenspace f μ := by
  ext x
  rw [mem_eigenspace_iff, mem_eigenspace_iff, LinearMap.smul_apply, mul_smul,
    smul_right_inj hc]

end Module.End
