/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces of the zero endomorphism

The zero endomorphism of a torsion-free module over a domain has no eigenvectors at a nonzero
scalar: `0 = μ • m` forces `m = 0` when `μ ≠ 0`. At `μ = 0` its eigenspace is its kernel, the
whole module (`Module.End.eigenspace_zero`).

## Main results

* `Module.End.zero_eigenspace_eq_bot`: the `μ`-eigenspace of `0` is trivial for `μ ≠ 0`.
-/

public section

namespace Module.End

/-- The zero endomorphism of a torsion-free module over a domain has trivial eigenspace at every
nonzero scalar. -/
@[simp]
theorem zero_eigenspace_eq_bot {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [IsTorsionFree R M] {μ : R} (hμ : μ ≠ 0) : (0 : End R M).eigenspace μ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun m hm ↦ ?_
  rw [mem_eigenspace_iff, LinearMap.zero_apply, eq_comm, smul_eq_zero] at hm
  exact hm.resolve_left hμ

end Module.End
