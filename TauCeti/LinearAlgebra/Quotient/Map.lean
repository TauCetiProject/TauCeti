/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Images of submodules in a quotient

A class `[x]` of `M ⧸ p` lies in the image of a submodule `p'` containing `p` exactly when
`x ∈ p'` (`Submodule.Quotient.mk_mem_map_mkQ_iff`). This is membership in the image of
`p'` under the quotient map, read off from Mathlib's `Submodule.comap_map_mkQ`; it identifies
subspaces of a quotient through their representatives, as in the linear symplectic reduction of
a subspace of a reduced space.
-/

public section

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The class of `x` in `M ⧸ p` lies in the image of a submodule `p'` containing `p` exactly when
`x ∈ p'`. -/
theorem Quotient.mk_mem_map_mkQ_iff {p p' : Submodule R M} (h : p ≤ p') (x : M) :
    (Quotient.mk x : M ⧸ p) ∈ p'.map p.mkQ ↔ x ∈ p' := by
  rw [← mkQ_apply, ← mem_comap, comap_map_mkQ, sup_eq_right.2 h]

end Submodule
