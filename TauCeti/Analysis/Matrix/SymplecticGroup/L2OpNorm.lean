/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The `ℓ²` operator norm and the canonical skew-symmetric matrix

The canonical skew-symmetric matrix `J` is unitary (`Matrix.J_mem_unitaryGroup`), so multiplying
by it preserves Mathlib's scoped `ℓ²` operator norm (`Matrix.Norms.L2Operator`).

## Main results

* `Matrix.l2_opNorm_J_mul`: `‖J S‖ = ‖S‖` in the `ℓ²` operator norm.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- Multiplying by the canonical skew-symmetric matrix `J` preserves the `ℓ²` operator norm, as `J`
is unitary. -/
@[simp]
theorem l2_opNorm_J_mul {l 𝕜 : Type*} [Fintype l] [DecidableEq l] [RCLike 𝕜]
    (S : Matrix (l ⊕ l) (l ⊕ l) 𝕜) : ‖J l 𝕜 * S‖ = ‖S‖ :=
  CStarRing.norm_mem_unitary_mul S (J_mem_unitaryGroup l 𝕜)

end Matrix
