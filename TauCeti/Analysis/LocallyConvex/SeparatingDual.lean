/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Commutant of bounded operators on spaces with separating dual

On any topological vector space `E` over a topological field `𝕜` with separating dual
(`SeparatingDual 𝕜 E`), Mathlib's `Algebra.IsCentral.instContinuousLinearMap` establishes that
`E →L[𝕜] E` is a central `𝕜`-algebra. Equivalently, an operator `T : E →L[𝕜] E` commutes with every
continuous linear operator on `E` if and only if it is a scalar multiple of the identity
(`ContinuousLinearMap.commute_forall_iff`). In particular this applies to every normed space over
`ℝ` or `ℂ`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [TopologicalSpace 𝕜] [TopologicalSpace E]
  [IsTopologicalRing 𝕜] [Module 𝕜 E] [SeparatingDual 𝕜 E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]

/-- An operator on a topological vector space with separating dual commutes with every continuous
linear operator if and only if it is a scalar multiple of the identity. -/
theorem commute_forall_iff {T : E →L[𝕜] E} :
    (∀ a : E →L[𝕜] E, Commute T a) ↔ ∃ c : 𝕜, T = c • 1 := by
  have hmem : (∀ a : E →L[𝕜] E, Commute T a) ↔ T ∈ Subalgebra.center 𝕜 (E →L[𝕜] E) := by
    rw [Subalgebra.mem_center_iff]
    exact forall_congr' fun _ => by simp [Commute, SemiconjBy, eq_comm]
  rw [hmem, Algebra.IsCentral.mem_center_iff (K := 𝕜)]
  exact exists_congr fun _ => by simp [Algebra.algebraMap_eq_smul_one]

end ContinuousLinearMap
