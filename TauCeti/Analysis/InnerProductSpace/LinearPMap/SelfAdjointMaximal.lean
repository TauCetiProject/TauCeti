/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Maximality of self-adjoint partial operators

A self-adjoint partial operator on a complex Hilbert space has no proper
self-adjoint extension. Thus, inclusion of self-adjoint partial operators
already implies equality.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointMaximal.lean`.
-/

public section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint partial operator cannot be properly extended to another
self-adjoint partial operator. -/
theorem eq_of_le_of_isSelfAdjoint {A B : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A ≤ B) : A = B := by
  have hAi : Complex.I ∈ A.resolventSet :=
    hA.mem_resolventSet_of_im_ne_zero (by simp)
  have hBi : Complex.I ∈ B.resolventSet :=
    hB.mem_resolventSet_of_im_ne_zero (by simp)
  exact _root_.LinearPMap.eq_of_le_of_mem_resolventSet hAB hAi hBi

end LinearPMap
