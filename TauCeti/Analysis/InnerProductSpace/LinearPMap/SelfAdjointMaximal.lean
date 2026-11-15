/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# Maximality of self-adjoint partial operators

Taking the adjoint reverses extension order on densely defined partial linear maps
(`LinearPMap.adjoint_antitone`). Consequently, a self-adjoint partial operator on a
Hilbert space over an `RCLike` scalar field has no proper self-adjoint extension
(`LinearPMap.eq_of_le_of_isSelfAdjoint`).

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointMaximal.lean`,
and generalized from `ℂ` to arbitrary `RCLike` scalars.
-/

public section

namespace LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Taking the adjoint reverses extension order on densely defined partial linear maps. -/
theorem adjoint_antitone {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A B : H →ₗ.[𝕜] F} (hAB : A ≤ B) (hA : Dense (A.domain : Set H)) : B† ≤ A† :=
  IsFormalAdjoint.le_adjoint hA fun x y => by
    rw [hAB.2 (x := x) (y := ⟨x, hAB.1 x.2⟩) rfl]
    exact (adjoint_isFormalAdjoint (hA.mono hAB.1)).symm ⟨x, hAB.1 x.2⟩ y

/-- A self-adjoint partial operator cannot be properly extended to another
self-adjoint partial operator. -/
theorem eq_of_le_of_isSelfAdjoint {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A ≤ B) : A = B :=
  le_antisymm hAB <| by
    simpa [isSelfAdjoint_def.mp hA, isSelfAdjoint_def.mp hB] using
      adjoint_antitone hAB hA.dense_domain

end LinearPMap
