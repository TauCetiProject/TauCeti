/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# Maximality of self-adjoint partial operators

Taking the adjoint reverses extension order on densely defined partial linear maps
(`LinearPMap.adjoint_anti`). Consequently, a self-adjoint partial operator on a Hilbert space over
an `RCLike` scalar field has no proper formally self-adjoint extension
(`LinearPMap.eq_of_le_of_isFormalAdjoint`) and in particular no proper self-adjoint extension
(`LinearPMap.eq_of_le_of_isSelfAdjoint`).

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointMaximal.lean`,
and generalized from `ℂ` to arbitrary `RCLike` scalars.
-/

public section

namespace LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Taking the adjoint reverses extension order on densely defined partial linear maps. -/
theorem adjoint_anti {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A B : H →ₗ.[𝕜] F} (hAB : A ≤ B) (hA : Dense (A.domain : Set H)) : B† ≤ A† :=
  IsFormalAdjoint.le_adjoint hA fun x y => by
    rw [hAB.2 (x := x) (y := ⟨x, hAB.1 x.property⟩) rfl]
    exact (adjoint_isFormalAdjoint (hA.mono hAB.1)).symm ⟨x, hAB.1 x.property⟩ y

/-- A self-adjoint partial operator has no proper formally self-adjoint extension. -/
theorem eq_of_le_of_isFormalAdjoint {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) (hAB : A ≤ B) : A = B :=
  le_antisymm hAB <|
    (hB.le_adjoint (hA.dense_domain.mono hAB.1)).trans
      ((adjoint_anti hAB hA.dense_domain).trans_eq (isSelfAdjoint_def.mp hA))

/-- A self-adjoint partial operator cannot be properly extended to another
self-adjoint partial operator. -/
theorem eq_of_le_of_isSelfAdjoint {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A ≤ B) : A = B :=
  eq_of_le_of_isFormalAdjoint hA hB.isFormalAdjoint hAB

end LinearPMap
