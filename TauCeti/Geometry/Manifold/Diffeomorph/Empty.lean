/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Diffeomorphism between empty manifolds with arbitrary models

Two empty charted spaces `M` and `N` over a common base field `𝕜` are `C^n` diffeomorphic for any
models with corners `I` and `J` (`Diffeomorph.ofIsEmpty`). Mathlib's `Diffeomorph.empty` covers the
special case where `M` and `N` share the same model `I`.
-/

public section

open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

/-- The unique `C^n` diffeomorphism between two empty charted spaces `M` and `N`, allowing
distinct models with corners `I` and `J` (generalizing `Diffeomorph.empty`). -/
def ofIsEmpty [IsEmpty M] [IsEmpty N] : M ≃ₘ^n⟮I, J⟯ N where
  __ := Equiv.equivOfIsEmpty M N
  contMDiff_toFun x := (IsEmpty.false x).elim
  contMDiff_invFun y := (IsEmpty.false y).elim

/-- The underlying equivalence of `Diffeomorph.ofIsEmpty` is `Equiv.equivOfIsEmpty`. -/
@[simp]
theorem toEquiv_ofIsEmpty [IsEmpty M] [IsEmpty N] :
    (ofIsEmpty : M ≃ₘ^n⟮I, J⟯ N).toEquiv = Equiv.equivOfIsEmpty M N :=
  (rfl)

/-- The inverse of `Diffeomorph.ofIsEmpty` is `Diffeomorph.ofIsEmpty`. -/
@[simp]
theorem symm_ofIsEmpty [IsEmpty M] [IsEmpty N] :
    (ofIsEmpty : M ≃ₘ^n⟮I, J⟯ N).symm = ofIsEmpty :=
  ext fun y ↦ (IsEmpty.false y).elim

end Diffeomorph
