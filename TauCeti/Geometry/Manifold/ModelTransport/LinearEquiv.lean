/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.LinearEquiv

/-!
# Linear model changes for `BoundarylessModel`

Combining a continuous linear equivalence `L : E ≃L[𝕜] F` of model vector spaces with
`TauCeti.BoundarylessModel.diffeomorph` produces a canonical diffeomorphism
`BoundarylessModel.diffeomorphTransContinuousLinearEquiv I L n : M ≃ₘ^n⟮I, 𝓘(𝕜, F)⟯ _`
from any manifold modelled on a boundaryless model `(E, H, I)` onto a self-modelled copy over `F`.

## Main definitions

* `TauCeti.BoundarylessModel.diffeomorphTransContinuousLinearEquiv`: the identity diffeomorphism
  from `(M, I)` to `BoundarylessModel (I.transContinuousLinearEquiv L) M` modelled on `𝓘(𝕜, F)`.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.BoundarylessModel

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- The identity as a `C^n` diffeomorphism from a boundaryless manifold `(M, I)` to its copy
`BoundarylessModel (I.transContinuousLinearEquiv L) M` modelled directly on the vector space `F`
via `L : E ≃L[𝕜] F`. -/
def diffeomorphTransContinuousLinearEquiv (L : E ≃L[𝕜] F) (n : ℕ∞ω) :
    M ≃ₘ^n⟮I, 𝓘(𝕜, F)⟯ BoundarylessModel (I.transContinuousLinearEquiv L) M :=
  (L.toTransContinuousLinearEquiv I M).trans
    (diffeomorph (I.transContinuousLinearEquiv L) (M := M) n)

@[simp]
theorem coe_diffeomorphTransContinuousLinearEquiv (L : E ≃L[𝕜] F) (n : ℕ∞ω) :
    ⇑(diffeomorphTransContinuousLinearEquiv I (M := M) L n) =
      homeomorph (I.transContinuousLinearEquiv L) M := by
  ext x
  simp only [diffeomorphTransContinuousLinearEquiv, Diffeomorph.coe_trans, Function.comp_apply,
    coe_diffeomorph, ContinuousLinearEquiv.toTransContinuousLinearEquiv]
  rfl

@[simp]
theorem coe_diffeomorphTransContinuousLinearEquiv_symm (L : E ≃L[𝕜] F) (n : ℕ∞ω) :
    ⇑(diffeomorphTransContinuousLinearEquiv I (M := M) L n).symm =
      (homeomorph (I.transContinuousLinearEquiv L) M).symm := by
  ext x
  simp only [diffeomorphTransContinuousLinearEquiv, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    Function.comp_apply, coe_diffeomorph_symm, ContinuousLinearEquiv.toTransContinuousLinearEquiv]
  rfl

end TauCeti.BoundarylessModel
