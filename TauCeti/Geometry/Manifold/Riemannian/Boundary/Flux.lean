/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Volume
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.OutwardUnitNormal

/-!
# Regularity and integrability of the outward boundary flux

For a vector field `X` on a Riemannian manifold `M` with boundary modeled on
`EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), this module proves compact support, continuity, and
integrability against `TauCeti.halfSpaceBoundaryVolume` of the outward normal boundary flux
`x ↦ inner ℝ (X x) (outwardUnitNormal x)`.

## Main results

* `TauCeti.hasCompactSupport_boundaryFlux`, `TauCeti.continuous_boundaryFlux`,
  `TauCeti.integrable_boundaryFlux`: compact support, continuity, and integrability of the outward
  normal boundary flux `x ↦ inner ℝ (X x) (outwardUnitNormal x)`.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

section BoundaryFlux

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The outward normal flux `x ↦ inner ℝ (X x) (N x)` of a compactly supported vector field has
compact support on the boundary. -/
theorem hasCompactSupport_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    HasCompactSupport (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (outwardUnitNormal x)) := by
  have hclosed := ((𝓡∂ (n + 1)).isClosed_boundary (M := M) one_ne_zero).isClosedEmbedding_subtypeVal
  refine HasCompactSupport.intro' (hclosed.isCompact_preimage hc)
    ((isClosed_tsupport _).preimage continuous_subtypeVal) fun x hx ↦ ?_
  have h0 : X (x : M) = 0 := image_eq_zero_of_notMem_tsupport
    (α := EuclideanSpace ℝ (Fin (n + 1))) hx
  simp [h0]

variable [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
  (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The outward normal flux `x ↦ inner ℝ (X x) (N x)` of a continuous vector field `X` is
continuous on the boundary. -/
theorem continuous_boundaryFlux {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}
    (hX : Continuous (T% X)) :
    Continuous (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (outwardUnitNormal x)) := by
  let _ := isManifold_boundary (n := n) (k := 1) M
  have _ : IsManifold (𝓡∂ (n + 1)) (0 + 1) M := by simpa using ‹IsManifold (𝓡∂ (n + 1)) 1 M›
  have _ := IsContinuousRiemannianBundle.toIsContMDiffZero (IB := 𝓡∂ (n + 1))
    (F := EuclideanSpace ℝ (Fin (n + 1))) (V := fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)
  exact (ContMDiff.inner_bundle
    (h := IsContinuousRiemannianBundle.toIsContMDiffZero (IB := 𝓡∂ (n + 1)))
    (contMDiff_zero_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))).2 (hX.comp continuous_subtypeVal))
    (contMDiff_zero_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))).2
      (contMDiff_outwardUnitNormal (n := n) (M := M) (k := 0)).continuous)).continuous

/-- **Integrability of the boundary flux.** The outward normal flux `x ↦ inner ℝ (X x) (N x)` of a
compactly supported continuous vector field is integrable against `halfSpaceBoundaryVolume`. -/
theorem integrable_boundaryFlux [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    {X : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hX : Continuous (T% X))
    (hc : HasCompactSupport (β := EuclideanSpace ℝ (Fin (n + 1))) X) :
    Integrable (fun x : (𝓡∂ (n + 1)).boundary M ↦
      inner ℝ (X (x : M)) (outwardUnitNormal x))
      (halfSpaceBoundaryVolume (n := n) (M := M)) :=
  (continuous_boundaryFlux hX).integrable_of_hasCompactSupport (hasCompactSupport_boundaryFlux hc)

end BoundaryFlux

end TauCeti
