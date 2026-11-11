/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.TwistedProd

/-!
# Lagrangian maps into twisted products

A map `f : L → M × N` is Lagrangian for the twisted product `pr₁*σ - pr₂*τ` exactly when, at
each point, its tangent image read in `T M × T N` through the canonical identification
`Manifold.tangentSpaceProdEquiv` is Lagrangian for the linear twisted product of the tangent
fibre forms (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_twistedProd_iff_forall`).
This is the form in which linear results about canonical relations, such as Lagrangian graphs
and compositions, apply to Lagrangian correspondences.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F G N EL HL L : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [NormedAddCommGroup EL] [NormedSpace ℝ EL] [TopologicalSpace HL]
  {K : ModelWithCorners ℝ EL HL} [TopologicalSpace L] [ChartedSpace HL L]
  {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} {f : L → M × N}

/-- A map into a twisted product is Lagrangian exactly when its tangent images, read in the
product of the tangent spaces of the factors, are linear canonical relations. -/
theorem isLagrangianMap_twistedProd_iff_forall (hσ : σ.IsNondegenerate)
    (hτ : τ.IsNondegenerate) :
    (hσ.twistedProd hτ).IsLagrangianMap K f ↔
      ∀ x, ((hσ.symplecticFormAt (f x).1).twistedProd (hτ.symplecticFormAt (f x).2)).IsLagrangian
        (LinearMap.range ((Manifold.tangentSpaceProdEquiv (f x)).toLinearEquiv.toLinearMap ∘ₗ
          (mfderiv K (I.prod J) f x).toLinearMap)) := by
  rw [isLagrangianMap_iff_forall]
  refine forall_congr' fun x ↦ ?_
  rw [LinearMap.range_comp, ← symplecticFormAt_twistedProd hσ hτ,
    SymplecticForm.isLagrangian_map_transport_iff]

end TauCeti.SmoothTwoForm.IsNondegenerate
