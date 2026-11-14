/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# The metric in normal coordinates

Let `U` be a normal domain at a point `p` of a Riemannian manifold `M`. The exponential map is a
local diffeomorphism on `U`, so pulling the metric `g` back along it gives a metric on the open
subset `U` of the tangent space `T_p M`: the metric `g` read in normal coordinates centred at `p`.

## Main definitions and results

* `TauCeti.Manifold.IsNormalDomain.normalCoordinateMetric`: the metric `exp_p^* g` on a normal
  domain.
* `TauCeti.Manifold.IsNormalDomain.normalCoordinateMetric_inner`: it pairs two vectors as `g`
  pairs their images under the differential of `exp_p`.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

namespace IsNormalDomain

variable {p : M} {U : Set (TangentSpace I p)}

/-- The metric `g` read in normal coordinates: its pullback along the exponential map, as a metric
on the normal domain. -/
def normalCoordinateMetric (hU : IsNormalDomain I M p U) :
    ContMDiffRiemannianMetric 𝓘(ℝ, TangentSpace I p) ∞ (TangentSpace I p)
      (fun v : hU.opens ↦ TangentSpace 𝓘(ℝ, TangentSpace I p) v) :=
  (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)).pullback
      (riemannianExp I M p ∘ Subtype.val) (hU.contMDiff_riemannianExp_comp_val le_rfl)
      fun v ↦ (hU.isInvertible_mfderiv_riemannianExp_comp_val v).injective

/-- The metric in normal coordinates is the pullback of `g` along the exponential map. -/
theorem normalCoordinateMetric_eq_pullback (hU : IsNormalDomain I M p U) :
    hU.normalCoordinateMetric =
      (ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
        (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)).pullback
          (riemannianExp I M p ∘ Subtype.val) (hU.contMDiff_riemannianExp_comp_val le_rfl)
          fun v ↦ (hU.isInvertible_mfderiv_riemannianExp_comp_val v).injective :=
  (rfl)

/-- The metric in normal coordinates pairs two vectors as `g` pairs their images under the
differential of the exponential map. -/
theorem normalCoordinateMetric_inner (hU : IsNormalDomain I M p U) (v : hU.opens)
    (u w : TangentSpace 𝓘(ℝ, TangentSpace I p) v) :
    hU.normalCoordinateMetric.inner v u w =
      inner ℝ (mfderiv 𝓘(ℝ, TangentSpace I p) I
          (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) v u)
        (mfderiv 𝓘(ℝ, TangentSpace I p) I
          (riemannianExp I M p ∘ (Subtype.val : hU.opens → TangentSpace I p)) v w) := by
  rw [normalCoordinateMetric_eq_pullback, ContMDiffRiemannianMetric.pullback_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  -- The bundle metric of the `RiemannianBundle` instance is its fibrewise `inner ℝ`.
  rfl

end IsNormalDomain

end TauCeti.Manifold
