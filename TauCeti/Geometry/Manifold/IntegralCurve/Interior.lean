/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.Boundary.Interior

/-!
# Vector fields and integral curves in the interior of a manifold with corners

Let `M` be a manifold modelled with corners on a finite-dimensional real vector space `E`. Its
interior `I.interior M` is a manifold without boundary modelled on `E`
(`ModelWithCorners.instChartedSpaceInterior`), whose tangent spaces, like those of `M`, are `E`.
So a vector field `V` on `M` restricts to a vector field `x ↦ V x` on the interior. This file shows
that the restriction of a `C^n` field is `C^n` (`ModelWithCorners.contMDiff_restrictInterior`),
and that the integral curves of the restriction are exactly the integral curves of `V` that stay in
the interior (`ModelWithCorners.isMIntegralCurveOn_subtypeVal_comp_iff`).

This lets the flow of a vector field on a manifold without boundary, `TauCeti.flowOf`, be applied
to the part of a manifold with boundary away from its boundary, for instance to the trajectories
of an inward-pointing field after they have left the boundary.

## Main results

* `ModelWithCorners.isMIntegralCurveOn_subtypeVal_comp_iff`: the integral curves of the restriction
  of `V` to the interior are the integral curves of `V` in the interior.
* `ModelWithCorners.mpullback_subtypeVal_interior`: the restriction is the pullback of `V` by the
  inclusion of the interior.
* `ModelWithCorners.contMDiff_restrictInterior`: the restriction of a `C^n` vector field to the
  interior is `C^n`.
-/

public section

open Set
open scoped Manifold ContDiff

namespace ModelWithCorners

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {V : (x : M) → TangentSpace I x}

variable (I)

variable (V) in
/-- The restriction of a vector field `V` on `M` to the interior of `M`: the tangent spaces of the
interior, like those of `M`, are `E`. -/
def restrictInterior (x : I.interior M) : TangentSpace 𝓘(ℝ, E) x :=
  V x

@[simp]
theorem restrictInterior_apply (x : I.interior M) : I.restrictInterior V x = V x :=
  (rfl)

/-- **Integral curves in the interior.** A curve `γ` in the interior of `M` is an integral curve
of the restriction of the vector field `V` to the interior if and only if it is an integral curve
of `V` when read in `M`. -/
theorem isMIntegralCurveOn_subtypeVal_comp_iff {γ : ℝ → I.interior M} {s : Set ℝ} :
    IsMIntegralCurveOn (Subtype.val ∘ γ) V s ↔
      IsMIntegralCurveOn γ (I.restrictInterior V) s :=
  forall₂_congr fun _ _ ↦ I.hasMFDerivWithinAt_subtypeVal_comp_iff

/-- The restriction of `V` to the interior is the pullback of `V` by the inclusion of the interior,
whose differential is the identity of `E`. -/
theorem mpullback_subtypeVal_interior :
    VectorField.mpullback 𝓘(ℝ, E) I (Subtype.val : I.interior M → M) V = I.restrictInterior V := by
  funext x
  rw [VectorField.mpullback_apply, I.mfderiv_subtypeVal_interior]
  exact DFunLike.congr_fun (ContinuousLinearMap.inverse_id (R := ℝ) (M := E)) (V x)

/-- **The restriction of a smooth vector field to the interior is smooth.** If the vector field
`V` on a manifold with corners is `C^n`, so is its restriction to the interior. -/
theorem contMDiff_restrictInterior {n : WithTop ℕ∞} [IsManifold I 1 M]
    (hV : ContMDiff I I.tangent n (T% V)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n (T% (I.restrictInterior V)) := by
  intro x
  have h := ContMDiffWithinAt.mpullback_vectorField_preimage ((hV x).contMDiffWithinAt (s := univ))
    (contMDiff_subtypeVal_interior (n := ω) I x)
    (by rw [I.mfderiv_subtypeVal_interior]; exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩) le_top
  rwa [I.mpullback_subtypeVal_interior, preimage_univ, contMDiffWithinAt_univ] at h

end ModelWithCorners
