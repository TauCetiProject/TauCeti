/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Orientation.Boundaryless
public import TauCeti.Geometry.Manifold.Orientation.LinearEquiv

/-!
# Invariance of smooth mapping degree under source model changes

Both independent changes of source model coordinates on a `C¹` manifold `(M, I)` preserve the
smooth degree counts `TauCeti.degreeAtRegularValue` and `TauCeti.degree` of any map `f : M → N`
into an oriented `C¹` manifold `(N, J)`:

1. Recharting `I` along a continuous linear equivalence `e : E ≃L[ℝ] F` via
   `TauCeti.Manifold.Orientation.transContinuousLinearEquiv` (including on manifolds with boundary
   or corners).
2. Replacing a boundaryless model `I` on `M` by its vector-space-modelled copy
   `TauCeti.BoundarylessModel I M` via `TauCeti.Manifold.Orientation.toBoundarylessModel`.

## Main results

* `TauCeti.Manifold.Orientation.degreeAtRegularValue_transContinuousLinearEquiv`,
  `TauCeti.Manifold.Orientation.degree_transContinuousLinearEquiv`: recharting the source
  orientation along `e : E ≃L[ℝ] F` leaves `TauCeti.degreeAtRegularValue` and `TauCeti.degree`
  unchanged.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_toBoundarylessModel`,
  `TauCeti.Manifold.Orientation.degree_toBoundarylessModel`: recharting a boundaryless source
  `(M, I)` to `TauCeti.BoundarylessModel I M` leaves `TauCeti.degreeAtRegularValue` and
  `TauCeti.degree` unchanged.
-/

public section

noncomputable section

open Function
open scoped ContDiff Manifold

namespace TauCeti.Manifold.Orientation

variable {E F H M F' G N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  [TopologicalSpace G] {J : ModelWithCorners ℝ F' G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  [Fintype ι]

/-- Recharting the source orientation along a continuous linear equivalence `e : E ≃L[ℝ] F` leaves
`degreeAtRegularValue` unchanged at every point of `N`. -/
@[simp]
theorem degreeAtRegularValue_transContinuousLinearEquiv (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (e : E ≃L[ℝ] F) (f : M → N) (y : N) :
    degreeAtRegularValue (o.transContinuousLinearEquiv e) oN f y =
      degreeAtRegularValue o oN f y := by
  simpa only [e.coe_toTransContinuousLinearEquiv_symm I M, comp_id] using
    (e.toTransContinuousLinearEquiv (n := 1) I M
      ).symm.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt one_ne_zero oN
      (o.isOrientationPreservingAt_id_transContinuousLinearEquiv_symm e) f y

/-- Recharting the source orientation along a continuous linear equivalence `e : E ≃L[ℝ] F` leaves
`degree` unchanged. -/
@[simp]
theorem degree_transContinuousLinearEquiv (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (e : E ≃L[ℝ] F) (f : M → N) :
    degree (o.transContinuousLinearEquiv e) oN f = degree o oN f := by
  simpa only [e.coe_toTransContinuousLinearEquiv_symm I M, comp_id] using
    (e.toTransContinuousLinearEquiv (n := 1) I M
      ).symm.degree_comp_diffeomorph_of_isOrientationPreservingAt one_ne_zero oN
      (o.isOrientationPreservingAt_id_transContinuousLinearEquiv_symm e) f

section Boundaryless

variable [I.Boundaryless]

/-- Replacing a boundaryless source `(M, I)` by `BoundarylessModel I M` leaves
`degreeAtRegularValue` unchanged at every point of `N`. -/
@[simp]
theorem degreeAtRegularValue_toBoundarylessModel (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (f : M → N) (y : N) :
    degreeAtRegularValue o.toBoundarylessModel oN
        (f ∘ (BoundarylessModel.homeomorph I M).symm) y =
      degreeAtRegularValue o oN f y := by
  simpa only [BoundarylessModel.coe_diffeomorph_symm] using
    (BoundarylessModel.diffeomorph I (M := M) 1
      ).symm.degreeAtRegularValue_comp_diffeomorph_of_isOrientationPreservingAt one_ne_zero oN
      o.isOrientationPreservingAt_diffeomorph_symm_toBoundarylessModel f y

/-- Replacing a boundaryless source `(M, I)` by `BoundarylessModel I M` leaves `degree`
unchanged. -/
@[simp]
theorem degree_toBoundarylessModel (o : Manifold.Orientation I M ι)
    (oN : Manifold.Orientation J N ι) (f : M → N) :
    degree o.toBoundarylessModel oN (f ∘ (BoundarylessModel.homeomorph I M).symm) =
      degree o oN f := by
  simpa only [BoundarylessModel.coe_diffeomorph_symm] using
    (BoundarylessModel.diffeomorph I (M := M) 1
      ).symm.degree_comp_diffeomorph_of_isOrientationPreservingAt one_ne_zero oN
      o.isOrientationPreservingAt_diffeomorph_symm_toBoundarylessModel f

end Boundaryless

end TauCeti.Manifold.Orientation
