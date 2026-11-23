/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Transporting smooth orientations to `BoundarylessModel`

Let `(M, I)` be a boundaryless `C¹` manifold modelled on a finite-dimensional real normed space `E`.
Pulling an orientation `o` of `M` back along the inverse of the identity diffeomorphism
`TauCeti.BoundarylessModel.diffeomorph I 1` equips the vector-space-modelled copy
`TauCeti.BoundarylessModel I M` with an orientation `o.toBoundarylessModel` under which both
directions of `TauCeti.BoundarylessModel.homeomorph I M` preserve orientation at every point.

When a change of model vector space `L : E ≃L[ℝ] F` is also needed, compose first with
`TauCeti.Manifold.Orientation.transContinuousLinearEquiv`:
`(o.transContinuousLinearEquiv L).toBoundarylessModel`.

## Main definitions

* `TauCeti.Manifold.Orientation.toBoundarylessModel`: transport a manifold orientation of a
  boundaryless `C¹` manifold `(M, I)` to `TauCeti.BoundarylessModel I M`.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_homeomorph_symm_toBoundarylessModel`,
  `TauCeti.Manifold.Orientation.isOrientationPreservingAt_homeomorph_toBoundarylessModel`: both
  directions of `TauCeti.BoundarylessModel.homeomorph I M` preserve orientation between `o` and
  `o.toBoundarylessModel`.
* `TauCeti.Manifold.Orientation.eq_toBoundarylessModel_iff`: `o.toBoundarylessModel` is the unique
  orientation of `TauCeti.BoundarylessModel I M` from which
  `(TauCeti.BoundarylessModel.homeomorph I M).symm` preserves orientation everywhere.
* `TauCeti.Manifold.Orientation.toBoundarylessModel_neg`,
  `TauCeti.Manifold.Orientation.toBoundarylessModel_injective`,
  `TauCeti.Manifold.Orientation.toBoundarylessModel_inj`: compatibility with negation and
  injectivity.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Manifold.Orientation

variable {E H M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [Fintype ι]

/-- Transport an orientation `o` of a boundaryless `C¹` manifold `(M, I)` to its
vector-space-modelled copy `BoundarylessModel I M`, by pulling `o` back along the inverse of the
identity diffeomorphism `BoundarylessModel.diffeomorph I 1`. -/
def toBoundarylessModel (o : Manifold.Orientation I M ι) :
    Manifold.Orientation 𝓘(ℝ, E) (BoundarylessModel I M) ι :=
  o.pullback (BoundarylessModel.diffeomorph I (M := M) 1).symm.contMDiff
    (fun _ ↦ (BoundarylessModel.diffeomorph I (M := M) 1).symm.isInvertible_mfderiv one_ne_zero)
    o.card_eq

/-- Explicit pullback formula for `toBoundarylessModel`. -/
theorem toBoundarylessModel_def (o : Manifold.Orientation I M ι) :
    o.toBoundarylessModel =
      o.pullback (BoundarylessModel.diffeomorph I (M := M) 1).symm.contMDiff
        (fun _ ↦ (BoundarylessModel.diffeomorph I (M := M) 1).symm.isInvertible_mfderiv one_ne_zero)
        o.card_eq :=
  (rfl)

/-- Reversing the orientation commutes with transporting to `BoundarylessModel I M`. -/
@[simp]
theorem toBoundarylessModel_neg (o : Manifold.Orientation I M ι) :
    (-o).toBoundarylessModel = -o.toBoundarylessModel :=
  pullback_neg o _ _ _

/-- The inverse identity diffeomorphism from `BoundarylessModel I M` to `M` preserves orientation
from `o.toBoundarylessModel` to `o` at every point. -/
theorem isOrientationPreservingAt_diffeomorph_symm_toBoundarylessModel
    (o : Manifold.Orientation I M ι) (x : BoundarylessModel I M) :
    IsOrientationPreservingAt o.toBoundarylessModel o
      (BoundarylessModel.diffeomorph I (M := M) 1).symm x :=
  isOrientationPreservingAt_pullback o _ _ _ x

/-- The inverse identity homeomorphism `(BoundarylessModel.homeomorph I M).symm` preserves
orientation from `o.toBoundarylessModel` to `o` at every point. -/
@[simp]
theorem isOrientationPreservingAt_homeomorph_symm_toBoundarylessModel
    (o : Manifold.Orientation I M ι) (x : BoundarylessModel I M) :
    IsOrientationPreservingAt o.toBoundarylessModel o
      (BoundarylessModel.homeomorph I M).symm x := by
  simpa only [BoundarylessModel.coe_diffeomorph_symm] using
    o.isOrientationPreservingAt_diffeomorph_symm_toBoundarylessModel x

/-- The identity homeomorphism `BoundarylessModel.homeomorph I M` preserves orientation from `o` to
`o.toBoundarylessModel` at every point. -/
@[simp]
theorem isOrientationPreservingAt_homeomorph_toBoundarylessModel
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationPreservingAt o o.toBoundarylessModel (BoundarylessModel.homeomorph I M) x := by
  let Φ := BoundarylessModel.diffeomorph I (M := M) 1
  have hsymm : Φ.symm.symm = Φ := rfl
  simpa only [hsymm, Φ, BoundarylessModel.coe_diffeomorph] using
    (o.isOrientationPreservingAt_diffeomorph_symm_toBoundarylessModel
      (Φ.symm.symm x)).diffeomorph_symm one_ne_zero

/-- `o.toBoundarylessModel` is the unique orientation of `BoundarylessModel I M` from which
`(BoundarylessModel.homeomorph I M).symm` preserves orientation at every point. -/
theorem eq_toBoundarylessModel_iff (o : Manifold.Orientation I M ι)
    {o' : Manifold.Orientation 𝓘(ℝ, E) (BoundarylessModel I M) ι} :
    o' = o.toBoundarylessModel ↔
      ∀ x, IsOrientationPreservingAt o' o (BoundarylessModel.homeomorph I M).symm x := by
  simpa only [toBoundarylessModel_def, BoundarylessModel.coe_diffeomorph_symm] using
    eq_pullback_iff o (BoundarylessModel.diffeomorph I (M := M) 1).symm.contMDiff
      (fun _ ↦ (BoundarylessModel.diffeomorph I (M := M) 1).symm.isInvertible_mfderiv one_ne_zero)
      o.card_eq (o := o')

/-- Transporting orientations to `BoundarylessModel I M` is injective. -/
theorem toBoundarylessModel_injective :
    Function.Injective (toBoundarylessModel (I := I) (M := M) (ι := ι)) := by
  intro o₁ o₂ h
  ext x
  have h₁ := o₁.isOrientationPreservingAt_homeomorph_symm_toBoundarylessModel
    (BoundarylessModel.homeomorph I M x)
  have h₂ := o₂.isOrientationPreservingAt_homeomorph_symm_toBoundarylessModel
    (BoundarylessModel.homeomorph I M x)
  rw [← h] at h₂
  exact Homeomorph.symm_apply_apply (BoundarylessModel.homeomorph I M) x ▸ h₁.orientationAt_eq h₂

@[simp]
theorem toBoundarylessModel_inj {o₁ o₂ : Manifold.Orientation I M ι} :
    o₁.toBoundarylessModel = o₂.toBoundarylessModel ↔ o₁ = o₂ :=
  toBoundarylessModel_injective.eq_iff

end TauCeti.Manifold.Orientation
