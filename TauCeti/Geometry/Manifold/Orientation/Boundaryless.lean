/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Geometry.Manifold.Orientation.LinearEquiv
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
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv`
  (and `isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv_symm`,
  `orientationAt_toBoundarylessModel_transContinuousLinearEquiv`): recharting `BoundarylessModel`
  along `e : E ≃L[ℝ] F` preserves orientation to
  `(o.transContinuousLinearEquiv e).toBoundarylessModel` and pushes forward tangent orientations.
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

section TransContinuousLinearEquiv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The inverse recharting diffeomorphism
`(BoundarylessModel.diffeomorphTransContinuousLinearEquiv I e k).symm` preserves orientations from
`(o.transContinuousLinearEquiv e).toBoundarylessModel` to `o`. -/
theorem isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv_symm
    (o : Manifold.Orientation I M ι) (e : E ≃L[ℝ] F) (k : ℕ∞ω)
    (y : BoundarylessModel (I.transContinuousLinearEquiv e) M) :
    IsOrientationPreservingAt (o.transContinuousLinearEquiv e).toBoundarylessModel o
      (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) e k).symm y := by
  have hcoe :
      ⇑(BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) e k).symm =
        (id : M → M) ∘
          (BoundarylessModel.homeomorph (I.transContinuousLinearEquiv e) M).symm := by
    rw [BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv_symm, Function.id_comp]
  rw [hcoe]
  exact (o.isOrientationPreservingAt_id_transContinuousLinearEquiv_symm e _).comp
    ((o.transContinuousLinearEquiv e).isOrientationPreservingAt_homeomorph_symm_toBoundarylessModel
      y)

/-- The recharting diffeomorphism `BoundarylessModel.diffeomorphTransContinuousLinearEquiv I e k`
preserves orientations from `o` to `(o.transContinuousLinearEquiv e).toBoundarylessModel`. -/
theorem isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv
    (o : Manifold.Orientation I M ι) (e : E ≃L[ℝ] F) (k : ℕ∞ω) (x : M) :
    IsOrientationPreservingAt o (o.transContinuousLinearEquiv e).toBoundarylessModel
      (BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) e k) x := by
  have hcoe :
      ⇑(BoundarylessModel.diffeomorphTransContinuousLinearEquiv I (M := M) e k) =
        BoundarylessModel.homeomorph (I.transContinuousLinearEquiv e) M ∘ (id : M → M) := by
    rw [BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv, Function.comp_id]
  rw [hcoe]
  exact ((o.transContinuousLinearEquiv e).isOrientationPreservingAt_homeomorph_toBoundarylessModel
    x).comp (o.isOrientationPreservingAt_id_transContinuousLinearEquiv e x)

end TransContinuousLinearEquiv

end TauCeti.Manifold.Orientation

namespace TauCeti.Manifold.Orientation

section SelfModelTransContinuousLinearEquiv

variable {E F M ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [Fintype ι]

/-- For a continuous linear equivalence `e : E ≃L[ℝ] F` on a self-modelled `C¹` manifold
`(M, 𝓘(ℝ, E))`, the tangent orientation of `(o.transContinuousLinearEquiv e).toBoundarylessModel`
at `BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) e k x` is the pushforward of
`o.orientationAt x` along `e`. -/
theorem orientationAt_toBoundarylessModel_transContinuousLinearEquiv
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι) (e : E ≃L[ℝ] F) (k : ℕ∞ω) (x : M) :
    _root_.Orientation.map ι e.toLinearEquiv
        (o.orientationAt x : _root_.Orientation ℝ E ι) =
      (((o.transContinuousLinearEquiv e).toBoundarylessModel).orientationAt
        (BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) e k x) :
        _root_.Orientation ℝ F ι) := by
  set I' := 𝓘(ℝ, E).transContinuousLinearEquiv e
  set Φ := BoundarylessModel.diffeomorphTransContinuousLinearEquiv 𝓘(ℝ, E) (M := M) e k
  have hcoe : (Φ : M → BoundarylessModel I' M) = BoundarylessModel.homeomorph I' M ∘ id := by
    rw [BoundarylessModel.coe_diffeomorphTransContinuousLinearEquiv, Function.comp_id]
  have hpres := o.isOrientationPreservingAt_diffeomorphTransContinuousLinearEquiv e k x
  change IsOrientationPreservingAt o (o.transContinuousLinearEquiv e).toBoundarylessModel
    (Φ : M → BoundarylessModel I' M) x at hpres
  rw [hcoe] at hpres
  set e' : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ]
      TangentSpace 𝓘(ℝ, F) ((BoundarylessModel.homeomorph I' M ∘ id) x) :=
    ((tangentSpaceCastModel 𝓘(ℝ, E) x).trans e).trans
      (tangentSpaceCastModel 𝓘(ℝ, F) ((BoundarylessModel.homeomorph I' M ∘ id) x)).symm
  have hmf : (e' : TangentSpace 𝓘(ℝ, E) x →L[ℝ]
        TangentSpace 𝓘(ℝ, F) ((BoundarylessModel.homeomorph I' M ∘ id) x)) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (BoundarylessModel.homeomorph I' M ∘ id) x := by
    rw [BoundarylessModel.mfderiv_target I' 𝓘(ℝ, E) id x,
      ModelWithCorners.mfderiv_id_transContinuousLinearEquiv 𝓘(ℝ, E) e x]
    ext v
    have hcast_Φ (w : TangentSpace I' x) :
        tangentSpaceCastModel I' (id x) w = tangentSpaceCastModel I' x w := rfl
    simp only [e', I', Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply, hcast_Φ,
      ContinuousLinearEquiv.apply_symm_apply]
  have hcast_in (v : TangentSpace 𝓘(ℝ, E) x) : tangentSpaceCastModel 𝓘(ℝ, E) x v = v := rfl
  have hcast_out (w : F) :
      (tangentSpaceCastModel 𝓘(ℝ, F) ((BoundarylessModel.homeomorph I' M ∘ id) x)).symm w = w := rfl
  have he' : (e'.toLinearEquiv : E ≃ₗ[ℝ] F) = e.toLinearEquiv := by
    ext v
    simp only [e', ContinuousLinearEquiv.trans_toLinearEquiv, LinearEquiv.trans_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, hcast_in, hcast_out]
    rfl
  have h := (isOrientationPreservingAt_iff_of_coe_eq _ _ _ _ e' hmf).1 hpres
  rw [← hcoe] at h
  rw [← he']
  exact h

end SelfModelTransContinuousLinearEquiv

end TauCeti.Manifold.Orientation
