/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Orientations normalized by an invertible derivative

A C¹ map into a normed space whose actual manifold derivative is invertible everywhere
pulls back any orientation of that space. The construction includes boundary and corner points.
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*} [Fintype ι]

private theorem eventually_mapOrientation_mfDerivEquiv {f : M → X}
    (hf : ContMDiff I 𝓘(ℝ, X) 1 f) (F : ∀ x, TangentSpace I x ≃L[ℝ] X)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, X) f x))
    (o : _root_.Orientation ℝ X ι) (hι : Fintype.card ι = Module.finrank ℝ E) (a : M) :
    ∀ᶠ x in 𝓝 a, ∀ hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet,
      (trivializationAt E (TangentSpace I) a).mapOrientation ι hx
        (_root_.Orientation.map ι (F x).symm.toLinearEquiv o) =
      (trivializationAt E (TangentSpace I) a).mapOrientation ι
        (FiberBundle.mem_baseSet_trivializationAt' a)
        (_root_.Orientation.map ι (F a).symm.toLinearEquiv o) := by
  let e := trivializationAt E (TangentSpace I) a
  let ha := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) a
  let G := (F a).symm.trans (e.continuousLinearEquivAt ℝ a ha)
  let c := fun x ↦ G.toContinuousLinearMap.comp
    (inTangentCoordinates I 𝓘(ℝ, X) id f (mfderiv I 𝓘(ℝ, X) f) a x)
  have hc : ContinuousAt c a := (continuousAt_const.clm_comp
    (((hf a).mfderiv_const (m := 0) (by simp)).continuousAt))
  have heq (x : M) (hx : x ∈ e.baseSet) :
      c x =
        (((e.continuousLinearEquivAt ℝ x hx).symm.trans (F x)).trans G).toContinuousLinearMap := by
    have hx' : x ∈ (chartAt H a).source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
    dsimp only [c]
    rw [inTangentCoordinates_eq id f (mfderiv I 𝓘(ℝ, X) f) hx' (by simp)]
    simp only [TangentBundle.coordChange_model_space, id_eq]
    ext v
    -- The normed-model tangent identification makes the target coordinate change the identity.
    change G ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x))
      (mfderiv I 𝓘(ℝ, X) f x
        ((tangentBundleCore I M).coordChange (achart H a) (achart H x) x v))) =
      G (F x ((e.continuousLinearEquivAt ℝ x hx).symm v))
    rw [← TangentBundle.symmL_trivializationAt_eq_core hx']
    have hread := congrArg (fun L : TangentSpace I x →L[ℝ] X ↦
      L ((e.continuousLinearEquivAt ℝ x hx).symm v)) (hF x)
    rw [Trivialization.symm_continuousLinearEquivAt_eq] at hread
    rw [Trivialization.symm_continuousLinearEquivAt_eq]
    exact congrArg G hread.symm
  have hca : c a = ContinuousLinearMap.id ℝ E := by
    rw [heq a ha]
    ext v
    -- Expose evaluation of the composed equivalences so their inverse laws apply.
    change (e.continuousLinearEquivAt ℝ a ha)
      ((F a).symm ((F a) ((e.continuousLinearEquivAt ℝ a ha).symm v))) = v
    simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hp : ∀ᶠ x in 𝓝 a, 0 < (c x).det :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp hc).eventually
      (by simpa [hca, ContinuousLinearMap.det] using (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  filter_upwards [hp] with x hx hxmem
  let K := ((e.continuousLinearEquivAt ℝ x hxmem).symm.trans (F x)).trans G
  let oa := e.mapOrientation ι ha (_root_.Orientation.map ι (F a).symm.toLinearEquiv o)
  have hk : _root_.Orientation.map ι K.toLinearEquiv oa = oa := by
    have h := (_root_.Orientation.map_eq_map_iff_det_mul_pos oa K.toLinearEquiv
      (LinearEquiv.refl ℝ E) hι).mpr (by
        have hrefl : LinearMap.det (LinearEquiv.refl ℝ E : E →ₗ[ℝ] E) = 1 :=
          LinearMap.det_id
        rw [hrefl, mul_one]
        -- The continuous-map determinant is the determinant of its underlying linear map.
        change 0 < K.toContinuousLinearMap.det
        exact (heq x hxmem) ▸ hx)
    simpa using h
  apply (_root_.Orientation.map ι K.toLinearEquiv).injective
  rw [hk]
  dsimp only [oa]
  simp only [Trivialization.mapOrientation_apply, ← _root_.Orientation.map_trans]
  have hcomp : ((F x).symm.toLinearEquiv.trans (e.linearEquivAt ℝ x hxmem)).trans
      K.toLinearEquiv = (F a).symm.toLinearEquiv.trans (e.linearEquivAt ℝ a ha) := by
    ext v
    -- `linearEquivAt` is the linear part of `continuousLinearEquivAt`; expose composition.
    change (e.continuousLinearEquivAt ℝ a ha)
      ((F a).symm ((F x) ((e.continuousLinearEquivAt ℝ x hxmem).symm
        ((e.continuousLinearEquivAt ℝ x hxmem) ((F x).symm v))))) =
      (e.continuousLinearEquivAt ℝ a ha) ((F a).symm v)
    simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcomp]

/-- Pull back an orientation by a C¹ map with an everywhere invertible actual derivative.
The model orientation chooses a representative; the tangent orientation is fixed by `o`. -/
def ofMFDerivEquiv {f : M → X} (hf : ContMDiff I 𝓘(ℝ, X) 1 f)
    (F : ∀ x, TangentSpace I x ≃L[ℝ] X)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, X) f x))
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : _root_.Orientation ℝ X ι) : Manifold.Orientation I M ι :=
  ofVectorBundleOrientation model hι
    ⟨fun x ↦ _root_.Orientation.map ι (F x).symm.toLinearEquiv o,
      eventually_mapOrientation_mfDerivEquiv hf F hF o hι⟩

/-- The derivative sends the induced tangent orientation to the chosen target orientation,
including at boundary and corner points. -/
@[simp]
theorem map_orientationAt_ofMFDerivEquiv {f : M → X} (hf : ContMDiff I 𝓘(ℝ, X) 1 f)
    (F : ∀ x, TangentSpace I x ≃L[ℝ] X)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, X) f x))
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : _root_.Orientation ℝ X ι) (x : M) :
    _root_.Orientation.map ι (F x).toLinearEquiv
      ((ofMFDerivEquiv hf F hF model hι o).orientationAt x) = o := by
  simp only [ofMFDerivEquiv, orientationAt_ofVectorBundleOrientation,
    VectorBundleOrientation.coe_mk]
  rw [← _root_.Orientation.map_trans]
  simp

end TauCeti.Manifold.Orientation
