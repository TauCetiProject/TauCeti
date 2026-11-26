/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Linear changes of model coordinates

Composing a model with a continuous linear equivalence changes its vector-space coordinates,
not the smooth structure groupoid on its chart space. Thus the same maximal atlas can be used
before and after changing model coordinates, even for models with boundary or corners.

`ModelWithCorners.contDiffGroupoid_transContinuousLinearEquiv` gives this equality at every
regularity. The identity and composition laws for `ModelWithCorners.transContinuousLinearEquiv`
make repeated coordinate changes simplify to a single change; in particular a change followed
by its inverse returns the original model.

The groupoid comparison uses the same conjugation argument as Mathlib's
`ContinuousLinearEquiv.instIsManifoldtransContinuousLinearEquiv`, before choosing an atlas.
Similarly, within-range derivatives of coordinate expressions and chart transitions conjugate by the
linear equivalence (`ModelWithCorners.fderivWithin_transContinuousLinearEquiv`,
`ModelWithCorners.fderivWithin_extChartAt_transContinuousLinearEquiv`), the identity map from
`(M, I)` to `(M, I.transContinuousLinearEquiv e)` has manifold derivative `e` read through
`tangentSpaceCastModel` (`ModelWithCorners.hasMFDerivAt_id_transContinuousLinearEquiv`,
`ModelWithCorners.mfderiv_id_transContinuousLinearEquiv`), and manifold derivatives between
arbitrary charted spaces conjugate accordingly
(`ModelWithCorners.mdifferentiableAt_transContinuousLinearEquiv_iff`,
`ModelWithCorners.mfderiv_transContinuousLinearEquiv`).
Mathlib's `ContinuousLinearEquiv.toTransContinuousLinearEquiv` supplies the identity comparison
diffeomorphism on any charted manifold, with underlying map `id` in both directions.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
-/

public section

open Set
open scoped ContDiff Manifold Topology

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)

/-- The identity linear change of coordinates leaves the model unchanged. -/
@[simp]
theorem transContinuousLinearEquiv_refl :
    I.transContinuousLinearEquiv (ContinuousLinearEquiv.refl 𝕜 E) = I := by
  ext1 <;> simp [ModelWithCorners.target_eq]

/-- Successive linear changes of coordinates agree with their composite. -/
@[simp]
theorem transContinuousLinearEquiv_trans (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] G) :
    (I.transContinuousLinearEquiv e).transContinuousLinearEquiv f =
      I.transContinuousLinearEquiv (e.trans f) := by
  ext1 <;> simp [ModelWithCorners.target_eq, Function.comp_def]

/-- Differentiability within the model range of a coordinate expression `I ∘ f ∘ I.symm` is
unchanged by a continuous linear change of model coordinates. -/
theorem differentiableWithinAt_transContinuousLinearEquiv_iff (e : E ≃L[𝕜] F) (f : H → H)
    (x : H) :
    DifferentiableWithinAt 𝕜
        ((I.transContinuousLinearEquiv e) ∘ f ∘ (I.transContinuousLinearEquiv e).symm)
        (range (I.transContinuousLinearEquiv e)) ((I.transContinuousLinearEquiv e) x) ↔
      DifferentiableWithinAt 𝕜 (I ∘ f ∘ I.symm) (range I) (I x) := by
  have hcomp : (I.transContinuousLinearEquiv e) ∘ f ∘ (I.transContinuousLinearEquiv e).symm =
      e ∘ ((I ∘ f ∘ I.symm) ∘ e.symm) := by
    ext y
    simp
  rw [hcomp, I.transContinuousLinearEquiv_range e, e.image_eq_preimage_symm,
    I.coe_transContinuousLinearEquiv e, Function.comp_apply, e.comp_differentiableWithinAt_iff,
    e.symm.comp_right_differentiableWithinAt_iff, e.symm_apply_apply]

/-- A continuous linear change of model coordinates conjugates the within-range derivative of a
coordinate expression `I ∘ f ∘ I.symm` by `e`. -/
theorem fderivWithin_transContinuousLinearEquiv (e : E ≃L[𝕜] F) (f : H → H) (x : H) :
    fderivWithin 𝕜 ((I.transContinuousLinearEquiv e) ∘ f ∘ (I.transContinuousLinearEquiv e).symm)
        (range (I.transContinuousLinearEquiv e)) ((I.transContinuousLinearEquiv e) x) =
      (e : E →L[𝕜] F) ∘L fderivWithin 𝕜 (I ∘ f ∘ I.symm) (range I) (I x) ∘L
        (e.symm : F →L[𝕜] E) := by
  have hcomp : (I.transContinuousLinearEquiv e) ∘ f ∘ (I.transContinuousLinearEquiv e).symm =
      e ∘ ((I ∘ f ∘ I.symm) ∘ e.symm) := by
    ext y
    simp
  have hu : UniqueDiffWithinAt 𝕜 (e.symm ⁻¹' range I) (e (I x)) := by
    have h := (I.transContinuousLinearEquiv e).uniqueDiffWithinAt_image (x := x)
    rwa [I.transContinuousLinearEquiv_range e, e.image_eq_preimage_symm,
      I.coe_transContinuousLinearEquiv e, Function.comp_apply] at h
  rw [hcomp, I.transContinuousLinearEquiv_range e, e.image_eq_preimage_symm,
    I.coe_transContinuousLinearEquiv e, Function.comp_apply, e.comp_fderivWithin hu,
    e.symm.comp_right_fderivWithin hu, e.symm_apply_apply]

/-- A continuous linear change of model coordinates conjugates the within-range derivative of an
extended-chart transition by `e`. -/
theorem fderivWithin_extChartAt_transContinuousLinearEquiv {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (e : E ≃L[𝕜] F) (α β x : M) :
    fderivWithin 𝕜
        (extChartAt (I.transContinuousLinearEquiv e) β ∘
          (extChartAt (I.transContinuousLinearEquiv e) α).symm)
        (range (I.transContinuousLinearEquiv e))
        (extChartAt (I.transContinuousLinearEquiv e) α x) =
      (e : E →L[𝕜] F) ∘L
        fderivWithin 𝕜 (extChartAt I β ∘ (extChartAt I α).symm) (range I)
          (extChartAt I α x) ∘L (e.symm : F →L[𝕜] E) := by
  simpa only [Function.comp_def, extChartAt_coe, extChartAt_coe_symm] using
    I.fderivWithin_transContinuousLinearEquiv e (chartAt H β ∘ (chartAt H α).symm) (chartAt H α x)

/-- For any charted space `M`, the identity map `id : M → M` from `(M, I)` to
`(M, I.transContinuousLinearEquiv e)` has manifold derivative `e` at every point `x`, read through
the tangent-to-model identifications `tangentSpaceCastModel`. -/
theorem hasMFDerivAt_id_transContinuousLinearEquiv {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (e : E ≃L[𝕜] F) (x : M) :
    HasMFDerivAt I (I.transContinuousLinearEquiv e) (id : M → M) x
      (((tangentSpaceCastModel I x).trans e).trans
        (tangentSpaceCastModel (I.transContinuousLinearEquiv e) x).symm :
          TangentSpace I x →L[𝕜] TangentSpace (I.transContinuousLinearEquiv e) x) := by
  refine ⟨continuousAt_id, ?_⟩
  have hcast :
      (tangentSpaceCastModel (I.transContinuousLinearEquiv e) x : _ →L[𝕜] F) ∘L
        (((tangentSpaceCastModel I x).trans e).trans
          (tangentSpaceCastModel (I.transContinuousLinearEquiv e) x).symm :
            TangentSpace I x →L[𝕜] TangentSpace (I.transContinuousLinearEquiv e) x) ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜] _) = (e : E →L[𝕜] F) := by
    ext v
    simp
  have heq : writtenInExtChartAt I (I.transContinuousLinearEquiv e) x (id : M → M) =ᶠ[
      𝓝[range I] (extChartAt I x x)] e := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, id_eq, id_eq,
      I.coe_extChartAt_transContinuousLinearEquiv, Function.comp_apply,
      (extChartAt I x).right_inv hy]
  have hx : writtenInExtChartAt I (I.transContinuousLinearEquiv e) x (id : M → M)
      (extChartAt I x x) = e (extChartAt I x x) := by
    rw [writtenInExtChartAt, Function.comp_apply, Function.comp_apply, id_eq, id_eq,
      I.coe_extChartAt_transContinuousLinearEquiv, Function.comp_apply,
      (extChartAt I x).right_inv (mem_extChartAt_target x)]
  rw [id_eq, hcast]
  exact e.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq hx

/-- The manifold derivative of `id : M → M` from `(M, I)` to `(M, I.transContinuousLinearEquiv e)`
at `x` is `e`, read through the tangent-to-model identifications `tangentSpaceCastModel`. -/
@[simp]
theorem mfderiv_id_transContinuousLinearEquiv {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (e : E ≃L[𝕜] F) (x : M) :
    mfderiv I (I.transContinuousLinearEquiv e) (id : M → M) x =
      (((tangentSpaceCastModel I x).trans e).trans
        (tangentSpaceCastModel (I.transContinuousLinearEquiv e) x).symm :
          TangentSpace I x →L[𝕜] TangentSpace (I.transContinuousLinearEquiv e) x) :=
  (I.hasMFDerivAt_id_transContinuousLinearEquiv e x).mfderiv

/-- Continuous linear changes of the source and target model coordinates conjugate
`writtenInExtChartAt` by `e` and `e'`. -/
theorem writtenInExtChartAt_transContinuousLinearEquiv
    {E' F' H' M N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [TopologicalSpace H']
    (J : ModelWithCorners 𝕜 E' H') [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (e : E ≃L[𝕜] F) (e' : E' ≃L[𝕜] F') (x : M) (f : M → N) :
    writtenInExtChartAt (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv e') x f =
      e' ∘ (writtenInExtChartAt I J x f ∘ e.symm) := by
  ext y
  simp [writtenInExtChartAt]

/-- Continuous linear changes of the source and target model coordinates leave manifold
differentiability at a point unchanged. -/
@[simp]
theorem mdifferentiableAt_transContinuousLinearEquiv_iff
    {E' F' H' M N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [TopologicalSpace H']
    (J : ModelWithCorners 𝕜 E' H') [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (e : E ≃L[𝕜] F) (e' : E' ≃L[𝕜] F') {f : M → N} {x : M} :
    MDifferentiableAt (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv e') f x ↔
      MDifferentiableAt I J f x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff,
    I.writtenInExtChartAt_transContinuousLinearEquiv J e e' x f,
    I.transContinuousLinearEquiv_range e, e.image_eq_preimage_symm,
    I.coe_extChartAt_transContinuousLinearEquiv e, Function.comp_apply,
    e'.comp_differentiableWithinAt_iff, e.symm.comp_right_differentiableWithinAt_iff,
    e.symm_apply_apply]

/-- Continuous linear changes of the source and target model coordinates conjugate the manifold
derivative `mfderiv` at `x` by `e` and `e'`, read through `tangentSpaceCastModel`. -/
theorem mfderiv_transContinuousLinearEquiv
    {E' F' H' M N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [TopologicalSpace H']
    (J : ModelWithCorners 𝕜 E' H') [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    (e : E ≃L[𝕜] F) (e' : E' ≃L[𝕜] F') (f : M → N) (x : M) :
    mfderiv (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv e') f x =
      (((tangentSpaceCastModel J (f x)).trans e').trans
          (tangentSpaceCastModel (J.transContinuousLinearEquiv e') (f x)).symm :
            TangentSpace J (f x) →L[𝕜] TangentSpace (J.transContinuousLinearEquiv e') (f x)) ∘L
        mfderiv I J f x ∘L
        (((tangentSpaceCastModel (I.transContinuousLinearEquiv e) x).trans e.symm).trans
          (tangentSpaceCastModel I x).symm :
            TangentSpace (I.transContinuousLinearEquiv e) x →L[𝕜] TangentSpace I x) := by
  have hu : UniqueDiffWithinAt 𝕜 (e.symm ⁻¹' range I) (e (extChartAt I x x)) := by
    have h := (I.transContinuousLinearEquiv e).uniqueDiffWithinAt_image (x := chartAt H x x)
    rwa [I.transContinuousLinearEquiv_range e, e.image_eq_preimage_symm,
      I.coe_transContinuousLinearEquiv e, Function.comp_apply] at h
  by_cases hf : MDifferentiableAt I J f x
  · have hf' :
        MDifferentiableAt (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv e') f x :=
      (I.mdifferentiableAt_transContinuousLinearEquiv_iff J e e').2 hf
    rw [hf'.mfderiv, hf.mfderiv,
      I.writtenInExtChartAt_transContinuousLinearEquiv J e e' x f,
      I.transContinuousLinearEquiv_range e, e.image_eq_preimage_symm,
      I.coe_extChartAt_transContinuousLinearEquiv e, Function.comp_apply,
      e'.comp_fderivWithin hu, e.symm.comp_right_fderivWithin hu, e.symm_apply_apply]
    ext v
    simp
  · have hf' :
        ¬ MDifferentiableAt (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv e')
          f x :=
      mt (I.mdifferentiableAt_transContinuousLinearEquiv_iff J e e').1 hf
    simp [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hf']

private theorem contDiffGroupoid_le_transContinuousLinearEquiv (e : E ≃L[𝕜] F)
    (n : ℕ∞ω) : contDiffGroupoid n I ≤ contDiffGroupoid n (I.transContinuousLinearEquiv e) := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact e.contDiff.comp_contDiffOn
    (hfs.comp e.symm.contDiff.contDiffOn (by
      simp [preimage_comp, range_comp, mapsTo_iff_subset_preimage,
        ContinuousLinearEquiv.image_eq_preimage_symm]))

/-- A continuous linear change of model coordinates leaves the smooth structure groupoid on
`H` unchanged. No boundarylessness or finite-dimensionality assumption is needed. -/
@[simp]
theorem contDiffGroupoid_transContinuousLinearEquiv (e : E ≃L[𝕜] F) (n : ℕ∞ω) :
    contDiffGroupoid n (I.transContinuousLinearEquiv e) = contDiffGroupoid n I := by
  apply le_antisymm
  · simpa using
      contDiffGroupoid_le_transContinuousLinearEquiv (I.transContinuousLinearEquiv e) e.symm n
  · exact contDiffGroupoid_le_transContinuousLinearEquiv I e n

/-- The maximal atlas of a charted space is unchanged by a continuous linear change of model
coordinates. This compares the actual sets of charts, not just manifold instances. -/
@[simp]
theorem maximalAtlas_transContinuousLinearEquiv {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (e : E ≃L[𝕜] F) (n : ℕ∞ω) :
    IsManifold.maximalAtlas (I.transContinuousLinearEquiv e) n M =
      IsManifold.maximalAtlas I n M := by
  simp only [IsManifold.maximalAtlas, contDiffGroupoid_transContinuousLinearEquiv]

end ModelWithCorners

namespace ContinuousLinearEquiv

variable {𝕜 E F H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M) [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The underlying equivalence of `toTransContinuousLinearEquiv` is the identity equivalence. -/
@[simp]
theorem toTransContinuousLinearEquiv_toEquiv (e : E ≃L[𝕜] F) :
    (toTransContinuousLinearEquiv (n := n) I M e).toEquiv = Equiv.refl M := (rfl)

/-- The comparison diffeomorphism `toTransContinuousLinearEquiv` has underlying map `id`. -/
@[simp]
theorem coe_toTransContinuousLinearEquiv (e : E ≃L[𝕜] F) :
    ⇑(toTransContinuousLinearEquiv (n := n) I M e) = id := (rfl)

/-- The inverse of `toTransContinuousLinearEquiv` has underlying map `id`. -/
@[simp]
theorem coe_toTransContinuousLinearEquiv_symm (e : E ≃L[𝕜] F) :
    ⇑(toTransContinuousLinearEquiv (n := n) I M e).symm = id := (rfl)

end ContinuousLinearEquiv
