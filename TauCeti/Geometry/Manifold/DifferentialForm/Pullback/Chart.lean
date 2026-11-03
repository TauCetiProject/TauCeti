/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Coordinate expressions of actual manifold pullback

The coordinate expression of a pullback uses the within-range derivative of the map composed
with the inverse source chart. This is the actual manifold chain rule, including boundary
points, and supplies the coefficient transport used in interval and product comparisons.
In top degree, the coefficient of a pullback in a basis is the coordinate Jacobian determinant
times the coefficient of the form.
Pulling a flat form back along a preferred chart and reading it in the same chart recovers the
flat form on the chart target, which is how flat constructions in a chart are moved to the
manifold.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti.RoughForm

variable {E H M E' H' M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The actual pullback's coefficient in a preferred source chart is obtained from the
within-range derivative of the composite with its inverse chart. -/
theorem inChartAt_mpullback (ω : RoughForm I' M' F k) (f : M → M') (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target)
    (hf : MDifferentiableAt I I' f ((extChartAt I α).symm z)) :
    (mpullback I I' f ω).inChartAt α z =
      (ω (f ((extChartAt I α).symm z))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) I' (f ∘ (extChartAt I α).symm) (range I) z) := by
  have hd := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, E)) (I' := I) (I'' := I') z hf
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α hz)
      |>.uniqueMDiffWithinAt)
  ext v
  rw [inChartAt_apply, mpullback_apply]
  have he := congrArg (fun L : E →L[ℝ] TangentSpace I' (f ((extChartAt I α).symm z)) ↦
    ω (f ((extChartAt I α).symm z)) (fun i ↦ L (v i))) hd
  exact he.symm

/-- The within-set pullback of a form along a map `f` from a normed space, at a point `w` sent into
the preferred chart at `c`, is the flat pullback of the coordinate expression of the form in that
chart along the coordinate expression of `f`. -/
theorem mpullbackWithin_eq_compContinuousLinearMap (φ : RoughForm I M F k) {f : E' → M}
    {s : Set E'} {w : E'} (c : M) (hfc : f w ∈ (extChartAt I c).source)
    (hf : MDifferentiableWithinAt 𝓘(ℝ, E') I f s w) (hs : UniqueDiffWithinAt ℝ s w) :
    mpullbackWithin 𝓘(ℝ, E') I f s φ w =
      (φ.inChartAt c (extChartAt I c (f w))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I c ∘ f) s w) := by
  set e := extChartAt I c
  have hpre : f ⁻¹' e.source ∈ 𝓝[s] w :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds' hfc)
  have hfe : f =ᶠ[𝓝[s] w] e.symm ∘ (e ∘ f) := by
    filter_upwards [hpre] with a ha
    exact (e.left_inv ha).symm
  have hg : MDifferentiableWithinAt 𝓘(ℝ, E') 𝓘(ℝ, E) (e ∘ f) s w :=
    (mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source] using hfc))
      |>.comp_mdifferentiableWithinAt w hf
  have hrange : (e ∘ f) ⁻¹' range I ∈ 𝓝[s] w := by
    filter_upwards [hpre] with a ha
    exact extChartAt_target_subset_range c (e.map_source ha)
  have hd : mfderivWithin 𝓘(ℝ, E') I f s w =
      (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) (e (f w))).comp
        (mfderivWithin 𝓘(ℝ, E') 𝓘(ℝ, E) (e ∘ f) s w) := by
    rw [hfe.mfderivWithin_eq (e.left_inv hfc).symm]
    exact mfderivWithin_comp_of_preimage_mem_nhdsWithin w
      (mdifferentiableWithinAt_extChartAt_symm (e.map_source hfc)) hg hrange
      hs.uniqueMDiffWithinAt
  ext v
  have h := inChartAt_apply φ c (e (f w)) (fun i ↦ fderivWithin ℝ (e ∘ f) s w (v i))
  rw [e.left_inv hfc] at h
  rw [mpullbackWithin_apply, hd, mfderivWithin_eq_fderivWithin]
  exact h.symm

end TauCeti.RoughForm

namespace TauCeti.RoughForm

variable {E H M X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- For a model-valued map, actual pullback coefficients use its ordinary within-range
Fréchet derivative, with the canonical model tangent identification made explicit. -/
theorem inChartAt_mpullback_modelSpace (ω : RoughForm 𝓘(ℝ, X) X F k) (f : M → X)
    (α : M) {z : E} (hz : z ∈ (extChartAt I α).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, X) f ((extChartAt I α).symm z)) :
    (mpullback I 𝓘(ℝ, X) f ω).inChartAt α z =
      (ω (f ((extChartAt I α).symm z))).compContinuousLinearMap
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ)
          (f ((extChartAt I α).symm z))).symm.toContinuousLinearMap.comp
          (fderivWithin ℝ (f ∘ (extChartAt I α).symm) (range I) z)) := by
  rw [inChartAt_mpullback ω f α hz hf, mfderivWithin_eq_fderivWithin]
  rfl

/-- Pulling a flat form back along a preferred extended chart and reading the result in the same
chart recovers the flat form on the chart target. -/
theorem inChartAt_mpullback_extChartAt (ω : RoughForm 𝓘(ℝ, E) E F k) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    (mpullback I 𝓘(ℝ, E) (extChartAt I α) ω).inChartAt α z = ω z := by
  have hsource : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hz
  have hid : extChartAt I α ∘ (extChartAt I α).symm =ᶠ[𝓝[range I] z] id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with w hw
    exact (extChartAt I α).right_inv hw
  rw [inChartAt_mpullback_modelSpace ω _ α hz (mdifferentiableAt_extChartAt hsource),
    hid.fderivWithin_eq ((extChartAt I α).right_inv hz),
    fderivWithin_id (I.uniqueDiffOn _ (extChartAt_target_subset_range α hz))]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  -- The model tangent identifications are identities, and the chart image of the point is `z`.
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearEquiv.coe_coe]
  exact congrArg (fun y : E ↦ ω y v) ((extChartAt I α).right_inv hz)

end TauCeti.RoughForm

namespace TauCeti.RoughForm

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

/-- The coefficient of a pullback in a preferred chart of the source is the determinant of the
coordinate expression of the map times the coefficient of the form in a preferred chart of the
target. Derivatives are taken within the model range, so boundary and corner points are
included. -/
theorem inChartAt_mpullback_apply_basis_eq_det_mul (φ : RoughForm J N ℝ k)
    (b : Module.Basis (Fin k) ℝ E) {f : M → N} {β : M} {α : N} {x : M}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt J α).source)
    (hf : MDifferentiableAt I J f x) :
    (mpullback I J f φ).inChartAt β (extChartAt I β x) b =
      (fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I)
        (extChartAt I β x)).det * φ.inChartAt α (extChartAt J α (f x)) b := by
  have hz := (extChartAt I β).map_source hx
  have hfz : MDifferentiableAt I J f ((extChartAt I β).symm (extChartAt I β x)) := by
    rwa [(extChartAt I β).left_inv hx]
  have hg : MDifferentiableWithinAt 𝓘(ℝ, E) J (f ∘ (extChartAt I β).symm) (range I)
      (extChartAt I β x) :=
    hfz.comp_mdifferentiableWithinAt _ (mdifferentiableWithinAt_extChartAt_symm hz)
  have hgα : (f ∘ (extChartAt I β).symm) (extChartAt I β x) ∈ (extChartAt J α).source := by
    simpa only [Function.comp_apply, (extChartAt I β).left_inv hx] using hfx
  have hw : (mpullback I J f φ).inChartAt β (extChartAt I β x) =
      mpullbackWithin 𝓘(ℝ, E) J (f ∘ (extChartAt I β).symm) (range I) φ (extChartAt I β x) := by
    rw [RoughForm.inChartAt_mpullback φ f β hz hfz]
    ext v
    rw [mpullbackWithin_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    -- The two sides differ only by unfolding `Function.comp`.
    rfl
  rw [hw, RoughForm.mpullbackWithin_eq_compContinuousLinearMap φ α hgα hg
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range β hz)),
    ContinuousAlternatingMap.compContinuousLinearMap_apply_basis]
  simp only [Function.comp_apply, (extChartAt I β).left_inv hx]

end TauCeti.RoughForm
