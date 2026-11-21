/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

import TauCeti.Geometry.Manifold.DifferentialForm.Chart

/-!
# Coordinate expressions of actual manifold pullback

The coordinate expression of a pullback uses the within-range derivative of the map composed
with the inverse source chart. This is the actual manifold chain rule, including boundary
points, and supplies the coefficient transport used in interval and product comparisons.
In top degree, the coefficient of a pullback in a basis is the coordinate Jacobian determinant
times the coefficient of the form; when the two manifolds are modelled on different spaces, the
Jacobian is read in the source model through a linear equivalence of the model spaces.
Pulling a flat form back along a preferred chart and reading it in the same chart recovers the
flat form on the chart target, which is how flat constructions in a chart are moved to the
manifold; conversely, evaluating a form `φ` on the chart source agrees with evaluating
`φ.inChartAt α` on `mvfderiv I (extChartAt I α)` (`TauCeti.RoughForm.apply_eq_inChartAt_mvfderiv`).
Near time `t`, the pullback along a family of maps which sends `y` into the chart at `y` at time `t`
is the flat pullback along the family read in the chart at `y`
(`TauCeti.RoughForm.eventuallyEq_mpullback_compContinuousLinearMap`).
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

variable [IsManifold I' 1 M'] in
/-- The coefficient of the pullback in a preferred source chart `β`, at a chart coordinate `z` whose
image under `f` lies in the preferred chart at `α`, is the flat pullback of the coordinate
expression of the form in the chart at `α` along the derivative of the coordinate expression
of `f`. -/
theorem inChartAt_mpullback_eq_compContinuousLinearMap (ω : RoughForm I' M' F k) {f : M → M'}
    (β : M) (α : M') {z : E} (hz : z ∈ (extChartAt I β).target)
    (hf : MDifferentiableAt I I' f ((extChartAt I β).symm z))
    (hfα : f ((extChartAt I β).symm z) ∈ (extChartAt I' α).source) :
    (mpullback I I' f ω).inChartAt β z =
      (ω.inChartAt α (extChartAt I' α (f ((extChartAt I β).symm z)))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I) z) := by
  have hg : MDifferentiableWithinAt 𝓘(ℝ, E) I' (f ∘ (extChartAt I β).symm) (range I) z :=
    hf.comp_mdifferentiableWithinAt _ (mdifferentiableWithinAt_extChartAt_symm hz)
  have hw : (mpullback I I' f ω).inChartAt β z =
      mpullbackWithin 𝓘(ℝ, E) I' (f ∘ (extChartAt I β).symm) (range I) ω z := by
    rw [inChartAt_mpullback ω f β hz hf]
    ext v
    rw [mpullbackWithin_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    -- The two sides differ only by unfolding `Function.comp`.
    rfl
  rw [hw, mpullbackWithin_eq_compContinuousLinearMap ω
    (f := f ∘ (extChartAt I β).symm) (s := range I) (w := z) α hfα hg
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range β hz))]
  simp only [Function.comp_apply]

variable [IsManifold I' 1 M'] in
/-- The pullback of a form at `x` along a map `f`, with `f x` in the preferred chart at `c`, is the
flat pullback of the coordinate expression of the form in that chart along the coordinate
expression of `f` from the preferred chart at `x`. -/
theorem mpullback_eq_compContinuousLinearMap (ω : RoughForm I' M' F k) {f : M → M'} {x : M}
    (c : M') (hf : MDifferentiableAt I I' f x) (hfc : f x ∈ (extChartAt I' c).source) :
    mpullback I I' f ω x =
      (ω.inChartAt c (extChartAt I' c (f x))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I' c ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x)) := by
  have hf' : MDifferentiableAt I I' f ((extChartAt I x).symm (extChartAt I x x)) := by
    rwa [extChartAt_to_inv]
  rw [← inChartAt_extChartAt_self (mpullback I I' f ω) x,
    inChartAt_mpullback_eq_compContinuousLinearMap ω x c (mem_extChartAt_target x) hf'
      (by rwa [extChartAt_to_inv])]
  simp only [extChartAt_to_inv]
  -- `TangentSpace I x` is definitionally the model space `E`, which is what `rfl` unfolds.
  rfl

/-- Near time `t`, the pullback of a form at `y` along a family of maps `ψᵤ` which sends `y` into
the chart at `c` at time `t` and is jointly `C¹` at `(t, y)` is the flat pullback of its chart
expression at `c` along the family read from the chart at `y`. -/
theorem eventuallyEq_mpullback_compContinuousLinearMap [I.Boundaryless] [IsManifold I' 1 M']
    (α : RoughForm I' M' F k) {ψ : ℝ → M → M'} {t : ℝ} {y : M} (c : M')
    (hψt : ψ t y ∈ (extChartAt I' c).source)
    (hsmooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I' 1 (fun p : ℝ × M ↦ ψ p.1 p.2) (t, y)) :
    (fun u ↦ mpullback I I' (ψ u) α y) =ᶠ[𝓝 t] fun u ↦
      (α.inChartAt c (extChartAt I' c (ψ u ((extChartAt I y).symm (extChartAt I y y))))
        ).compContinuousLinearMap
        (fderiv ℝ (fun z ↦ extChartAt I' c (ψ u ((extChartAt I y).symm z)))
          (extChartAt I y y)) := by
  -- Near time `t`, the maps `ψᵤ` are differentiable at `y` and keep `y` in the chart at `y`.
  have hψ : ∀ᶠ u in 𝓝 t, MDifferentiableAt I I' (ψ u) y := by
    have h := ((continuous_id.prodMk continuous_const).tendsto t).eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hsmooth)
    filter_upwards [h] with u hu
    exact (hu.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_id) rfl).mdifferentiableAt
      (by norm_num)
  have hcont : ContinuousAt (fun u ↦ ψ u y) t :=
    hsmooth.continuousAt.comp (f := fun u : ℝ ↦ (u, y))
      (continuous_id.prodMk continuous_const).continuousAt
  have hsrc : ∀ᶠ u in 𝓝 t, ψ u y ∈ (extChartAt I' c).source :=
    hcont.preimage_mem_nhds ((isOpen_extChartAt_source c).mem_nhds hψt)
  filter_upwards [hsrc, hψ] with u hu hψu
  rw [extChartAt_to_inv, RoughForm.mpullback_eq_compContinuousLinearMap α c hψu hu,
    I.range_eq_univ, fderivWithin_univ]
  -- The two coordinate expressions of `ψᵤ` differ only by unfolding `Function.comp`.
  rfl

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

/-- At any point `x` of `(extChartAt I α).source`, evaluating `φ` on tangent vectors agrees with
evaluating `φ.inChartAt α` on their `mvfderiv` images under `extChartAt I α`. -/
theorem apply_eq_inChartAt_mvfderiv (φ : RoughForm I M F k) {α x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin k → TangentSpace I x) :
    φ x v =
      φ.inChartAt α (extChartAt I α x) (fun i ↦ mvfderiv I (extChartAt I α) x (v i)) := by
  let ω : RoughForm 𝓘(ℝ, E) E F k := fun z ↦
    (φ.inChartAt α z).compContinuousLinearMap
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).toContinuousLinearMap
  have hz : extChartAt I α x ∈ (extChartAt I α).target := (extChartAt I α).map_source hx
  have hsource : (extChartAt I α).symm (extChartAt I α x) ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hz
  have hid : extChartAt I α ∘ (extChartAt I α).symm =ᶠ[𝓝[range I] extChartAt I α x] id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with w hw
    exact (extChartAt I α).right_inv hw
  have hin : (mpullback I 𝓘(ℝ, E) (extChartAt I α) ω).inChartAt α (extChartAt I α x) =
      φ.inChartAt α (extChartAt I α x) := by
    rw [inChartAt_mpullback_modelSpace ω _ α hz (mdifferentiableAt_extChartAt hsource),
      hid.fderivWithin_eq ((extChartAt I α).right_inv hz),
      fderivWithin_id (I.uniqueDiffOn _ (extChartAt_target_subset_range α hz))]
    ext u
    simp only [ω, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
      ContinuousLinearMap.comp_id, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, (extChartAt I α).right_inv hz]
  have hpull : mpullback I 𝓘(ℝ, E) (extChartAt I α) ω x = φ x :=
    (inChartAt_chart_eq_iff hx).1 hin
  rw [← hpull, mpullback_apply]
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans
    (congrArg (φ.inChartAt α (extChartAt I α x)) (funext fun i ↦ ?_))
  rw [Function.comp_apply, ContinuousLinearEquiv.coe_coe, mvfderiv_apply_eq_mfderiv_apply,
    NormedSpace.fromTangentSpace_apply]

end TauCeti.RoughForm

namespace TauCeti.RoughForm

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

/-- The coefficient of a pullback in a preferred chart of the source is the determinant of the
coordinate expression of the map times the coefficient of the form in a preferred chart of the
target. The two model spaces are compared through a continuous linear equivalence `C : E ≃ E'`:
the determinant is that of the coordinate derivative followed by `C⁻¹`, and the target
coefficient is taken in the basis `C ∘ b`. Derivatives are taken within the model range, so
boundary and corner points are included. -/
theorem inChartAt_mpullback_apply_basis_eq_det_mul (φ : RoughForm J N ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (C : E ≃L[ℝ] E') {f : M → N} {β : M} {α : N} {x : M}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt J α).source)
    (hf : MDifferentiableAt I J f x) :
    (mpullback I J f φ).inChartAt β (extChartAt I β x) b =
      ((C.symm : E' →L[ℝ] E) ∘L fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm)
        (range I) (extChartAt I β x)).det *
          φ.inChartAt α (extChartAt J α (f x)) (b.map C.toLinearEquiv) := by
  have hz := (extChartAt I β).map_source hx
  have hfz : MDifferentiableAt I J f ((extChartAt I β).symm (extChartAt I β x)) := by
    rwa [(extChartAt I β).left_inv hx]
  have hgα : f ((extChartAt I β).symm (extChartAt I β x)) ∈ (extChartAt J α).source := by
    simpa only [(extChartAt I β).left_inv hx] using hfx
  rw [inChartAt_mpullback_eq_compContinuousLinearMap φ β α hz hfz hgα,
    ContinuousAlternatingMap.compContinuousLinearMap_apply_basis_map _ _ _ C]
  simp only [(extChartAt I β).left_inv hx]

end TauCeti.RoughForm
