/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Change of variables for top-form integrals

Let `f : M → N` be an open embedding between manifolds modelled on the same finite-dimensional
real vector space, with invertible manifold derivative at every point. Pulling back a top form
supported in the range of `f` preserves integrability, and if `f` preserves the given
orientations then it preserves the integral:
$$\int_M f^*\varphi = \int_N \varphi.$$
An orientation-reversing `f` changes the sign of the integral, and homeomorphisms are the case
`range f = univ`. Manifolds with boundary and corners are allowed: derivatives in charts are taken
within the model range.

The same holds locally. Let `e` be an open partial homeomorphism agreeing with a differentiable
map `f` on its source, and let `φ` be an integrable top form supported in the target of `e`. A
form `ψ` supported in the source that agrees there with `f^*φ` has integral `∫_N φ`
when `f` preserves orientation on the source, and `-∫_N φ` when it reverses it. This is how the
pullback along a map that is only locally a diffeomorphism, such as the sheets of a covering or of
a map over a regular value, is integrated piece by piece.

The proof is chartwise. On a Borel piece `s` of the overlap of a chart at `β` of `M` with the
preimage of a chart at `α` of `N`, the coefficient of `f^*φ` in the chart at `β` is the
determinant of the coordinate expression `T` of `f` times the coefficient of `φ` in the chart at
`α` (`TauCeti.RoughForm.inChartAt_mpullback_apply_basis_eq_det_mul`), and the chart signs of
orientation lifts with a common model orientation compensate the sign of that determinant
(`TauCeti.Manifold.OrientationLift.signAt_mul_signAt_mul_det_pos`). The Jacobian change of
variables for `T` then identifies the integrals over the two coordinate images of the piece. A
finite cover of the support of `φ` by chart pieces in `N`, together with the corresponding pieces
of `M`, assembles these pieces into the integrals over `N` and `M`.

## Main results

* `TauCeti.RoughForm.setLIntegral_ofReal_abs_inChartAt_mpullback`: on a chart piece, the lower
  integral of the absolute coefficient of `f^*φ` is that of `φ` over the image piece.
* `OpenPartialHomeomorph.integrableTopForm_of_eq_mpullback`: such a form is integrable when `φ`
  is.
* `OpenPartialHomeomorph.integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt`,
  `OpenPartialHomeomorph.integralTopForm_of_eq_mpullback_of_isOrientationReversingAt`: change of
  variables along `e`.
* `Topology.IsOpenEmbedding.integrableTopForm_mpullback_iff`: pullback along an open embedding
  with invertible derivative preserves and reflects integrability of top forms supported in its
  range.
* `Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt`: an
  orientation-preserving such embedding preserves the integral of top forms supported in its
  range, and `Topology.IsOpenEmbedding.integralTopForm_mpullback_of_isOrientationReversingAt`:
  an orientation-reversing one negates it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 16.6.

The Jacobian step uses `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` and
`MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

namespace TauCeti

section ChartPiece

variable [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The Jacobian data of the coordinate expression of `f` on the chart image of a Borel piece of
a chart overlap: the image is measurable, the coordinate expression is injective on it and has
its within-range derivative there, and it carries the piece onto the chart image of `f '' s`. -/
private theorem coordinate_jacobian_data {f : M → N} {s : Set M} (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt I J f x) {β : M} {α : N} (hs : IsChartMeasurable I s)
    (hsub : s ⊆ (extChartAt I β).source ∩ f ⁻¹' (extChartAt J α).source) :
    MeasurableSet ((extChartAt I β) '' s) ∧
    (extChartAt J α ∘ f ∘ (extChartAt I β).symm) '' ((extChartAt I β) '' s) =
      (extChartAt J α) '' (f '' s) ∧
    InjOn (extChartAt J α ∘ f ∘ (extChartAt I β).symm) ((extChartAt I β) '' s) ∧
    ∀ z ∈ (extChartAt I β) '' s, HasFDerivWithinAt
      (extChartAt J α ∘ f ∘ (extChartAt I β).symm)
      (fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I) z)
      ((extChartAt I β) '' s) z := by
  refine ⟨hs.image_extChartAt β fun x hx ↦ (hsub hx).1, ?_, ?_, ?_⟩
  · rw [image_image, image_image]
    exact image_congr fun x hx ↦ by
      simp only [Function.comp_apply, (extChartAt I β).left_inv (hsub hx).1]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
    simp only [Function.comp_apply, (extChartAt I β).left_inv (hsub hx).1,
      (extChartAt I β).left_inv (hsub hy).1] at h
    rw [hinj hx hy ((extChartAt J α).injOn (hsub hx).2 (hsub hy).2 h)]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ (chartAt H β).source := by simpa only [extChartAt_source] using (hsub hx).1
    have hfx' : f x ∈ (chartAt H' α).source := by
      simpa only [extChartAt_source, mem_preimage] using (hsub hx).2
    exact ((mdifferentiableAt_iff_of_mem_source hx' hfx').mp (hf x hx)).2.hasFDerivWithinAt.mono
      (image_subset_iff.mpr fun y hy ↦
        extChartAt_target_subset_range β ((extChartAt I β).map_source (hsub hy).1))

/-- On a Borel piece `s` of a chart overlap on which `f` is injective and differentiable, the
unsigned coefficient of `f^*φ` is integrable on the chart image of `s` exactly when the unsigned
coefficient of `φ` is integrable on the chart image of `f '' s`. No orientation is involved. -/
theorem RoughForm.integrableOn_signedInChartAt_one_mpullback_iff (φ : RoughForm J N ℝ k)
    (b : Module.Basis (Fin k) ℝ E) {f : M → N} {s : Set M} (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt I J f x) {β : M} {α : N} (hs : IsChartMeasurable I s)
    (hsub : s ⊆ (extChartAt I β).source ∩ f ⁻¹' (extChartAt J α).source)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    IntegrableOn ((mpullback I J f φ).signedInChartAt b β (fun _ ↦ 1))
        ((extChartAt I β) '' s) μ ↔
      IntegrableOn (φ.signedInChartAt b α (fun _ ↦ 1)) ((extChartAt J α) '' (f '' s)) μ := by
  obtain ⟨hm, himage, hinjT, hD⟩ := coordinate_jacobian_data hinj hf hs hsub
  rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hm hD hinjT]
  have hd : AEStronglyMeasurable (fun z ↦ (fderivWithin ℝ
      (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I) z).toLinearMap.det)
      (μ.restrict ((extChartAt I β) '' s)) :=
    (ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
      (aemeasurable_fderivWithin μ hm hD)).aestronglyMeasurable
  have hc : ∀ z ∈ (extChartAt I β) '' s,
      (mpullback I J f φ).signedInChartAt b β (fun _ ↦ 1) z =
        (fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I) z).toLinearMap.det *
          φ.signedInChartAt b α (fun _ ↦ 1) ((extChartAt J α ∘ f ∘ (extChartAt I β).symm) z) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).1, Function.comp_apply,
      Function.comp_apply, (extChartAt I β).left_inv (hsub hx).1,
      signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).2,
      φ.inChartAt_mpullback_apply_basis_eq_det_mul b (hsub hx).1 (hsub hx).2 (hf x hx)]
    simp only [Units.val_one, Int.cast_one, one_mul]
  rw [integrableOn_congr_fun hc hm]
  simpa only [IntegrableOn, smul_eq_mul] using
    MeasureTheory.integrable_smul_iff_abs_smul (F := ℝ) hd

/-- On a Borel piece `s` of a chart overlap on which `f` is injective and differentiable, the
lower integral of the absolute coefficient of `f^*φ` over the chart image of `s` equals the lower
integral of the absolute coefficient of `φ` over the chart image of `f '' s`. No orientation, and
no measurability or integrability of the coefficients, is needed. -/
theorem RoughForm.setLIntegral_ofReal_abs_inChartAt_mpullback (φ : RoughForm J N ℝ k)
    (b : Module.Basis (Fin k) ℝ E) {f : M → N} {s : Set M} (hinj : InjOn f s)
    (hf : ∀ x ∈ s, MDifferentiableAt I J f x) {β : M} {α : N} (hs : IsChartMeasurable I s)
    (hsub : s ⊆ (extChartAt I β).source ∩ f ⁻¹' (extChartAt J α).source)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∫⁻ z in (extChartAt I β) '' s, ENNReal.ofReal |(mpullback I J f φ).inChartAt β z b| ∂μ =
      ∫⁻ w in (extChartAt J α) '' (f '' s), ENNReal.ofReal |φ.inChartAt α w b| ∂μ := by
  obtain ⟨hm, himage, hinjT, hD⟩ := coordinate_jacobian_data hinj hf hs hsub
  rw [← himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hm hD hinjT]
  refine setLIntegral_congr_fun hm ?_
  rintro _ ⟨x, hx, rfl⟩
  beta_reduce
  rw [φ.inChartAt_mpullback_apply_basis_eq_det_mul b (hsub hx).1 (hsub hx).2 (hf x hx), abs_mul,
    ENNReal.ofReal_mul (abs_nonneg _), Function.comp_apply, Function.comp_apply,
    (extChartAt I β).left_inv (hsub hx).1]

/-- On a Borel piece `s` of a chart overlap on which `f` is injective and orientation
preserving, the signed chart integral of `f^*φ` over the chart image of `s` equals the signed
chart integral of `φ` over the chart image of `f '' s`, for orientation lifts with a common model
orientation. -/
theorem RoughForm.integral_signedInChartAt_mpullback_eq (φ : RoughForm J N ℝ k)
    (b : Module.Basis (Fin k) ℝ E) (l : Manifold.OrientationLift I M (Fin k))
    (l' : Manifold.OrientationLift J N (Fin k)) (hl : l'.modelOrientation = l.modelOrientation)
    {f : M → N} {s : Set M} (hinj : InjOn f s) (hf : ∀ x ∈ s, MDifferentiableAt I J f x)
    (ho : ∀ x ∈ s, Manifold.Orientation.IsOrientationPreservingAt (Manifold.Orientation.mk l)
      (Manifold.Orientation.mk l') f x)
    {β : M} {α : N} (hs : IsChartMeasurable I s)
    (hsub : s ⊆ (extChartAt I β).source ∩ f ⁻¹' (extChartAt J α).source)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∫ z in (extChartAt I β) '' s,
        (mpullback I J f φ).signedInChartAt b β (fun x ↦ l.signAt β x) z ∂μ =
      ∫ w in (extChartAt J α) '' (f '' s),
        φ.signedInChartAt b α (fun y ↦ l'.signAt α y) w ∂μ := by
  obtain ⟨hm, himage, hinjT, hD⟩ := coordinate_jacobian_data hinj hf hs hsub
  rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul μ hm hD hinjT]
  refine setIntegral_congr_fun hm ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ (chartAt H β).source := by simpa only [extChartAt_source] using (hsub hx).1
  have hfx' : f x ∈ (chartAt H' α).source := by
    simpa only [extChartAt_source, mem_preimage] using (hsub hx).2
  have hpos := l.signAt_mul_signAt_mul_det_pos l' hl (hf x hx) (ho x hx) hx' hfx'
  beta_reduce
  rw [signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).1, Function.comp_apply,
    Function.comp_apply, (extChartAt I β).left_inv (hsub hx).1,
    signedInChartAt_apply_of_mem_source _ _ _ _ (hsub hx).2,
    φ.inChartAt_mpullback_apply_basis_eq_det_mul b (hsub hx).1 (hsub hx).2 (hf x hx),
    smul_eq_mul]
  -- The chart signs are `±1`, and `hpos` fixes the sign of the Jacobian against them.
  generalize (fderivWithin ℝ (extChartAt J α ∘ f ∘ (extChartAt I β).symm) (range I)
    (extChartAt I β x)).det = d at hpos ⊢
  have hu (u : ℤˣ) : |((u : ℤ) : ℝ)| = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  have hsq : ((l'.signAt α (f x) : ℤ) : ℝ) * (l'.signAt α (f x) : ℤ) = 1 := by
    exact_mod_cast Int.isUnit_mul_self (l'.signAt α (f x)).isUnit
  have habs : |d| = (l.signAt β x : ℤ) * (l'.signAt α (f x) : ℤ) * d := by
    rw [← abs_of_pos hpos, abs_mul, abs_mul, hu, hu, one_mul, one_mul]
  rw [habs]
  linear_combination (-((l.signAt β x : ℤ) : ℝ) * d * φ.inChartAt α (extChartAt J α (f x)) b) * hsq

end ChartPiece

end TauCeti

namespace OpenPartialHomeomorph

open TauCeti

variable (e : OpenPartialHomeomorph M N) {f : M → N}

/-- Let `e` be an open partial homeomorphism agreeing with a map `f` on its source, where `f` is
differentiable, and let `φ` be an integrable top form supported in the target of `e`. A form `ψ`
supported in the source of `e` that agrees there with `f^*φ` is integrable. -/
theorem integrableTopForm_of_eq_mpullback (hfe : EqOn f e e.source)
    (hf : ∀ x ∈ e.source, MDifferentiableAt I J f x) {φ : RoughForm J N ℝ k}
    {ψ : RoughForm I M ℝ k} (hφ : IntegrableTopForm φ)
    (hφt : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target)
    (hψ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ ⊆ e.source)
    (hψφ : ∀ x ∈ e.source, ψ x = mpullback I J f φ x) : IntegrableTopForm ψ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hψc := e.isCompact_tsupport_of_eq_mpullback hfe hφ.isCompact hφt hψ hψφ
  obtain ⟨-, ⟨b⟩, hi⟩ := (integrableTopForm_iff φ).mp hφ
  -- Over each point `p`, the part of the source of `e` in the chart at `p` whose image lies in
  -- the chart at `e p` is a chart piece on which `ψ` is `f^*φ` and `f` is injective.
  let u : M → Set M := fun p ↦ e.source ∩ e ⁻¹' (chartAt H' (e p)).source ∩ (chartAt H p).source
  have hu (p : M) : IsOpen (u p) :=
    (e.isOpen_inter_preimage (chartAt H' (e p)).open_source).inter (chartAt H p).open_source
  have hsub (p : M) : u p ⊆ (extChartAt I p).source ∩ f ⁻¹' (extChartAt J (e p)).source :=
    fun x hx ↦ ⟨by simpa only [extChartAt_source] using hx.2, by
      simpa only [mem_preimage, extChartAt_source, hfe hx.1.1] using hx.1.2⟩
  refine ψ.integrableTopForm_of_open_cover hψc b (fun p ↦ p) u hu (fun p ↦ inter_subset_right)
    (fun x hx ↦ mem_iUnion.mpr ⟨x, ⟨hψ hx, mem_chart_source H' (e x)⟩, mem_chart_source H x⟩)
    fun p ↦ ?_
  have hm := (hu p).isChartMeasurable.image_extChartAt p fun x hx ↦ (hsub p hx).1
  have hpu : u p ⊆ e.source := fun x hx ↦ hx.1.1
  refine IntegrableOn.congr_fun ?_ (RoughForm.eqOn_signedInChartAt_image
    (fun x hx ↦ (hψφ x (hpu hx)).symm) b p _ fun x hx ↦ (hsub p hx).1) hm
  exact (φ.integrableOn_signedInChartAt_one_mpullback_iff b
    ((e.injOn.mono hpu).congr fun x hx ↦ (hfe (hpu hx)).symm)
    (fun x hx ↦ hf x (hpu hx)) (hu p).isChartMeasurable (hsub p) b.addHaar).mpr
    (hi b (e p)).integrableOn

/-- One piece of the change of variables along `e`: for a subset `t` of the target of `e` inside
a chart of `N`, whose preimage piece `e.source ∩ e ⁻¹' t` is chart measurable inside a chart of
`M`, the signed chart integral of `ψ` over the preimage piece equals that of `φ` over `t`. -/
private theorem integral_signedInChartAt_source_inter_preimage_eq [MeasurableSpace E]
    [BorelSpace E] (hfe : EqOn f e e.source) (hf : ∀ x ∈ e.source, MDifferentiableAt I J f x)
    (b : Module.Basis (Fin k) ℝ E) (l : Manifold.OrientationLift I M (Fin k))
    (l' : Manifold.OrientationLift J N (Fin k)) (hl : l'.modelOrientation = l.modelOrientation)
    (ho : ∀ x ∈ e.source, Manifold.Orientation.IsOrientationPreservingAt
      (Manifold.Orientation.mk l) (Manifold.Orientation.mk l') f x)
    {φ : RoughForm J N ℝ k} {ψ : RoughForm I M ℝ k}
    (hψφ : ∀ x ∈ e.source, ψ x = mpullback I J f φ x) {t : Set N} (ht : t ⊆ e.target) {β : M}
    {α : N} (hs : IsChartMeasurable I (e.source ∩ e ⁻¹' t))
    (hβ : e.source ∩ e ⁻¹' t ⊆ (extChartAt I β).source) (hα : t ⊆ (extChartAt J α).source) :
    ∫ z in (extChartAt I β) '' (e.source ∩ e ⁻¹' t),
        ψ.signedInChartAt b β (fun x ↦ l.signAt β x) z ∂b.addHaar =
      ∫ w in (extChartAt J α) '' t, φ.signedInChartAt b α (fun y ↦ l'.signAt α y) w ∂b.addHaar := by
  have hse : e.source ∩ e ⁻¹' t ⊆ e.source := inter_subset_left
  have hsub : e.source ∩ e ⁻¹' t ⊆ (extChartAt I β).source ∩ f ⁻¹' (extChartAt J α).source :=
    fun x hx ↦ ⟨hβ hx, by simpa only [mem_preimage, hfe hx.1] using hα hx.2⟩
  have himage : f '' (e.source ∩ e ⁻¹' t) = t := by
    rw [(hfe.mono hse).image_eq, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
      inter_eq_right.mpr ht]
  have h := φ.integral_signedInChartAt_mpullback_eq b l l' hl
    ((e.injOn.mono hse).congr fun x hx ↦ (hfe (hse hx)).symm)
    (fun x hx ↦ hf x (hse hx)) (fun x hx ↦ ho x (hse hx)) hs hsub b.addHaar
  rw [himage] at h
  rw [← h]
  exact setIntegral_congr_fun (hs.image_extChartAt _ hβ)
    (RoughForm.eqOn_signedInChartAt_image (fun x hx ↦ hψφ x (hse hx)) b _ _ hβ)

/-- **Change of variables for top forms along an open partial homeomorphism.** Let `e` agree on its
source with a map `f` that is differentiable and orientation preserving there, and let `φ` be an
integrable top form supported in the target of `e`. A form `ψ` supported in the source of `e` that
agrees there with `f^*φ` has the same integral as `φ`: `∫_M ψ = ∫_N φ`. -/
theorem integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt (hfe : EqOn f e e.source)
    (hf : ∀ x ∈ e.source, MDifferentiableAt I J f x) {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation J N (Fin k)}
    (ho : ∀ x ∈ e.source, Manifold.Orientation.IsOrientationPreservingAt o o' f x)
    {φ : RoughForm J N ℝ k} {ψ : RoughForm I M ℝ k} (hφ : IntegrableTopForm φ)
    (hφt : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target)
    (hψ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ ⊆ e.source)
    (hψφ : ∀ x ∈ e.source, ψ x = mpullback I J f φ x) :
    integralTopForm o ψ = integralTopForm o' φ := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hψi := e.integrableTopForm_of_eq_mpullback hfe hf hφ hφt hψ hψφ
  -- Represent both orientations by lifts with the same model orientation.
  obtain ⟨l, rfl⟩ := o.exists_lift
  obtain ⟨l', rfl, hl⟩ := o'.exists_lift_modelOrientation_eq l.modelOrientation
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  -- A finite cover of the support of `φ` by open subsets of the target lying in a chart of `N`
  -- and carried by `e.symm` into a chart of `M`; their preimages under `e` cover the support
  -- of `ψ`.
  let v : N → Set N := fun q ↦
    e.target ∩ e.symm ⁻¹' (chartAt H (e.symm q)).source ∩ (chartAt H' q).source
  have hv (q : N) : IsOpen (v q) :=
    (e.isOpen_inter_preimage_symm (chartAt H _).open_source).inter (chartAt H' q).open_source
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover v hv fun y hy ↦
    mem_iUnion.mpr ⟨y, ⟨hφt hy, mem_chart_source H (e.symm y)⟩, mem_chart_source H' y⟩
  let α : Fin t.card → N := fun i ↦ t.equivFin.symm i
  let w : Fin t.card → Set N := fun i ↦ v (α i)
  have hcover : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ ⋃ i, w i := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp (ht hy)
    exact mem_iUnion.mpr ⟨t.equivFin ⟨q, hq⟩, by simpa only [w, α, Equiv.symm_apply_apply]⟩
  have hw (i : Fin t.card) : w i ⊆ (extChartAt J (α i)).source := fun y hy ↦ by
    simpa only [extChartAt_source] using hy.2
  let u : Fin t.card → Set M := fun i ↦ e.source ∩ e ⁻¹' w i
  have hu (i : Fin t.card) : IsOpen (u i) := e.isOpen_inter_preimage (hv _)
  have hus (i : Fin t.card) : u i ⊆ (extChartAt I (e.symm (α i))).source := fun x hx ↦ by
    have h := hx.2.1.2
    rw [mem_preimage, e.left_inv hx.1] at h
    simpa only [extChartAt_source] using h
  have hψcover : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ ⊆ ⋃ i, u i := fun x hx ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (e.mapsTo_tsupport_of_eq_mpullback hfe hψ hψφ hx))
    exact mem_iUnion.mpr ⟨i, hψ hx, hi⟩
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l ψ hψi b (fun i ↦ e.symm (α i)) u hu
      hus hψcover,
    integralTopForm_eq_sum_disjointed_chart_integrals l' φ hφ b α w (fun i ↦ hv _) hw hcover, hl]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hdisj : disjointed u i = e.source ∩ e ⁻¹' disjointed w i := by
    ext x
    simp only [u, disjointed_eq_inter_compl, mem_inter_iff, mem_preimage, mem_iInter,
      mem_compl_iff]
    exact ⟨fun ⟨⟨hs, hw⟩, h⟩ ↦ ⟨hs, hw, fun j hj hj' ↦ h j hj ⟨hs, hj'⟩⟩,
      fun ⟨hs, hw, h⟩ ↦ ⟨⟨hs, hw⟩, fun j hj hj' ↦ h j hj hj'.2⟩⟩
  have hs : IsChartMeasurable I (disjointed u i) := by
    rw [disjointed_apply, Finset.sup_set_eq_biUnion]
    exact (hu i).isChartMeasurable.diff (isOpen_biUnion fun j _ ↦ hu j).isChartMeasurable
  have hβ : disjointed u i ⊆ (extChartAt I (e.symm (α i))).source :=
    (disjointed_subset u i).trans (hus i)
  rw [hdisj] at hs hβ ⊢
  exact integral_signedInChartAt_source_inter_preimage_eq e hfe hf b l l' hl ho hψφ
    ((disjointed_subset w i).trans fun y hy ↦ hy.1.1) hs hβ ((disjointed_subset w i).trans (hw i))

/-- Change of variables for top forms along an open partial homeomorphism agreeing on its source
with an orientation-reversing map: under the hypotheses of
`integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt` with `f` reversing orientation,
`∫_M ψ = -∫_N φ`. -/
theorem integralTopForm_of_eq_mpullback_of_isOrientationReversingAt (hfe : EqOn f e e.source)
    (hf : ∀ x ∈ e.source, MDifferentiableAt I J f x) {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation J N (Fin k)}
    (ho : ∀ x ∈ e.source, Manifold.Orientation.IsOrientationReversingAt o o' f x)
    {φ : RoughForm J N ℝ k} {ψ : RoughForm I M ℝ k} (hφ : IntegrableTopForm φ)
    (hφt : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target)
    (hψ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ ⊆ e.source)
    (hψφ : ∀ x ∈ e.source, ψ x = mpullback I J f φ x) :
    integralTopForm o ψ = -integralTopForm o' φ := by
  rw [← integralTopForm_neg]
  exact e.integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt hfe hf
    (fun x hx ↦ (Manifold.Orientation.isOrientationPreservingAt_neg_right o o' f x).2 (ho x hx))
    hφ hφt hψ hψφ

end OpenPartialHomeomorph

namespace Topology.IsOpenEmbedding

open TauCeti

/-- Pullback along an open embedding whose manifold derivative is invertible at every point
preserves and reflects integrability of top forms supported in its range. -/
theorem integrableTopForm_mpullback_iff {f : M → N} (hf : IsOpenEmbedding f)
    (hd : ∀ x, (mfderiv I J f x).IsInvertible) {φ : RoughForm J N ℝ k}
    (hφ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ range f) :
    IntegrableTopForm (mpullback I J f φ) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hts := φ.tsupport_mpullback_eq_preimage hf.continuous hf.isOpenMap hd
  -- Over each point `p` of `M`, the overlap of the chart at `p` with the preimage of the chart
  -- at `f p` is a chart piece on which the two coefficients have the same integrability.
  let u : M → Set M := fun p ↦ (chartAt H p).source ∩ f ⁻¹' (chartAt H' (f p)).source
  have hu (p : M) : IsOpen (u p) :=
    (chartAt H p).open_source.inter ((chartAt H' (f p)).open_source.preimage hf.continuous)
  have hsub (p : M) : u p ⊆ (extChartAt I p).source ∩ f ⁻¹' (extChartAt J (f p)).source := by
    simp only [u, extChartAt_source, Subset.rfl]
  have hpiece (b : Module.Basis (Fin k) ℝ E) (p : M) :=
    φ.integrableOn_signedInChartAt_one_mpullback_iff b hf.injective.injOn
      (fun x _ ↦ mdifferentiableAt_of_isInvertible_mfderiv (hd x)) (hu p).isChartMeasurable
      (hsub p) b.addHaar
  constructor
  · intro h
    obtain ⟨hc, ⟨b⟩, hi⟩ := (integrableTopForm_iff _).mp h
    rw [hts] at hc
    refine φ.integrableTopForm_of_open_cover ?_ b (fun p ↦ f p) (fun p ↦ f '' u p)
      (fun p ↦ hf.isOpenMap _ (hu p)) (fun p ↦ image_subset_iff.mpr inter_subset_right) ?_
      fun p ↦ (hpiece b p).mp (hi b p).integrableOn
    · simpa only [image_preimage_eq_of_subset hφ] using hc.image hf.continuous
    · intro y hy
      obtain ⟨x, rfl⟩ := hφ hy
      exact mem_iUnion.mpr ⟨x, mem_image_of_mem f ⟨mem_chart_source H x, mem_chart_source H' (f x)⟩⟩
  · intro h
    obtain ⟨hc, ⟨b⟩, hi⟩ := (integrableTopForm_iff _).mp h
    refine (mpullback I J f φ).integrableTopForm_of_open_cover ?_ b id u hu
      (fun p ↦ inter_subset_left) (fun x _ ↦ mem_iUnion.mpr
        ⟨x, mem_chart_source H x, mem_chart_source H' (f x)⟩)
      fun p ↦ (hpiece b p).mpr (hi b (f p)).integrableOn
    rw [hts]
    exact hf.isInducing.isCompact_preimage' hc hφ

/-- **Change of variables for top forms along an open embedding.** Pullback along an
orientation-preserving open embedding preserves the integral of every top form supported in its
range: `∫_M f^*φ = ∫_N φ`. Both sides vanish together when `φ` is not integrable. -/
theorem integralTopForm_mpullback_of_isOrientationPreservingAt {f : M → N}
    (hf : IsOpenEmbedding f) {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation J N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o o' f x) {φ : RoughForm J N ℝ k}
    (hφ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ range f) :
    integralTopForm o (mpullback I J f φ) = integralTopForm o' φ := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hd (x : M) := (ho x).isInvertible_mfderiv
  have hmd (x : M) := mdifferentiableAt_of_isInvertible_mfderiv (hd x)
  have hint := hf.integrableTopForm_mpullback_iff hd hφ
  by_cases hφi : IntegrableTopForm φ
  swap
  · rw [integralTopForm_eq_zero_of_not_integrable _ _ hφi,
      integralTopForm_eq_zero_of_not_integrable _ _ (mt hint.mp hφi)]
  -- Represent both orientations by lifts with the same model orientation.
  obtain ⟨l, rfl⟩ := o.exists_lift
  obtain ⟨l', rfl, hl⟩ := o'.exists_lift_modelOrientation_eq l.modelOrientation
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  -- A finite cover of the support of `φ` by images of overlaps of charts of `M` with preimages
  -- of charts of `N`; its preimage under `f` covers the support of the pullback.
  let v : M → Set N := fun p ↦ f '' ((chartAt H p).source ∩ f ⁻¹' (chartAt H' (f p)).source)
  have hv (p : M) : IsOpen (v p) := hf.isOpenMap _
    ((chartAt H p).open_source.inter ((chartAt H' (f p)).open_source.preimage hf.continuous))
  obtain ⟨t, ht⟩ := hφi.isCompact.elim_finite_subcover v hv fun y hy ↦ by
    obtain ⟨x, rfl⟩ := hφ hy
    exact mem_iUnion.mpr ⟨x, mem_image_of_mem f ⟨mem_chart_source H x, mem_chart_source H' (f x)⟩⟩
  let α : Fin t.card → M := fun i ↦ t.equivFin.symm i
  let w : Fin t.card → Set N := fun i ↦ v (α i)
  have hcover : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ ⋃ i, w i := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp (ht hy)
    exact mem_iUnion.mpr ⟨t.equivFin ⟨q, hq⟩, by simpa only [w, α, Equiv.symm_apply_apply]⟩
  have hw (i : Fin t.card) : w i ⊆ (extChartAt J (f (α i))).source := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [extChartAt_source, mem_preimage] using hx.2
  have hu (i : Fin t.card) : f ⁻¹' w i ⊆ (extChartAt I (α i)).source := fun x hx ↦ by
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← hf.injective hyx]
    simpa only [extChartAt_source] using hy.1
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l _ (hint.mpr hφi) b α
      (fun i ↦ f ⁻¹' w i) (fun i ↦ (hv _).preimage hf.continuous) hu
      ((RoughForm.tsupport_mpullback_subset_preimage hf.continuous φ).trans
        (by simpa only [preimage_iUnion] using preimage_mono hcover)),
    integralTopForm_eq_sum_disjointed_chart_integrals l' φ hφi b (fun i ↦ f (α i)) w
      (fun i ↦ hv _) hw hcover, hl]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hdisj : disjointed (fun j ↦ f ⁻¹' w j) i = f ⁻¹' disjointed w i := by
    simp only [disjointed_eq_inter_compl, preimage_inter, preimage_iInter, preimage_compl]
  have hs : IsChartMeasurable I (f ⁻¹' disjointed w i) := by
    rw [disjointed_apply, preimage_sdiff, Finset.sup_set_eq_biUnion, preimage_iUnion₂]
    exact ((hv _).preimage hf.continuous).isChartMeasurable.diff
      (isOpen_biUnion fun j _ ↦ (hv _).preimage hf.continuous).isChartMeasurable
  have h := φ.integral_signedInChartAt_mpullback_eq b l l' hl hf.injective.injOn
    (fun x _ ↦ hmd x) (fun x _ ↦ ho x) hs
    (fun x hx ↦ ⟨hu i (preimage_mono (disjointed_subset w i) hx),
      hw i (disjointed_subset w i hx)⟩) b.addHaar
  rwa [image_preimage_eq_of_subset ((disjointed_subset w i).trans
    (image_subset_range _ _)), ← hdisj] at h

/-- Pullback along an orientation-reversing open embedding negates the integral of every top form
supported in its range: `∫_M f^*φ = -∫_N φ`. -/
theorem integralTopForm_mpullback_of_isOrientationReversingAt {f : M → N}
    (hf : IsOpenEmbedding f) {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation J N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt o o' f x) {φ : RoughForm J N ℝ k}
    (hφ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ range f) :
    integralTopForm o (mpullback I J f φ) = -integralTopForm o' φ := by
  rw [← integralTopForm_neg]
  refine hf.integralTopForm_mpullback_of_isOrientationPreservingAt (fun x ↦ ?_) hφ
  exact (Manifold.Orientation.isOrientationPreservingAt_neg_right o o' f x).2 (ho x)

end Topology.IsOpenEmbedding
