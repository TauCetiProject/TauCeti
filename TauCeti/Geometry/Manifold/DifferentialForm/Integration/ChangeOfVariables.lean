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

Let `f : M ≃ₜ N` be a homeomorphism between manifolds modelled on the same finite-dimensional
real vector space, differentiable with invertible manifold derivative at every point. Pulling a
top form back along `f` preserves integrability, and if `f` preserves the given orientations then
it preserves the integral:
$$\int_M f^*\varphi = \int_N \varphi,$$
while an orientation-reversing `f` changes its sign. Manifolds with boundary and corners are
allowed: derivatives in charts are taken within the model range.

The proof is chartwise. On a Borel piece `s` of the overlap of a chart at `β` of `M` with the
preimage of a chart at `α` of `N`, the coefficient of `f^*φ` in the chart at `β` is the
determinant of the coordinate expression `T` of `f` times the coefficient of `φ` in the chart at
`α` (`TauCeti.RoughForm.inChartAt_mpullback_apply_basis_eq_det_mul`), and the chart signs of
orientation lifts with a common model orientation compensate the sign of that determinant
(`TauCeti.Manifold.OrientationLift.signAt_mul_signAt_mul_det_pos`). The Jacobian change of
variables for `T` then identifies the integrals over the two coordinate images of the piece. A
finite chart cover of the support of `φ` and its preimage under `f` assembles these pieces into
the integrals over `N` and `M`.

## Main results

* `Homeomorph.integrableTopForm_mpullback_iff`: pullback along a homeomorphism with invertible
  derivative preserves and reflects integrability of top forms.
* `Homeomorph.integralTopForm_mpullback_of_isOrientationPreservingAt`: an orientation-preserving
  such homeomorphism preserves the integral.
* `Homeomorph.integralTopForm_mpullback_of_isOrientationReversingAt`: an orientation-reversing one
  negates it.

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

namespace Homeomorph

open TauCeti

/-- Pullback along a homeomorphism that is differentiable with invertible manifold derivative
at every point preserves and reflects integrability of top forms. -/
theorem integrableTopForm_mpullback_iff (f : M ≃ₜ N) (hf : MDifferentiable I J f)
    (hd : ∀ x, (mfderiv I J f x).IsInvertible) (φ : RoughForm J N ℝ k) :
    IntegrableTopForm (mpullback I J f φ) ↔ IntegrableTopForm φ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  -- Over each point `p` of `M`, the overlap of the chart at `p` with the preimage of the chart
  -- at `f p` is a chart piece on which the two coefficients have the same integrability.
  let u : M → Set M := fun p ↦ (chartAt H p).source ∩ f ⁻¹' (chartAt H' (f p)).source
  have hu (p : M) : IsOpen (u p) :=
    (chartAt H p).open_source.inter ((chartAt H' (f p)).open_source.preimage f.continuous)
  have hsub (p : M) : u p ⊆ (extChartAt I p).source ∩ f ⁻¹' (extChartAt J (f p)).source := by
    simp only [u, extChartAt_source, Subset.rfl]
  have hpiece (b : Module.Basis (Fin k) ℝ E) (p : M) :=
    φ.integrableOn_signedInChartAt_one_mpullback_iff b f.injective.injOn (fun x _ ↦ hf x)
      (hu p).isChartMeasurable (hsub p) b.addHaar
  constructor
  · intro h
    obtain ⟨hc, ⟨b⟩, hi⟩ := (integrableTopForm_iff _).mp h
    rw [φ.tsupport_mpullback_eq_preimage f hd, f.isCompact_preimage] at hc
    refine φ.integrableTopForm_of_open_cover hc b (fun p ↦ f p) (fun p ↦ f '' u p)
      (fun p ↦ f.isOpenMap _ (hu p))
      (fun p ↦ image_subset_iff.mpr inter_subset_right) (fun y _ ↦ mem_iUnion.mpr
        ⟨f.symm y, f.symm y, ⟨mem_chart_source H _, by
          simp only [mem_preimage, f.apply_symm_apply, mem_chart_source]⟩,
          f.apply_symm_apply y⟩) fun p ↦ (hpiece b p).mp (hi b p).integrableOn
  · intro h
    obtain ⟨hc, ⟨b⟩, hi⟩ := (integrableTopForm_iff _).mp h
    refine (mpullback I J f φ).integrableTopForm_of_open_cover
      ((f.isCompact_preimage.mpr hc).of_isClosed_subset
        (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) _)
        (RoughForm.tsupport_mpullback_subset_preimage f.continuous φ))
      b id u hu (fun p ↦ inter_subset_left) (fun x _ ↦ mem_iUnion.mpr
        ⟨x, mem_chart_source H x, mem_chart_source H' (f x)⟩)
      fun p ↦ (hpiece b p).mpr (hi b (f p)).integrableOn

/-- **Change of variables for top forms.** Pullback along an orientation-preserving
homeomorphism that is differentiable at every point preserves the integral of every top form:
`∫_M f^*φ = ∫_N φ`. Both sides vanish together when `φ` is not integrable. -/
theorem integralTopForm_mpullback_of_isOrientationPreservingAt (f : M ≃ₜ N)
    (hf : MDifferentiable I J f) {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation J N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o o' f x)
    (φ : RoughForm J N ℝ k) : integralTopForm o (mpullback I J f φ) = integralTopForm o' φ := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hint := f.integrableTopForm_mpullback_iff hf (fun x ↦ (ho x).isInvertible_mfderiv) φ
  by_cases hφ : IntegrableTopForm φ
  swap
  · rw [integralTopForm_eq_zero_of_not_integrable _ _ hφ,
      integralTopForm_eq_zero_of_not_integrable _ _ (mt hint.mp hφ)]
  -- Represent both orientations by lifts with the same model orientation.
  obtain ⟨l, rfl⟩ := o.exists_lift
  obtain ⟨l', rfl, hl⟩ : ∃ l' : Manifold.OrientationLift J N (Fin k),
      Manifold.Orientation.mk l' = o' ∧ l'.modelOrientation = l.modelOrientation := by
    obtain ⟨l₀, rfl⟩ := o'.exists_lift
    rcases _root_.Orientation.eq_or_eq_neg l₀.modelOrientation l.modelOrientation l.card_eq
      with h | h
    · exact ⟨l₀, rfl, h⟩
    · exact ⟨l₀.flip, (Manifold.Orientation.mk_eq_mk_iff _ _).mpr (.inr rfl), by
        rw [Manifold.OrientationLift.flip_modelOrientation, h]
        exact _root_.neg_neg l.modelOrientation⟩
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  -- A finite cover of the support of `φ` by overlaps of charts of `N` with images of charts of
  -- `M`; its preimage under `f` covers the support of the pullback.
  let v : N → Set N := fun q ↦ (chartAt H' q).source ∩ f.symm ⁻¹' (chartAt H (f.symm q)).source
  have hv (q : N) : IsOpen (v q) :=
    (chartAt H' q).open_source.inter ((chartAt H (f.symm q)).open_source.preimage
      f.symm.continuous)
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover v hv fun y _ ↦
    mem_iUnion.mpr ⟨y, mem_chart_source H' y, mem_chart_source H (f.symm y)⟩
  let α : Fin t.card → N := fun i ↦ t.equivFin.symm i
  let w : Fin t.card → Set N := fun i ↦ v (α i)
  have hcover : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ ⋃ i, w i := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp (ht hy)
    exact mem_iUnion.mpr ⟨t.equivFin ⟨q, hq⟩, by simpa only [w, α, Equiv.symm_apply_apply]⟩
  have hw (i : Fin t.card) : w i ⊆ (extChartAt J (α i)).source := fun y hy ↦ by
    simpa only [extChartAt_source] using hy.1
  have hu (i : Fin t.card) : f ⁻¹' w i ⊆ (extChartAt I (f.symm (α i))).source := fun x hx ↦ by
    simpa only [extChartAt_source, w, v, mem_preimage, f.symm_apply_apply] using hx.2
  rw [integralTopForm_eq_sum_disjointed_chart_integrals l _ (hint.mpr hφ) b
      (fun i ↦ f.symm (α i)) (fun i ↦ f ⁻¹' w i) (fun i ↦ (hv _).preimage f.continuous) hu
      ((RoughForm.tsupport_mpullback_subset_preimage f.continuous φ).trans
        (by simpa only [preimage_iUnion] using preimage_mono hcover)),
    integralTopForm_eq_sum_disjointed_chart_integrals l' φ hφ b α w (fun i ↦ hv _) hw hcover, hl]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hdisj : disjointed (fun j ↦ f ⁻¹' w j) i = f ⁻¹' disjointed w i := by
    simp only [disjointed_eq_inter_compl, preimage_inter, preimage_iInter, preimage_compl]
  have hs : IsChartMeasurable I (f ⁻¹' disjointed w i) := by
    rw [disjointed_apply, preimage_sdiff, Finset.sup_set_eq_biUnion, preimage_iUnion₂]
    exact ((hv _).preimage f.continuous).isChartMeasurable.diff
      (isOpen_biUnion fun j _ ↦ (hv _).preimage f.continuous).isChartMeasurable
  have h := φ.integral_signedInChartAt_mpullback_eq b l l' hl f.injective.injOn
    (fun x _ ↦ hf x) (fun x _ ↦ ho x) hs
    (fun x hx ↦ ⟨hu i (preimage_mono (disjointed_subset w i) hx),
      hw i (disjointed_subset w i hx)⟩) b.addHaar
  rwa [f.image_preimage, ← hdisj] at h

/-- Pullback along an orientation-reversing homeomorphism that is differentiable at every point
negates the integral of every top form: `∫_M f^*φ = -∫_N φ`. -/
theorem integralTopForm_mpullback_of_isOrientationReversingAt (f : M ≃ₜ N)
    (hf : MDifferentiable I J f) {o : Manifold.Orientation I M (Fin k)}
    {o' : Manifold.Orientation J N (Fin k)}
    (ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt o o' f x)
    (φ : RoughForm J N ℝ k) : integralTopForm o (mpullback I J f φ) = -integralTopForm o' φ := by
  rw [← integralTopForm_neg]
  refine f.integralTopForm_mpullback_of_isOrientationPreservingAt hf (fun x ↦ ?_) φ
  exact (Manifold.Orientation.isOrientationPreservingAt_neg_right o o' f x).2 (ho x)

end Homeomorph
