/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The degree formula for integrals

Let `E` be a finite-dimensional real inner product space and `f : E → E` a proper `C¹` map. For
every continuous compactly supported `g : E → F` with values in a real normed space,

`∫ det Df(x) • g (f x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the homological degree of `f` for any orientation of `E`, used on both source
and target (`TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_smul_integral`).
For a two-form `β = b dy₁ ∧ dy₂` on the plane the pullback is `f^* β = (b ∘ f) det Df dx₁ ∧ dx₂`, so
this is the classical formula `∫ f^* β = deg f ∫ β` for compactly supported top-degree forms, here
proved with the degree defined by local homology rather than by counting preimages of regular
values or by de Rham cohomology.

The proof has two halves. The first is a signed area formula with multiplicity, valid for any
differentiable map with almost every fibre finite
(`TauCeti.integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul`):

`∫ det Df(x) • g (f x) dx = ∫ (N⁺(y) - N⁻(y)) • g(y) dy`,

where `N^±(y)` is the number of preimages of `y` at which `det Df` is positive, respectively
negative. It splits the regular set into the open sets where the Jacobian is positive and negative,
where the area formula with multiplicity
(`TauCeti.lintegral_normDet_fderiv_mul_eq_lintegral_tsum_of_injective_fderiv`) identifies the
pushforward of `|det Df| dx` with the counting density `N^±(y) dy`
(`TauCeti.map_withDensity_abs_det_fderiv_eq_withDensity_encard`). The second half is that
`N⁺(y) - N⁻(y) = deg f` at every regular value `y`
(`TauCeti.HomologicalOrientation.degree_eq_ncard_sub_ncard`), and that almost every point is a
regular value by Sard's theorem (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).

## Main results

* `TauCeti.map_withDensity_abs_det_fderiv_eq_withDensity_encard`: on a set of regular points,
  `f` pushes `|det Df| dx` forward to the fibre-counting density.
* `TauCeti.setIntegral_abs_det_fderiv_smul_comp_eq_integral_ncard_smul`,
  `TauCeti.integrable_ncard_smul_of_integrableOn_abs_det_fderiv_smul`: the corresponding area
  formula and integrability transfer for Bochner integrals.
* `TauCeti.integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul`: the signed area
  formula.
* `TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_smul_integral`: the
  degree formula.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
-/

public section

noncomputable section

open Set Function MeasureTheory Measure Module
open scoped ENNReal

namespace TauCeti

section AreaFormula

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → E}
  {s : Set E}

private theorem measurable_ofReal_abs_det_fderiv :
    Measurable fun x ↦ ENNReal.ofReal |(fderiv ℝ f x).det| :=
  ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)))

private theorem measurable_encard_inter_preimage_singleton (hs : MeasurableSet s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (hdet : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) :
    Measurable fun y ↦ ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) := by
  simpa only [ENNReal.tsum_set_one] using measurable_tsum_fiber_of_injective_fderiv hs hd
    (fun x hx ↦ ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hdet x hx)).injective)
    (g := fun _ ↦ (1 : ℝ≥0∞)) measurable_const

/-- **The pushforward of the Jacobian measure counts preimages.** On a measurable set `s` of
points where `f` is differentiable with invertible derivative, `f` pushes the measure
`|det Df(x)| dx` on `s` forward to the measure with density `y ↦ #(s ∩ f⁻¹(y))`, an extended
natural number. This is the non-injective form of
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar`. -/
theorem map_withDensity_abs_det_fderiv_eq_withDensity_encard (hs : MeasurableSet s)
    (hf : Measurable f) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hdet : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) :
    ((volume.restrict s).withDensity fun x ↦ ENNReal.ofReal |(fderiv ℝ f x).det|).map f =
      volume.withDensity fun y ↦ ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) := by
  ext B hB
  have h := lintegral_normDet_fderiv_mul_eq_lintegral_tsum_of_injective_fderiv hs hd
    (fun x hx ↦ ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hdet x hx)).injective)
    ((measurable_one.indicator hB).comp hf)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  rw [map_apply hf hB, withDensity_apply _ (hf hB), withDensity_apply _ hB,
    ← lintegral_indicator (hf hB), ← lintegral_indicator hB]
  calc
    _ = ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * (B.indicator 1 ∘ f) x := by
      refine lintegral_congr fun x ↦ ?_
      by_cases hx : f x ∈ B <;>
        simp [hx, LinearMap.normDet_eq_abs_det, indicator_of_mem, indicator_of_notMem]
    _ = _ := h
    _ = _ := by
      refine lintegral_congr fun y ↦ ?_
      have e : ∀ x : ↥(s ∩ f ⁻¹' {y}), (B.indicator (1 : E → ℝ≥0∞) ∘ f) x = B.indicator 1 y :=
        fun x ↦ by rw [comp_apply, x.2.2]
      simp_rw [e, ENNReal.tsum_set_const]
      by_cases hy : y ∈ B <;> simp [hy]

/-- **The area formula with multiplicity on a set of regular points.** If `f` is differentiable
with invertible derivative on a measurable set `s`, and almost every fibre of `f` meets `s` in a
finite set, then `∫_s |det Df(x)| • g (f x) dx = ∫ #(s ∩ f⁻¹(y)) • g(y) dy`. -/
theorem setIntegral_abs_det_fderiv_smul_comp_eq_integral_ncard_smul (hs : MeasurableSet s)
    (hf : Measurable f) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hdet : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) (hfin : ∀ᵐ y, (s ∩ f ⁻¹' {y}).Finite)
    {g : E → F} (hg : StronglyMeasurable g) :
    ∫ x in s, |(fderiv ℝ f x).det| • g (f x) = ∫ y, ((s ∩ f ⁻¹' {y}).ncard : ℝ) • g y := by
  calc
    _ = ∫ x, g (f x) ∂(volume.restrict s).withDensity
          fun x ↦ ENNReal.ofReal |(fderiv ℝ f x).det| := by
      rw [integral_withDensity_eq_integral_toReal_smul measurable_ofReal_abs_det_fderiv
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
    _ = ∫ y, g y ∂volume.withDensity fun y ↦ ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) := by
      rw [← map_withDensity_abs_det_fderiv_eq_withDensity_encard hs hf hd hdet,
        integral_map hf.aemeasurable hg.aestronglyMeasurable]
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul
        (measurable_encard_inter_preimage_singleton hs hd hdet)
        (hfin.mono fun y hy ↦ by simpa using hy.encard_lt_top)]
      refine integral_congr_ae (hfin.mono fun y hy ↦ ?_)
      simp [← hy.cast_ncard_eq]

/-- Under the hypotheses of `TauCeti.setIntegral_abs_det_fderiv_smul_comp_eq_integral_ncard_smul`,
if `|det Df(x)| • g (f x)` is integrable on `s`, then `y ↦ #(s ∩ f⁻¹(y)) • g(y)` is integrable. -/
theorem integrable_ncard_smul_of_integrableOn_abs_det_fderiv_smul (hs : MeasurableSet s)
    (hf : Measurable f) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hdet : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) (hfin : ∀ᵐ y, (s ∩ f ⁻¹' {y}).Finite)
    {g : E → F} (hg : StronglyMeasurable g)
    (hint : IntegrableOn (fun x ↦ |(fderiv ℝ f x).det| • g (f x)) s) :
    Integrable fun y ↦ ((s ∩ f ⁻¹' {y}).ncard : ℝ) • g y := by
  have hlt : ∀ᵐ y, ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞) < ∞ :=
    hfin.mono fun y hy ↦ by simpa using hy.encard_lt_top
  have h : Integrable g (volume.withDensity fun y ↦ ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞)) := by
    rw [← map_withDensity_abs_det_fderiv_eq_withDensity_encard hs hf hd hdet,
      integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable,
      integrable_withDensity_iff_integrable_smul' measurable_ofReal_abs_det_fderiv
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (abs_nonneg _), comp_apply]
    exact hint
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_encard_inter_preimage_singleton hs hd hdet) hlt] at h
  refine h.congr (hfin.mono fun y hy ↦ ?_)
  simp [← hy.cast_ncard_eq]

/-- **The signed area formula.** Let `f : E → E` be differentiable with almost every fibre finite,
and let `det Df(x) • g (f x)` be integrable. Then its integral is the integral of `g` weighted by
the number of preimages at which `det Df` is positive minus the number at which it is negative.
Points with `det Df(x) = 0` contribute to neither side. -/
theorem integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul (hf : Differentiable ℝ f)
    (hfin : ∀ᵐ y, (f ⁻¹' {y}).Finite) {g : E → F} (hg : StronglyMeasurable g)
    (hint : Integrable fun x ↦ (fderiv ℝ f x).det • g (f x)) :
    ∫ x, (fderiv ℝ f x).det • g (f x) =
      ∫ y, ((({x | 0 < (fderiv ℝ f x).det} ∩ f ⁻¹' {y}).ncard : ℝ) -
        ({x | (fderiv ℝ f x).det < 0} ∩ f ⁻¹' {y}).ncard) • g y := by
  have hJ : Measurable fun x ↦ (fderiv ℝ f x).det :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ f)
  have hP : MeasurableSet {x | 0 < (fderiv ℝ f x).det} := measurableSet_lt measurable_const hJ
  have hN : MeasurableSet {x | (fderiv ℝ f x).det < 0} := measurableSet_lt hJ measurable_const
  have hfm : Measurable f := hf.continuous.measurable
  have hfinP : ∀ᵐ y, ({x | 0 < (fderiv ℝ f x).det} ∩ f ⁻¹' {y}).Finite :=
    hfin.mono fun y hy ↦ hy.subset inter_subset_right
  have hfinN : ∀ᵐ y, ({x | (fderiv ℝ f x).det < 0} ∩ f ⁻¹' {y}).Finite :=
    hfin.mono fun y hy ↦ hy.subset inter_subset_right
  -- On the positive and negative parts, the integrand is `±|det Df| • g ∘ f`.
  have hintP : IntegrableOn (fun x ↦ |(fderiv ℝ f x).det| • g (f x))
      {x | 0 < (fderiv ℝ f x).det} :=
    hint.integrableOn.congr_fun (fun x hx ↦ by simp [abs_of_pos hx.out]) hP
  have hintN : IntegrableOn (fun x ↦ |(fderiv ℝ f x).det| • g (f x))
      {x | (fderiv ℝ f x).det < 0} :=
    hint.integrableOn.neg.congr_fun (fun x hx ↦ by simp [abs_of_neg hx.out]) hN
  calc
    _ = ∫ x in {x | 0 < (fderiv ℝ f x).det} ∪ {x | (fderiv ℝ f x).det < 0},
          (fderiv ℝ f x).det • g (f x) := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hx
      simp [le_antisymm hx.1 hx.2]
    _ = (∫ x in {x | 0 < (fderiv ℝ f x).det}, |(fderiv ℝ f x).det| • g (f x)) -
          ∫ x in {x | (fderiv ℝ f x).det < 0}, |(fderiv ℝ f x).det| • g (f x) := by
      rw [setIntegral_union (disjoint_left.2 fun x hxP hxN ↦ lt_asymm hxP.out hxN.out) hN
        hint.integrableOn hint.integrableOn, sub_eq_add_neg, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun hP fun x hx ↦ by simp [abs_of_pos hx.out]
      · exact setIntegral_congr_fun hN fun x hx ↦ by simp [abs_of_neg hx.out]
    _ = (∫ y, (({x | 0 < (fderiv ℝ f x).det} ∩ f ⁻¹' {y}).ncard : ℝ) • g y) -
          ∫ y, (({x | (fderiv ℝ f x).det < 0} ∩ f ⁻¹' {y}).ncard : ℝ) • g y := by
      rw [setIntegral_abs_det_fderiv_smul_comp_eq_integral_ncard_smul hP hfm (fun x _ ↦ hf x)
          (fun x hx ↦ ne_of_gt hx.out) hfinP hg,
        setIntegral_abs_det_fderiv_smul_comp_eq_integral_ncard_smul hN hfm (fun x _ ↦ hf x)
          (fun x hx ↦ ne_of_lt hx.out) hfinN hg]
    _ = _ := by
      simp_rw [sub_smul]
      exact (integral_sub
        (integrable_ncard_smul_of_integrableOn_abs_det_fderiv_smul hP hfm (fun x _ ↦ hf x)
          (fun x hx ↦ ne_of_gt hx.out) hfinP hg hintP)
        (integrable_ncard_smul_of_integrableOn_abs_det_fderiv_smul hN hfm (fun x _ ↦ hf x)
          (fun x hx ↦ ne_of_lt hx.out) hfinN hg hintN)).symm

end AreaFormula

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **The degree formula for integrals.** Let `o` be an orientation of the finite-dimensional real
inner product space `E`, and let `f : E → E` be a proper `C¹` map. For every continuous compactly
supported `g : E → F`,

`∫ det Df(x) • g (f x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the degree of `f` for the orientation `o` on both source and target. -/
theorem integral_det_fderiv_smul_comp_eq_degree_smul_integral (o : HomologicalOrientation E E n)
    (hE : finrank ℝ E = n) {f : C(E, E)} (hf : ContDiff ℝ 1 f) (hp : IsProperMap f) {g : E → F}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ x, (fderiv ℝ f x).det • g (f x) = o.degree o hE f • ∫ y, g y := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  -- The integrand is continuous with compact support, since `f` is proper.
  have hgf : HasCompactSupport (g ∘ f) :=
    IsCompact.of_isClosed_subset (hp.isCompact_preimage hgc) (isClosed_tsupport _)
      (closure_minimal (by rw [support_comp_eq_preimage]; exact preimage_mono (subset_tsupport g))
        ((isClosed_tsupport g).preimage f.continuous))
  have hint : Integrable fun x ↦ (fderiv ℝ f x).det • g (f x) :=
    ((ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv one_ne_zero)).smul
      (hg.comp f.continuous)).integrable_of_hasCompactSupport hgf.smul_left
  -- By Sard's theorem almost every point is a regular value.
  have hsard : ∀ᵐ y, ∀ x ∈ f ⁻¹' {y}, (fderiv ℝ f x).det ≠ 0 := by
    have h0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) (f := f)
      (s := {x | (fderiv ℝ f x).det = 0}) (fun x _ ↦ (hd x).hasFDerivAt.hasFDerivWithinAt)
      fun x hx ↦ hx
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy x hx hJx
    exact hy ⟨x, hJx, hx⟩
  -- The fibre over a regular value is finite, and its signed count is the degree.
  have hfin : ∀ᵐ y, (f ⁻¹' {y}).Finite := hsard.mono fun y hy ↦
    (hp.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt
      (fun x _ ↦ (hd x).hasFDerivAt) fun x hx ↦
        ⟨_, ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hy x hx)).antilipschitzWith⟩
  rw [integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul hd hfin
      hg.stronglyMeasurable hint, ← Int.cast_smul_eq_zsmul ℝ, ← integral_smul]
  refine integral_congr_ae (hsard.mono fun y hy ↦ ?_)
  simp [o.degree_eq_ncard_sub_ncard hE hp (fun x _ ↦ (hd x).hasFDerivAt) hy]

end HomologicalOrientation

end TauCeti
