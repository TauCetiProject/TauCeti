/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Function.Coarea.Integral
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Weighted, pushforward, and Bochner coarea formulas for Lipschitz maps

Let `E` and `F` be finite-dimensional real inner product spaces of dimensions `n` and `m`, let
`f : E → F`, and let `J f x = (fderiv ℝ f x)†.normDet` denote the coarea Jacobian of `f` at `x`.
Building on the unweighted Lipschitz coarea formula in
`TauCeti.MeasureTheory.Function.Coarea.Lipschitz` and the regular-locus weighted `ℝ≥0∞` coarea
identity in `TauCeti.MeasureTheory.Function.Coarea.Integral`, this file proves the full weighted
`ℝ≥0∞`, measure-pushforward, and Banach-space Bochner coarea formulas:

1. **Regular-locus Bochner coarea (`MeasureTheory`).** If `f` is differentiable with surjective
   derivative at every point of a Lebesgue-measurable set `s` and `x ↦ J f x • g x` is Bochner
   integrable on `s` with values in a real normed space `V`, then `g` is integrable on
   `μHE[n - m]`-almost every fiber `s ∩ f ⁻¹' {y}`, the fiber integral
   `y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[n - m]` is Bochner integrable on `F`, and
   `∫ x in s, J f x • g x = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[n - m]`. Neither completeness
   of `V` nor a separate measurability assumption on `g` is required: on `s`, `J f` is everywhere
   nonzero, so strong measurability of `J f • g` recovers that of `g`.
2. **Weighted `ℝ≥0∞`, Radon-Nikodym pushforward, and Bochner coarea for locally Lipschitz maps on
   open sets (`LocallyLipschitzOn`).** When `f` is locally Lipschitz on an open set `U ⊇ s` with
   `s` Lebesgue measurable, Rademacher's theorem and the coarea Sard lemma eliminate the critical
   and nondifferentiable locus `s \ G` on both sides: on `s \ G` the Jacobian `J f` vanishes
   almost everywhere, while on almost every fiber `s ∩ f ⁻¹' {y}` the restricted Hausdorff measure
   agrees with its restriction to `(s ∩ G) ∩ f ⁻¹' {y}`. Consequently:
   * the weighted `ℝ≥0∞` coarea identity holds whenever `x ↦ ENNReal.ofReal (J f x) * w x` is
     `volume.restrict s`-almost everywhere measurable (in particular whenever `w` is);
   * pushing forward `(volume.restrict s).withDensity (ENNReal.ofReal (J f ·) * w ·)` along `f`
     yields `volume.withDensity (fun y ↦ ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[n - m])`, identifying the
     fiber Hausdorff measure `y ↦ μHE[n - m] (s ∩ f ⁻¹' {y})` as the Radon-Nikodym density of
     `Measure.map f ((volume.restrict s).withDensity (ENNReal.ofReal (J f ·)))`;
   * the Banach-space Bochner coarea formula holds assuming only `NullMeasurableSet s` and
     `IntegrableOn (fun x ↦ J f x • g x) s`.
3. **Specializations (`LipschitzOnWith`, `LocallyLipschitz`, `LipschitzWith`, `LinearMap`,
   `Submodule`).** For a `K`-Lipschitz map on an open set `U`, `J f x ≤ K ^ dim F` on `U`, so
   `IntegrableOn g s` alone implies `IntegrableOn (fun x ↦ J f x • g x) s`. Applying this to
   globally Lipschitz maps, linear maps `L : E →ₗ[ℝ] F`, and orthogonal projections
   `K.orthogonalProjectionOnto` gives Banach-space Fubini-type slicing along affine fibers.

## Main results

* `MeasureTheory.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber`: Bochner
  coarea formula on the regular locus.
* `LocallyLipschitzOn.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber`:
  weighted `ℝ≥0∞` coarea formula for locally Lipschitz maps on open sets.
* `LocallyLipschitzOn` Radon-Nikodym pushforward
  `map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure`:
  pushforward of Jacobian-weighted volume has Radon-Nikodym density given by fiber Hausdorff
  measure.
* `LocallyLipschitzOn.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber`: Bochner
  coarea formula for locally Lipschitz maps on open sets.
* `LipschitzOnWith.normDet_adjoint_fderiv_le`, `LipschitzWith.normDet_adjoint_fderiv_le`: uniform
  bound `(fderiv ℝ f x)†.normDet ≤ K ^ dim F` on the coarea Jacobian of a `K`-Lipschitz map.
* `LipschitzWith` global Bochner coarea
  `integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage_of_integrable`:
  global Bochner coarea formula for a Lipschitz map and an integrable `V`-valued function.
* `LinearMap.integral_setIntegral_preimage_singleton`,
  `Submodule.integral_setIntegral_preimage_orthogonalProjectionOnto`: Bochner slicing along fibers
  of linear maps and orthogonal projections.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.3 (Theorem 3.13, weighted coarea formula).
* H. Federer, *Geometric Measure Theory*, Theorem 3.2.12.
-/

public section

open MeasureTheory Measure Set Filter Module Function Topology
open scoped ENNReal NNReal

/-! ### Regular-locus pushforward and Bochner coarea -/

namespace MeasureTheory

section RegularPushforward

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {f : E → F} {s : Set E}

/-- Disintegration of Jacobian-weighted volume on the regular locus: pushing forward
`(volume.restrict s).withDensity (ENNReal.ofReal (J f ·) * w ·)` under `f` produces `volume`
weighted by the fiber Hausdorff integrals of `w`. -/
theorem map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {w : E → ℝ≥0∞}
    (hw : AEMeasurable w (volume.restrict s)) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) =
      volume.withDensity fun y ↦
        ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have h'f : AEMeasurable f (volume.restrict s) :=
    ContinuousOn.aemeasurable₀ (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt) hs
  have h''f : AEMeasurable f ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) :=
    h'f.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext fun t ht ↦ ?_
  have h't : NullMeasurableSet (f ⁻¹' t) (volume.restrict s) := h'f.nullMeasurableSet_preimage ht
  rw [map_apply_of_aemeasurable h''f ht, withDensity_apply₀ _ h't, withDensity_apply _ ht,
    restrict_restrict₀ h't,
    lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
      ((nullMeasurableSet_restrict hs).1 h't) (fun x hx ↦ hd x hx.2) (fun x hx ↦ hsurj x hx.2)
      (hw.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)),
    ← lintegral_indicator ht]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ t
  · have hset : (f ⁻¹' t ∩ s) ∩ f ⁻¹' {y} = s ∩ f ⁻¹' {y} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨h.2.symm ▸ hy, h.1⟩, h.2⟩⟩
    rw [indicator_of_mem hy, hset]
  · have hset : (f ⁻¹' t ∩ s) ∩ f ⁻¹' {y} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun h ↦ hy (h.2 ▸ h.1.1)
    rw [indicator_of_notMem hy, hset, Measure.restrict_empty, lintegral_zero_measure]

/-- Unweighted Radon-Nikodym form of coarea on the regular locus: pushing forward
`(volume.restrict s).withDensity (ENNReal.ofReal (J f ·))` under `f` yields `volume` weighted by the
fiber Hausdorff measures `y ↦ μHE[dim E - dim F] (s ∩ f ⁻¹' {y})`. -/
theorem map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) := by
  simpa using map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber hs hd
    hsurj (aemeasurable_const (b := (1 : ℝ≥0∞)))

end RegularPushforward

section RegularBochner

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E → F} {s : Set E} {g : E → V}

omit [MeasurableSpace F] [BorelSpace F] in
/-- On a Lebesgue-measurable set where `fderiv ℝ f` is surjective, strong measurability of the
Jacobian-weighted integrand `(fderiv ℝ f x)†.normDet • g x` implies strong measurability of `g`,
since the scalar factor `(fderiv ℝ f x)†.normDet` is measurable and everywhere nonzero on `s`. -/
private theorem aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hgm : AEStronglyMeasurable (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x)
      (volume.restrict s)) :
    AEStronglyMeasurable g (volume.restrict s) := by
  have hJ : Measurable fun x : E ↦ ((fderiv ℝ f x).adjoint.normDet)⁻¹ :=
    (TauCeti.measurable_normDet_adjoint_fderiv f).inv
  refine (hJ.aestronglyMeasurable.restrict.smul hgm).congr ?_
  filter_upwards [ae_restrict_mem₀ hs] with x hx
  exact inv_smul_smul₀ (ContinuousLinearMap.normDet_adjoint_ne_zero_iff.2 (hsurj x hx)) (g x)

omit [MeasurableSpace F] [BorelSpace F] in
/-- Integrability with respect to `(volume.restrict s).withDensity (ENNReal.ofReal (J f ·))` on the
regular locus `s` implies `volume.restrict s`-strong measurability. -/
private theorem aestronglyMeasurable_of_integrable_withDensity
    (hs : NullMeasurableSet s volume) (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {u : E → V}
    (hu : Integrable u ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)) :
    AEStronglyMeasurable u (volume.restrict s) := by
  have hw_meas : Measurable fun x : E ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet :=
    ENNReal.measurable_ofReal.comp (TauCeti.measurable_normDet_adjoint_fderiv f)
  have hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • u x) s := by
    simpa [IntegrableOn, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)] using
      (integrable_withDensity_iff_integrable_smul' hw_meas
        (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).1 hu
  exact aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul hs hsurj
    hint.aestronglyMeasurable

/-- Integrability of `(fderiv ℝ f x)†.normDet • g x` on the regular locus `s` implies
`μHE[dim E - dim F]`-integrability of `g` on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] := by
  have hgm : AEStronglyMeasurable g (volume.restrict s) :=
    aestronglyMeasurable_of_aestronglyMeasurable_normDet_adjoint_fderiv_smul hs hsurj
      hint.aestronglyMeasurable
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hco := lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hd hsurj
    hgm.eNorm
  have hfin : (∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, ‖g x‖ₑ ∂μHE[finrank ℝ E - finrank ℝ F]) ≠ ∞ := by
    rw [← hco]
    refine (lintegral_congr fun x ↦ ?_).symm.trans_lt hint.2 |>.ne
    rw [eNorm_smul, Real.eNorm_of_nonneg (LinearMap.normDet_nonneg _)]
  filter_upwards [ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt volume hdw hgm,
    ae_lt_top' (aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw hgm.eNorm)
      hfin] with y hy_meas hy_fin
  exact ⟨hy_meas, hy_fin⟩

/-- For an `L¹` function `u` with respect to `(volume.restrict s).withDensity w`, the `L¹` norm of
`u` equals the iterated fiber `L¹` integral of `u` when `s` lies in the regular locus. -/
private theorem lintegral_setLIntegral_enorm_eq_lintegral_withDensity
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {u : E → V}
    (hu : Integrable u ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)) :
    (∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, ‖u x‖ₑ ∂μHE[finrank ℝ E - finrank ℝ F]) =
      ∫⁻ x, ‖u x‖ₑ ∂(volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet := by
  have hw_meas : Measurable fun x : E ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet :=
    ENNReal.measurable_ofReal.comp (TauCeti.measurable_normDet_adjoint_fderiv f)
  have hum : AEStronglyMeasurable u (volume.restrict s) :=
    aestronglyMeasurable_of_integrable_withDensity hs hsurj hu
  rw [← lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hd hsurj hum.eNorm,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw_meas
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

omit [MeasurableSpace F] [BorelSpace F] in
/-- Integrability against the coarea Jacobian density `(volume.restrict s).withDensity ...` is
equivalent to `IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • u x) s`. -/
private theorem integrable_withDensity_normDet_adjoint_fderiv_iff {u : E → V} :
    Integrable u ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) ↔
      IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • u x) s := by
  have hw_meas : Measurable fun x : E ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet :=
    ENNReal.measurable_ofReal.comp (TauCeti.measurable_normDet_adjoint_fderiv f)
  rw [integrable_withDensity_iff_integrable_smul' hw_meas
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [IntegrableOn, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)]

/-- Strong measurability of the fiber integral plus `L¹(ν)` integrability implies Bochner
integrability of the fiber integral on `F`. -/
private theorem integrable_setIntegral_fiber_of_aestronglyMeasurable
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) {u : E → V}
    (hu : Integrable u ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet))
    (hum : AEStronglyMeasurable
      (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[finrank ℝ E - finrank ℝ F]) volume) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  ⟨hum, (lintegral_mono fun _ ↦ eNorm_integral_le_lintegral_eNorm _).trans_lt
    ((lintegral_setLIntegral_enorm_eq_lintegral_withDensity hs hd hsurj hu).trans_lt hu.2)⟩

/-- Indicator case of the regular-locus Bochner coarea induction. -/
private theorem aestronglyMeasurable_and_integral_withDensity_eq_indicator [CompleteSpace V]
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) (c : V) {t : Set E} (ht : MeasurableSet t)
    (hνt : ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) t < ∞) :
    AEStronglyMeasurable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, t.indicator (fun _ ↦ c) x
        ∂μHE[finrank ℝ E - finrank ℝ F]) volume ∧
      ∫ x, t.indicator (fun _ ↦ c) x ∂((volume.restrict s).withDensity
          fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
        ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, t.indicator (fun _ ↦ c) x
          ∂μHE[finrank ℝ E - finrank ℝ F] := by
  set k := finrank ℝ E - finrank ℝ F
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hm : AEMeasurable (fun y : F ↦ μHE[k] ((s ∩ t) ∩ f ⁻¹' {y})) volume :=
    aemeasurable_euclideanHausdorffMeasure_inter_preimage_of_hasFDerivWithinAt volume
      (hs.inter ht.nullMeasurableSet) fun x hx ↦ (hdw x hx.1).mono inter_subset_left
  have hco : ∫⁻ y : F, μHE[k] ((s ∩ t) ∩ f ⁻¹' {y}) =
      ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) t := by
    rw [withDensity_apply _ ht, Measure.restrict_restrict ht, inter_comm t s]
    exact lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      (hs.inter ht.nullMeasurableSet) (fun x hx ↦ hd x hx.1) (fun x hx ↦ hsurj x hx.1)
  have hfib (y : F) : (∫ x in s ∩ f ⁻¹' {y}, t.indicator (fun _ ↦ c) x ∂μHE[k]) =
      μHE[k].real ((s ∩ t) ∩ f ⁻¹' {y}) • c := by
    have hset : t ∩ (s ∩ f ⁻¹' {y}) = (s ∩ t) ∩ f ⁻¹' {y} := by ac_rfl
    rw [integral_indicator ht, Measure.restrict_restrict ht, setIntegral_const, hset]
  simp_rw [hfib]
  refine ⟨(ENNReal.measurable_toReal.comp_aemeasurable hm).aestronglyMeasurable.smul_const c, ?_⟩
  have hfin : ∀ᵐ y : F, μHE[k] ((s ∩ t) ∩ f ⁻¹' {y}) < ∞ :=
    ae_lt_top' hm (hco.trans_lt hνt).ne
  simp only [measureReal_def]
  rw [integral_indicator ht, setIntegral_const, integral_smul_const,
    integral_toReal hm hfin, hco, measureReal_def]

/-- Closedness in `L¹(ν)` of the class of functions satisfying fiber strong measurability and the
Bochner coarea identity on the regular locus. -/
private theorem isClosed_L1_aestronglyMeasurable_and_integral_withDensity_eq
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x)) :
    let ν := (volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet
    IsClosed {u : E →₁[ν] V |
      AEStronglyMeasurable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u x
        ∂μHE[finrank ℝ E - finrank ℝ F]) volume ∧
      ∫ x, u x ∂ν = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[finrank ℝ E - finrank ℝ F]} := by
  intro ν
  set k := finrank ℝ E - finrank ℝ F
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have h_int (v : E →₁[ν] V) : Integrable v ν := memLp_one_iff_integrable.1 (Lp.memLp v)
  refine isClosed_of_closure_subset fun a ha ↦ ?_
  obtain ⟨u, huP, hu_lim⟩ := mem_closure_iff_seq_limit.1 ha
  have hL1 : Tendsto (fun n ↦ ∫⁻ x, ‖u n x - a x‖ₑ ∂ν) atTop (𝓝 0) := by
    simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm',
      eLpNorm_one_eq_lintegral_eNorm ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable a)),
      Pi.sub_apply] using hu_lim
  set D : ℕ → F → ℝ≥0∞ := fun n y ↦ ∫⁻ x in s ∩ f ⁻¹' {y}, ‖u n x - a x‖ₑ ∂μHE[k]
  have hDm (n : ℕ) : AEMeasurable (D n) volume :=
    aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume hs hdw
      (aestronglyMeasurable_of_integrable_withDensity hs hsurj ((h_int (u n)).sub (h_int a))).eNorm
  have hD_lim : Tendsto (fun n ↦ ∫⁻ y, D n y) atTop (𝓝 0) := by
    refine hL1.congr fun n ↦ (lintegral_setLIntegral_enorm_eq_lintegral_withDensity hs hd hsurj
      ((h_int (u n)).sub (h_int a))).symm
  set U : ℕ → F → V := fun n y ↦ ∫ x in s ∩ f ⁻¹' {y}, u n x ∂μHE[k]
  set A : F → V := fun y ↦ ∫ x in s ∩ f ⁻¹' {y}, a x ∂μHE[k]
  have hbound (n : ℕ) : ∀ᵐ y : F, ‖U n y - A y‖ₑ ≤ D n y := by
    filter_upwards [ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt volume hdw
      (aestronglyMeasurable_of_integrable_withDensity hs hsurj (h_int (u n))),
      ae_aestronglyMeasurable_restrict_preimage_of_hasFDerivWithinAt volume hdw
        (aestronglyMeasurable_of_integrable_withDensity hs hsurj (h_int a))] with y hun ha'
    exact TauCeti.MeasureTheory.enorm_integral_sub_integral_le_lintegral_enorm_sub hun ha'
  obtain ⟨φ, -, hφ_ae⟩ := TauCeti.exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral hDm hD_lim
  have hA_meas : AEStronglyMeasurable A volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun j ↦ (huP (φ j)).1) ?_
    filter_upwards [hφ_ae, ae_all_iff.2 hbound] with y hy hb
    rw [tendsto_iff_edist_tendsto_0]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hy (fun _ ↦ zero_le)
      fun j ↦ (eDist_eq_eNorm_sub _ _).trans_le (hb (φ j))
  have hU_int (n : ℕ) : Integrable (U n) volume :=
    integrable_setIntegral_fiber_of_aestronglyMeasurable hs hd hsurj (h_int (u n)) (huP n).1
  have hLHS : Tendsto (fun n ↦ ∫ x, u n x ∂ν) atTop (𝓝 (∫ x, a x ∂ν)) :=
    tendsto_integral_of_L1 a (Lp.aestronglyMeasurable a)
      (Eventually.of_forall fun n ↦ h_int (u n)) hL1
  have hRHS : Tendsto (fun n ↦ ∫ y, U n y) atTop (𝓝 (∫ y, A y)) :=
    tendsto_integral_of_L1 A hA_meas (Eventually.of_forall hU_int)
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD_lim (fun _ ↦ zero_le)
        fun n ↦ lintegral_mono_ae (hbound n))
  exact ⟨hA_meas, tendsto_nhds_unique hLHS (by simpa only [(huP _).2] using hRHS)⟩

/-- Core `Integrable.induction` driver for fiber strong measurability and Bochner coarea on the
regular locus. -/
private theorem aestronglyMeasurable_and_integral_withDensity_eq
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hg : Integrable g ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)) :
    AEStronglyMeasurable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x
        ∂μHE[finrank ℝ E - finrank ℝ F]) volume ∧
      ∫ x, g x ∂((volume.restrict s).withDensity
          fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
        ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  by_cases hV : CompleteSpace V; swap
  · simp [integral_of_not_completeSpace hV, aestronglyMeasurable_const]
  let w : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet
  let ν := (volume.restrict s).withDensity w
  set k := finrank ℝ E - finrank ℝ F
  have hw_meas : Measurable w :=
    ENNReal.measurable_ofReal.comp (TauCeti.measurable_normDet_adjoint_fderiv f)
  have hdw (x : E) (hx : x ∈ s) : HasFDerivWithinAt f (fderiv ℝ f x) s x :=
    (hd x hx).hasFDerivAt.hasFDerivWithinAt
  have hfib_int (u : E → V) (hu : Integrable u ν) :
      ∀ᵐ y : F, IntegrableOn u (s ∩ f ⁻¹' {y}) μHE[k] :=
    ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd hsurj
      (integrable_withDensity_normDet_adjoint_fderiv_iff.1 hu)
  refine Integrable.induction
    (P := fun u : E → V ↦ AEStronglyMeasurable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[k])
      volume ∧ ∫ x, u x ∂ν = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, u x ∂μHE[k])
    (fun c t ht hνt ↦
      aestronglyMeasurable_and_integral_withDensity_eq_indicator hs hd hsurj c ht hνt)
    ?_ (isClosed_L1_aestronglyMeasurable_and_integral_withDensity_eq hs hd hsurj) ?_ hg
  · intro u₁ u₂ _ hu₁ hu₂ ih₁ ih₂
    have hadd : (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, (u₁ + u₂) x ∂μHE[k]) =ᵐ[volume]
        fun y : F ↦ (∫ x in s ∩ f ⁻¹' {y}, u₁ x ∂μHE[k]) +
          ∫ x in s ∩ f ⁻¹' {y}, u₂ x ∂μHE[k] := by
      filter_upwards [hfib_int u₁ hu₁, hfib_int u₂ hu₂] with y hy₁ hy₂
      exact integral_add hy₁ hy₂
    refine ⟨(ih₁.1.add ih₂.1).congr hadd.symm, ?_⟩
    have hi₁ := integrable_setIntegral_fiber_of_aestronglyMeasurable hs hd hsurj hu₁ ih₁.1
    have hi₂ := integrable_setIntegral_fiber_of_aestronglyMeasurable hs hd hsurj hu₂ ih₂.1
    calc ∫ x, (u₁ + u₂) x ∂ν = (∫ x, u₁ x ∂ν) + ∫ x, u₂ x ∂ν := integral_add hu₁ hu₂
      _ = ∫ y : F, ((∫ x in s ∩ f ⁻¹' {y}, u₁ x ∂μHE[k]) +
            ∫ x in s ∩ f ⁻¹' {y}, u₂ x ∂μHE[k]) := by rw [ih₁.2, ih₂.2, ← integral_add hi₁ hi₂]
      _ = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, (u₁ + u₂) x ∂μHE[k] := integral_congr_ae hadd.symm
  · intro u₁ u₂ hu₁₂ _ ih₁
    have hae_s : u₁ =ᵐ[volume.restrict s] u₂ := by
      filter_upwards [(ae_withDensity_iff hw_meas).1 hu₁₂, ae_restrict_mem₀ hs] with x hx hxs
      exact hx (ENNReal.ofReal_pos.2
        (ContinuousLinearMap.normDet_adjoint_pos_iff.2 (hsurj x hxs))).ne'
    have hfib : (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u₁ x ∂μHE[k]) =ᵐ[volume]
        fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, u₂ x ∂μHE[k] := by
      filter_upwards [ae_ae_eq_restrict_preimage_of_hasFDerivWithinAt volume hdw hae_s] with y hy
      exact integral_congr_ae hy
    exact ⟨ih₁.1.congr hfib,
      (integral_congr_ae hu₁₂).symm.trans (ih₁.2.trans (integral_congr_ae hfib))⟩

/-- Strong measurability of the Bochner fiber integral on the regular locus when the
Jacobian-weighted integrand is integrable on `s`. -/
theorem aestronglyMeasurable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    AEStronglyMeasurable
      (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  (aestronglyMeasurable_and_integral_withDensity_eq hs hd hsurj
    (integrable_withDensity_normDet_adjoint_fderiv_iff.2 hint)).1

/-- Bochner integrability of the fiber integrals `y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]`
on the regular locus when `(fderiv ℝ f x)†.normDet • g x` is integrable on `s`. -/
theorem integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  have hgν := integrable_withDensity_normDet_adjoint_fderiv_iff.2 hint
  exact integrable_setIntegral_fiber_of_aestronglyMeasurable hs hd hsurj hgν
    (aestronglyMeasurable_and_integral_withDensity_eq hs hd hsurj hgν).1

/-- **Bochner coarea formula on the regular locus.** For a map differentiable with surjective
derivative on a Lebesgue-measurable set `s`, if `(fderiv ℝ f x)†.normDet • g x` is Bochner
integrable on `s` with values in a real normed space `V`, then its integral over `s` equals the
iterated Bochner integral of `g` along the fibers `s ∩ f ⁻¹' {y}` with respect to normalized
Euclidean Hausdorff measure. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have hw_meas : Measurable fun x : E ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet :=
    ENNReal.measurable_ofReal.comp (TauCeti.measurable_normDet_adjoint_fderiv f)
  have hco := (aestronglyMeasurable_and_integral_withDensity_eq hs hd hsurj
    (integrable_withDensity_normDet_adjoint_fderiv_iff.2 hint)).2
  rw [integral_withDensity_eq_integral_toReal_smul hw_meas
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hco
  simpa only [ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)] using hco

/-- Triangle-inequality bound for fiber integrals on the regular locus:
`∫ y, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[k]‖ ≤ ∫ x in s, (fderiv ℝ f x)†.normDet * ‖g x‖`. -/
theorem integral_norm_setIntegral_fiber_le_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs : NullMeasurableSet s volume) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hsurj : ∀ x ∈ s, Surjective (fderiv ℝ f x))
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) ≤
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ := by
  have hnint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • ‖g x‖) s :=
    hint.norm.congr (Eventually.of_forall fun x ↦ by
      simp [norm_smul, Real.norm_of_nonneg (LinearMap.normDet_nonneg _)])
  have houter := integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd
    hsurj hint
  have hrhs_int := integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul hs hd
    hsurj hnint
  refine (integral_mono houter.norm hrhs_int fun y ↦ norm_integral_le_integral_norm _).trans_eq ?_
  simpa only [smul_eq_mul] using
    (integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs hd hsurj hnint).symm

end RegularBochner

end MeasureTheory

/-! ### Locally Lipschitz maps on open sets -/

namespace LocallyLipschitzOn

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {U s : Set E} {f : E → F}

omit [MeasurableSpace F] [BorelSpace F] in
/-- On the non-regular part `s \ G` of a subset `s ⊆ U` of an open set `U` where `f` is locally
Lipschitz, the coarea Jacobian `(fderiv ℝ f x)†.normDet` vanishes almost everywhere. -/
private theorem ae_restrict_sdiff_setOf_regular_normDet_adjoint_fderiv_eq_zero
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) :
    ∀ᵐ x ∂volume.restrict (s \ {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}),
      (fderiv ℝ f x).adjoint.normDet = 0 := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hUG : ∀ᵐ x ∂volume.restrict (U \ G), (fderiv ℝ f x).adjoint.normDet = 0 := by
    filter_upwards [ae_restrict_of_ae (hf.ae_differentiableAt_of_mem (μ := volume) hU),
      ae_restrict_mem (hU.measurableSet.diff hGm)] with x hx hxUG
    have hns : ¬Surjective (fderiv ℝ f x) := fun hsurj ↦ hxUG.2 ⟨hx hxUG.1, hsurj⟩
    exact ContinuousLinearMap.normDet_adjoint_eq_zero_iff.2 hns
  exact ae_mono (Measure.restrict_mono (sdiff_le_sdiff_right hsU) le_rfl) hUG

/-- **Weighted `ℝ≥0∞` coarea formula for locally Lipschitz maps on open sets (product-measurability
form).** Only `volume.restrict s`-almost-everywhere measurability of the product
`x ↦ ENNReal.ofReal (fderiv ℝ f x)†.normDet * w x` is needed: `w` need not be measurable on the
critical set where `(fderiv ℝ f x)†.normDet = 0`. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber_of_aemeasurable_mul
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {w : E → ℝ≥0∞}
    (hw : AEMeasurable (fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x)
      (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hwG : AEMeasurable w (volume.restrict (s ∩ G)) := by
    have hJinv : Measurable fun x : E ↦ (ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet)⁻¹ :=
      (ENNReal.measurable_ofReal.comp (TauCeti.measurable_normDet_adjoint_fderiv f)).inv
    refine (hJinv.aemeasurable.restrict.mul
      (hw.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))).congr ?_
    filter_upwards [ae_restrict_mem₀ (hs.inter hGm.nullMeasurableSet)] with x hx
    have hpos : 0 < (fderiv ℝ f x).adjoint.normDet :=
      ContinuousLinearMap.normDet_adjoint_pos_iff.2 hx.2.2
    exact ENNReal.inv_mul_cancel_left (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top
  have hzero : ∫⁻ x in s \ G, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hf.ae_restrict_sdiff_setOf_regular_normDet_adjoint_fderiv_eq_zero hU hsU]
      with x hx
    simp [hx]
  have hfib : (∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F]) =
      ∫⁻ y : F, ∫⁻ x in (s ∩ G) ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU] with y hy
    rw [hy]
  rw [← lintegral_inter_add_sdiff _ s hGm, hzero, add_zero, hfib]
  exact MeasureTheory.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2) hwG

/-- **Weighted `ℝ≥0∞` coarea formula for locally Lipschitz maps on open sets.** If `f` is locally
Lipschitz on an open set `U` containing a Lebesgue-measurable set `s` and `w : E → ℝ≥0∞` is
`volume.restrict s`-almost everywhere measurable, then the Jacobian-weighted integral of `w` over
`s` equals its iterated fiber integral with respect to normalized Hausdorff measure. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber_of_aemeasurable_mul
    hU hsU hs
    ((ENNReal.measurable_ofReal.comp
      (TauCeti.measurable_normDet_adjoint_fderiv f)).aemeasurable.restrict.mul hw)

/-- **Measure-disintegration form of the coarea formula** for a locally Lipschitz map on an open
set `U ⊇ s`: pushing forward `(volume.restrict s).withDensity (ENNReal.ofReal (J f ·) * w ·)` along
`f` produces `volume` weighted by `y ↦ ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[dim E - dim F]`. -/
theorem map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) =
      volume.withDensity fun y ↦
        ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  have h'f : AEMeasurable f (volume.restrict s) := (hf.mono hsU).continuousOn.aemeasurable₀ hs
  have h''f : AEMeasurable f ((volume.restrict s).withDensity
      fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) :=
    h'f.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext fun t ht ↦ ?_
  have h't : NullMeasurableSet (f ⁻¹' t) (volume.restrict s) := h'f.nullMeasurableSet_preimage ht
  rw [map_apply_of_aemeasurable h''f ht, withDensity_apply₀ _ h't, withDensity_apply _ ht,
    restrict_restrict₀ h't,
    hf.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hU
      (inter_subset_right.trans hsU) ((nullMeasurableSet_restrict hs).1 h't)
      (hw.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)),
    ← lintegral_indicator ht]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ t
  · have hset : (f ⁻¹' t ∩ s) ∩ f ⁻¹' {y} = s ∩ f ⁻¹' {y} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨h.2.symm ▸ hy, h.1⟩, h.2⟩⟩
    rw [indicator_of_mem hy, hset]
  · have hset : (f ⁻¹' t ∩ s) ∩ f ⁻¹' {y} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun h ↦ hy (h.2 ▸ h.1.1)
    rw [indicator_of_notMem hy, hset, Measure.restrict_empty, lintegral_zero_measure]

/-- **Radon-Nikodym form of the coarea formula** for a locally Lipschitz map on an open set `U ⊇ s`:
the pushforward of `(volume.restrict s).withDensity (ENNReal.ofReal (J f ·))` under `f` has density
`y ↦ μHE[dim E - dim F] (s ∩ f ⁻¹' {y})` with respect to Lebesgue measure on `F`. -/
theorem map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) := by
  simpa using hf.map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber
    hU hsU hs (aemeasurable_const (b := (1 : ℝ≥0∞)))

/-- If `f` is locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable and
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`, then `g` is `μHE[dim E - dim F]`-integrable
on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_integrableOn_fiber (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U)
    (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hfibG := MeasureTheory.ae_integrableOn_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
    (hint.mono_set inter_subset_left)
  filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU, hfibG] with y hy hyG
  rwa [IntegrableOn, hy]

/-- If `f` is locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable and
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`, then the Bochner fiber integral
`y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_setIntegral_fiber (hf : LocallyLipschitzOn U f) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    AEStronglyMeasurable
      (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hreg :=
    MeasureTheory.aestronglyMeasurable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
      (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
      (hint.mono_set inter_subset_left)
  refine hreg.congr ?_
  filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU] with y hy
  rw [hy]

/-- If `f` is locally Lipschitz on an open set `U ⊇ s` with `s` Lebesgue measurable and
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`, then the Bochner fiber integral
`y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` is Bochner integrable on `F`. -/
theorem integrable_setIntegral_fiber (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U)
    (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  refine (MeasureTheory.integrable_setIntegral_fiber_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
    (hint.mono_set inter_subset_left)).congr ?_
  filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU] with y hy
  rw [hy]

/-- Triangle-inequality bound for Bochner fiber integrals of a locally Lipschitz map on an open
set: `∫ y, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[k]‖ ≤ ∫ x in s, (fderiv ℝ f x)†.normDet * ‖g x‖`. -/
theorem integral_norm_setIntegral_fiber_le (hf : LocallyLipschitzOn U f) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) ≤
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hfib : (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) =
      ∫ y : F, ‖∫ x in (s ∩ G) ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU] with y hy
    rw [hy]
  have hnint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * ‖g x‖) s :=
    hint.norm.congr (Eventually.of_forall fun x ↦ by
      simp [norm_smul, Real.norm_of_nonneg (LinearMap.normDet_nonneg _)])
  have hzero : ∫ x in s \ G, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf.ae_restrict_sdiff_setOf_regular_normDet_adjoint_fderiv_eq_zero hU hsU]
      with x hx
    simp [hx]
  rw [hfib, ← integral_inter_add_sdiff hGm hnint, hzero, add_zero]
  exact MeasureTheory.integral_norm_setIntegral_fiber_le_of_integrableOn_normDet_adjoint_fderiv_smul
    (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
    (hint.mono_set inter_subset_left)

/-- **Bochner coarea formula for locally Lipschitz maps on open sets.** Let `f : E → F` be locally
Lipschitz on an open set `U` containing a Lebesgue-measurable set `s`, and let `g : E → V` take
values in a real normed space `V`. If `x ↦ (fderiv ℝ f x)†.normDet • g x` is Bochner integrable on
`s`, then
`∫ x in s, (fderiv ℝ f x)†.normDet • g x = ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]`.
Neither completeness of `V` nor a separate measurability hypothesis on `g` is needed. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  set G := {x | DifferentiableAt ℝ f x ∧ Surjective (fderiv ℝ f x)}
  have hGm : MeasurableSet G := TauCeti.measurableSet_setOf_differentiableAt_surjective_fderiv f
  have hzero : ∫ x in s \ G, (fderiv ℝ f x).adjoint.normDet • g x = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf.ae_restrict_sdiff_setOf_regular_normDet_adjoint_fderiv_eq_zero hU hsU]
      with x hx
    simp [hx]
  have hfib : (∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) =
      ∫ y : F, ∫ x in (s ∩ G) ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
    refine integral_congr_ae ?_
    filter_upwards [hf.ae_restrict_inter_setOf_regular_preimage_eq hU hsU] with y hy
    rw [hy]
  rw [← integral_inter_add_sdiff hGm hint, hzero, add_zero, hfib]
  exact MeasureTheory.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hs.inter hGm.nullMeasurableSet) (fun _ hx ↦ hx.2.1) (fun _ hx ↦ hx.2.2)
    (hint.mono_set inter_subset_left)

/-- **Signed real weighted coarea formula for locally Lipschitz maps on open sets.** -/
theorem integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_fiber
    (hf : LocallyLipschitzOn U f) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → ℝ} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet * g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hU hsU hs hint

end LocallyLipschitzOn

/-! ### Lipschitz maps on open sets -/

namespace LipschitzOnWith

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {U s : Set E} {f : E → F} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- If `f` is `K`-Lipschitz on an open set `U`, then its coarea Jacobian at every `x ∈ U` is
bounded by `K ^ dim F`. -/
theorem normDet_adjoint_fderiv_le (hf : LipschitzOnWith K f U) (hU : IsOpen U)
    {x : E} (hx : x ∈ U) :
    (fderiv ℝ f x).adjoint.normDet ≤ (K : ℝ) ^ finrank ℝ F :=
  (fderiv ℝ f x).normDet_adjoint_le_opNorm_pow.trans
    (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hx) hf) _)

omit [MeasurableSpace F] [BorelSpace F] in
/-- On a subset `s` of an open set `U` where `f` is `K`-Lipschitz, Bochner integrability of `g` on
`s` implies Bochner integrability of `(fderiv ℝ f x)†.normDet • g x` on `s`. -/
theorem integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) {g : E → V}
    (hg : IntegrableOn g s) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s := by
  have hU' : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) (s ∩ U) := by
    refine (hg.mono_set inter_subset_left).bdd_smul ((K : ℝ) ^ finrank ℝ F)
      (TauCeti.measurable_normDet_adjoint_fderiv f).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (ae_restrict_mem hU.measurableSet)] with x hx
    rw [Real.norm_of_nonneg (LinearMap.normDet_nonneg _)]
    exact hf.normDet_adjoint_fderiv_le hU hx
  rwa [inter_eq_left.2 hsU] at hU'

/-- Weighted `ℝ≥0∞` coarea formula for a `K`-Lipschitz map on an open set `U ⊇ s`. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {w : E → ℝ≥0∞} (hw : AEMeasurable w (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitzOn.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hU hsU hs hw

/-- For a `K`-Lipschitz map on an open set `U ⊇ s` with `s` Lebesgue measurable, `IntegrableOn g s`
implies fiberwise `μHE[dim E - dim F]`-integrability of `g` for almost every `y : F`. -/
theorem ae_integrableOn_fiber_of_integrableOn (hf : LipschitzOnWith K f U) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitzOn.ae_integrableOn_fiber hU hsU hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hU hsU hg)

/-- For a `K`-Lipschitz map on an open set `U ⊇ s` with `s` Lebesgue measurable, `IntegrableOn g s`
implies Bochner integrability of the fiber integrals on `F`. -/
theorem integrable_setIntegral_fiber_of_integrableOn (hf : LipschitzOnWith K f U) (hU : IsOpen U)
    (hsU : s ⊆ U) (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.locallyLipschitzOn.integrable_setIntegral_fiber hU hsU hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hU hsU hg)

/-- Bochner coarea formula for a `K`-Lipschitz map on an open set `U ⊇ s` when
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitzOn.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    hU hsU hs hint

/-- Bochner coarea formula for a `K`-Lipschitz map on an open set `U ⊇ s` assuming only
`IntegrableOn g s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber_of_integrableOn
    (hf : LipschitzOnWith K f U) (hU : IsOpen U) (hsU : s ⊆ U) (hs : NullMeasurableSet s)
    {g : E → V} (hg : IntegrableOn g s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hU hsU hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hU hsU hg)

end LipschitzOnWith

/-! ### Globally locally Lipschitz maps -/

namespace LocallyLipschitz

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set E} {f : E → F}

/-- **Weighted `ℝ≥0∞` coarea formula for locally Lipschitz maps** on a Lebesgue-measurable set
`s`. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {w : E → ℝ≥0∞}
    (hw : AEMeasurable w (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.locallyLipschitzOn (s := univ))
    |>.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
      isOpen_univ (subset_univ s) hs hw

/-- **Global weighted `ℝ≥0∞` coarea formula for locally Lipschitz maps.** -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_preimage
    (hf : LocallyLipschitz f) {w : E → ℝ≥0∞} (hw : AEMeasurable w) :
    ∫⁻ x : E, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  simpa using hf.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    MeasurableSet.univ.nullMeasurableSet hw.restrict

/-- Measure-disintegration form of the coarea formula for a locally Lipschitz map on a
Lebesgue-measurable set `s`. -/
theorem map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {w : E → ℝ≥0∞}
    (hw : AEMeasurable w (volume.restrict s)) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x) =
      volume.withDensity fun y ↦
        ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.locallyLipschitzOn (s := univ))
    |>.map_withDensity_normDet_adjoint_fderiv_mul_eq_withDensity_setLIntegral_fiber
      isOpen_univ (subset_univ s) hs hw

/-- Radon-Nikodym form of the coarea formula for a locally Lipschitz map on `s`. -/
theorem map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) :=
  (hf.locallyLipschitzOn (s := univ))
    |>.map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure
      isOpen_univ (subset_univ s) hs

/-- Global Radon-Nikodym form of the coarea formula for a locally Lipschitz map: pushing forward
`volume.withDensity (ENNReal.ofReal (J f ·))` under `f` yields `volume` weighted by the fiber
Hausdorff measures `y ↦ μHE[dim E - dim F] (f ⁻¹' {y})`. -/
theorem map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure_preimage
    (hf : LocallyLipschitz f) :
    Measure.map f (volume.withDensity fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (f ⁻¹' {y}) := by
  simpa using hf.map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure
    MeasurableSet.univ.nullMeasurableSet

/-- Almost-everywhere fiberwise integrability for a locally Lipschitz map on a Lebesgue-measurable
set `s`. -/
theorem ae_integrableOn_fiber (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.locallyLipschitzOn (s := univ)).ae_integrableOn_fiber isOpen_univ (subset_univ s) hs hint

/-- Global almost-everywhere fiberwise integrability for a locally Lipschitz map. -/
theorem ae_integrableOn_preimage (hf : LocallyLipschitz f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∀ᵐ y : F, IntegrableOn g (f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] := by
  simpa using hf.ae_integrableOn_fiber MeasurableSet.univ.nullMeasurableSet hint.integrableOn

/-- Bochner integrability of the fiber integrals for a locally Lipschitz map on `s`. -/
theorem integrable_setIntegral_fiber (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  (hf.locallyLipschitzOn (s := univ)).integrable_setIntegral_fiber isOpen_univ (subset_univ s) hs
    hint

/-- Global Bochner integrability of the fiber integrals for a locally Lipschitz map. -/
theorem integrable_setIntegral_preimage (hf : LocallyLipschitz f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    Integrable (fun y : F ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume := by
  simpa using hf.integrable_setIntegral_fiber MeasurableSet.univ.nullMeasurableSet hint.integrableOn

/-- Triangle-inequality bound for Bochner fiber integrals of a locally Lipschitz map. -/
theorem integral_norm_setIntegral_fiber_le (hf : LocallyLipschitz f) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    (∫ y : F, ‖∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]‖) ≤
      ∫ x in s, (fderiv ℝ f x).adjoint.normDet * ‖g x‖ :=
  (hf.locallyLipschitzOn (s := univ)).integral_norm_setIntegral_fiber_le isOpen_univ
    (subset_univ s) hs hint

/-- **Bochner coarea formula for locally Lipschitz maps** on a Lebesgue-measurable set `s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  (hf.locallyLipschitzOn (s := univ))
    |>.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
      isOpen_univ (subset_univ s) hs hint

/-- **Global Bochner coarea formula for locally Lipschitz maps.** -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage
    (hf : LocallyLipschitz f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] := by
  simpa using hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    MeasurableSet.univ.nullMeasurableSet hint.integrableOn

/-- **Signed real weighted coarea formula for locally Lipschitz maps** on a Lebesgue-measurable set
`s`. -/
theorem integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_fiber
    (hf : LocallyLipschitz f) (hs : NullMeasurableSet s) {g : E → ℝ}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet * g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs hint

/-- **Global signed real weighted coarea formula for locally Lipschitz maps.** -/
theorem integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_preimage
    (hf : LocallyLipschitz f) {g : E → ℝ}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet * g x) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet * g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage hint

end LocallyLipschitz

/-! ### Globally Lipschitz maps -/

namespace LipschitzWith

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set E} {f : E → F} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The coarea Jacobian `(fderiv ℝ f x)†.normDet` of a `K`-Lipschitz map `f : E → F` is everywhere
at most `K ^ dim F`. -/
theorem normDet_adjoint_fderiv_le (hf : LipschitzWith K f) (x : E) :
    (fderiv ℝ f x).adjoint.normDet ≤ (K : ℝ) ^ finrank ℝ F :=
  hf.lipschitzOnWith.normDet_adjoint_fderiv_le isOpen_univ (mem_univ x)

omit [MeasurableSpace F] [BorelSpace F] in
/-- For a `K`-Lipschitz map `f`, Bochner integrability of `g` on `s` implies Bochner integrability
of `(fderiv ℝ f x)†.normDet • g x` on `s`. -/
theorem integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn (hf : LipschitzWith K f)
    {g : E → V} (hg : IntegrableOn g s) :
    IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s :=
  hf.lipschitzOnWith.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn isOpen_univ
    (subset_univ s) hg

omit [MeasurableSpace F] [BorelSpace F] in
/-- For a `K`-Lipschitz map `f`, Bochner integrability of `g` implies Bochner integrability of
`(fderiv ℝ f x)†.normDet • g x`. -/
theorem integrable_normDet_adjoint_fderiv_smul_of_integrable (hf : LipschitzWith K f)
    {g : E → V} (hg : Integrable g) :
    Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x := by
  simpa using hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn (s := univ)
    hg.integrableOn

/-- **Weighted `ℝ≥0∞` coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`. -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {w : E → ℝ≥0∞}
    (hw : AEMeasurable w (volume.restrict s)) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in s ∩ f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber hs hw

/-- **Global weighted `ℝ≥0∞` coarea formula for Lipschitz maps.** -/
theorem lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_preimage
    (hf : LipschitzWith K f) {w : E → ℝ≥0∞} (hw : AEMeasurable w) :
    ∫⁻ x : E, ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet * w x =
      ∫⁻ y : F, ∫⁻ x in f ⁻¹' {y}, w x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_preimage hw

/-- Radon-Nikodym form of the coarea formula for a Lipschitz map on `s`. -/
theorem map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) :
    Measure.map f ((volume.restrict s).withDensity
        fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (s ∩ f ⁻¹' {y}) :=
  hf.locallyLipschitz
    |>.map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure hs

/-- Global Radon-Nikodym form of the coarea formula for a Lipschitz map. -/
theorem map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure_preimage
    (hf : LipschitzWith K f) :
    Measure.map f (volume.withDensity fun x ↦ ENNReal.ofReal (fderiv ℝ f x).adjoint.normDet) =
      volume.withDensity fun y ↦ μHE[finrank ℝ E - finrank ℝ F] (f ⁻¹' {y}) :=
  hf.locallyLipschitz
    |>.map_withDensity_normDet_adjoint_fderiv_eq_withDensity_euclideanHausdorffMeasure_preimage

/-- Almost-everywhere fiberwise integrability for a Lipschitz map on `s` when
`(fderiv ℝ f x)†.normDet • g x` is integrable on `s`. -/
theorem ae_integrableOn_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.ae_integrableOn_fiber hs hint

/-- For a Lipschitz map, `IntegrableOn g s` on a Lebesgue-measurable set `s` implies
`μHE[dim E - dim F]`-integrability of `g` on almost every fiber `s ∩ f ⁻¹' {y}`. -/
theorem ae_integrableOn_fiber_of_integrableOn (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    {g : E → V} (hg : IntegrableOn g s) :
    ∀ᵐ y : F, IntegrableOn g (s ∩ f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.ae_integrableOn_fiber hs (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hg)

/-- Global almost-everywhere fiberwise integrability for a Lipschitz map when
`(fderiv ℝ f x)†.normDet • g x` is integrable. -/
theorem ae_integrableOn_preimage (hf : LipschitzWith K f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∀ᵐ y : F, IntegrableOn g (f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.ae_integrableOn_preimage hint

/-- For a Lipschitz map, `Integrable g` implies `μHE[dim E - dim F]`-integrability of `g` on almost
every fiber `f ⁻¹' {y}`. -/
theorem ae_integrableOn_preimage_of_integrable (hf : LipschitzWith K f) {g : E → V}
    (hg : Integrable g) :
    ∀ᵐ y : F, IntegrableOn g (f ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  hf.ae_integrableOn_preimage (hf.integrable_normDet_adjoint_fderiv_smul_of_integrable hg)

/-- Bochner integrability of the fiber integrals for a Lipschitz map on `s`. -/
theorem integrable_setIntegral_fiber (hf : LipschitzWith K f) (hs : NullMeasurableSet s)
    {g : E → V} (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.locallyLipschitz.integrable_setIntegral_fiber hs hint

/-- For a Lipschitz map, `IntegrableOn g s` on a Lebesgue-measurable set `s` implies Bochner
integrability of `y ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` on `F`. -/
theorem integrable_setIntegral_fiber_of_integrableOn (hf : LipschitzWith K f)
    (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    Integrable (fun y : F ↦ ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.integrable_setIntegral_fiber hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hg)

/-- Global Bochner integrability of the fiber integrals for a Lipschitz map when
`(fderiv ℝ f x)†.normDet • g x` is integrable. -/
theorem integrable_setIntegral_preimage (hf : LipschitzWith K f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    Integrable (fun y : F ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.locallyLipschitz.integrable_setIntegral_preimage hint

/-- For a Lipschitz map, `Integrable g` implies Bochner integrability of
`y ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[dim E - dim F]` on `F`. -/
theorem integrable_setIntegral_preimage_of_integrable (hf : LipschitzWith K f) {g : E → V}
    (hg : Integrable g) :
    Integrable (fun y : F ↦ ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  hf.integrable_setIntegral_preimage (hf.integrable_normDet_adjoint_fderiv_smul_of_integrable hg)

/-- **Bochner coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → V}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs hint

/-- **Bochner coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`, assuming only
`IntegrableOn g s`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber_of_integrableOn
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → V} (hg : IntegrableOn g s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_fiber hs
    (hf.integrableOn_normDet_adjoint_fderiv_smul_of_integrableOn hg)

/-- **Global Bochner coarea formula for Lipschitz maps.** -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage
    (hf : LipschitzWith K f) {g : E → V}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet • g x) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage hint

/-- **Global Bochner coarea formula for Lipschitz maps** assuming only `Integrable g`. -/
theorem integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage_of_integrable
    (hf : LipschitzWith K f) {g : E → V} (hg : Integrable g) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet • g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage
    (hf.integrable_normDet_adjoint_fderiv_smul_of_integrable hg)

/-- **Signed real weighted coarea formula for Lipschitz maps** on a Lebesgue-measurable set `s`. -/
theorem integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_fiber
    (hf : LipschitzWith K f) (hs : NullMeasurableSet s) {g : E → ℝ}
    (hint : IntegrableOn (fun x ↦ (fderiv ℝ f x).adjoint.normDet * g x) s) :
    ∫ x in s, (fderiv ℝ f x).adjoint.normDet * g x =
      ∫ y : F, ∫ x in s ∩ f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_fiber hs hint

/-- **Global signed real weighted coarea formula for Lipschitz maps.** -/
theorem integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_preimage
    (hf : LipschitzWith K f) {g : E → ℝ}
    (hint : Integrable fun x ↦ (fderiv ℝ f x).adjoint.normDet * g x) :
    ∫ x : E, (fderiv ℝ f x).adjoint.normDet * g x =
      ∫ y : F, ∫ x in f ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] :=
  hf.locallyLipschitz.integral_normDet_adjoint_fderiv_mul_eq_integral_setIntegral_preimage hint

end LipschitzWith

/-! ### Linear maps and orthogonal projections -/

namespace LinearMap

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Every Bochner-integrable function `g : E → V` is `μHE[dim E - dim F]`-integrable on almost
every fiber `L ⁻¹' {y}` of any linear map `L : E →ₗ[ℝ] F`. -/
theorem ae_integrableOn_preimage_singleton (L : E →ₗ[ℝ] F) {g : E → V} (hg : Integrable g) :
    ∀ᵐ y : F, IntegrableOn g (L ⁻¹' {y}) μHE[finrank ℝ E - finrank ℝ F] :=
  L.toContinuousLinearMap.lipschitzWith.ae_integrableOn_preimage_of_integrable hg

/-- For any linear map `L : E →ₗ[ℝ] F` and Bochner-integrable `g : E → V`, the fiber integral
`y ↦ ∫ x in L ⁻¹' {y}, g x ∂μHE[dim E - dim F]` is Bochner integrable on `F`. -/
theorem integrable_setIntegral_preimage_singleton (L : E →ₗ[ℝ] F) {g : E → V} (hg : Integrable g) :
    Integrable (fun y : F ↦ ∫ x in L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F]) volume :=
  L.toContinuousLinearMap.lipschitzWith.integrable_setIntegral_preimage_of_integrable hg

/-- **Bochner coarea formula for linear maps.** Integrating a Bochner-integrable `V`-valued
function over the affine fibers `L ⁻¹' {y}` gives `L.adjoint.normDet • ∫ x, g x`. Both sides vanish
when `L` is not surjective. -/
theorem integral_setIntegral_preimage_singleton (L : E →ₗ[ℝ] F) {g : E → V} (hg : Integrable g) :
    ∫ y : F, ∫ x in L ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ F] =
      L.adjoint.normDet • ∫ x, g x := by
  have hL : LipschitzWith ‖L.toContinuousLinearMap‖₊ (L : E → F) :=
    L.toContinuousLinearMap.lipschitzWith
  have hco :=
    hL.integral_normDet_adjoint_fderiv_smul_eq_integral_setIntegral_preimage_of_integrable hg
  have hJ (x : E) : (fderiv ℝ (L : E → F) x).adjoint.normDet = L.adjoint.normDet := by
    rw [← LinearMap.coe_toContinuousLinearMap' L, L.toContinuousLinearMap.fderiv,
      ← LinearMap.adjoint_toContinuousLinearMap]
    rfl
  simp only [hJ] at hco
  rw [← hco, integral_smul]

end LinearMap

namespace Submodule

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Every Bochner-integrable function `g : E → V` is `μHE[dim E - dim K]`-integrable on almost
every affine fiber `K.orthogonalProjectionOnto ⁻¹' {y}` parallel to `Kᗮ`. -/
theorem ae_integrableOn_preimage_orthogonalProjectionOnto (K : Submodule ℝ E) {g : E → V}
    (hg : Integrable g) :
    ∀ᵐ y : K, IntegrableOn g (K.orthogonalProjectionOnto ⁻¹' {y})
      μHE[finrank ℝ E - finrank ℝ K] :=
  (K.orthogonalProjectionOnto : E →ₗ[ℝ] K).ae_integrableOn_preimage_singleton hg

/-- For a subspace `K ≤ E` and Bochner-integrable `g : E → V`, the affine-slice integral
`y ↦ ∫ x in K.orthogonalProjectionOnto ⁻¹' {y}, g x ∂μHE[dim E - dim K]` is Bochner integrable on
`K`. -/
theorem integrable_setIntegral_preimage_orthogonalProjectionOnto (K : Submodule ℝ E) {g : E → V}
    (hg : Integrable g) :
    Integrable (fun y : K ↦ ∫ x in K.orthogonalProjectionOnto ⁻¹' {y}, g x
      ∂μHE[finrank ℝ E - finrank ℝ K]) volume :=
  (K.orthogonalProjectionOnto : E →ₗ[ℝ] K).integrable_setIntegral_preimage_singleton hg

/-- **Bochner slicing by orthogonal projections.** Integrating a Bochner-integrable `V`-valued
function over the affine subspaces `K.orthogonalProjectionOnto ⁻¹' {y}` parallel to `Kᗮ` recovers
its Lebesgue Bochner integral over `E`. -/
theorem integral_setIntegral_preimage_orthogonalProjectionOnto (K : Submodule ℝ E) {g : E → V}
    (hg : Integrable g) :
    ∫ y : K, ∫ x in K.orthogonalProjectionOnto ⁻¹' {y}, g x ∂μHE[finrank ℝ E - finrank ℝ K] =
      ∫ x, g x := by
  have h := (K.orthogonalProjectionOnto : E →ₗ[ℝ] K).integral_setIntegral_preimage_singleton hg
  rw [ContinuousLinearMap.adjoint_toLinearMap, K.adjoint_orthogonalProjectionOnto] at h
  simpa using h

end Submodule

end
