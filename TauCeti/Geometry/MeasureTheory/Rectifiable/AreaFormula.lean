/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Rademacher
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import TauCeti.Topology.Algebra.InfiniteSum.Extend

/-!
# The tangential area formula on countably rectifiable sets

Let `E ⊆ V` be a countably `k`-rectifiable, `μHE[k]`-null-measurable set with locally finite
restricted measure `μHE[k].restrict E`, and let `g : V → W` be locally Lipschitz on `E`. The
tangential area formula transports `k`-dimensional Euclidean Hausdorff measure along `g` via
`tangentialJacobian k E g`: for every `μHE[k].restrict E`-a.e. measurable weight `w : V → ℝ≥0∞`,
`∫⁻ x in E, ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]` equals the `μHE[k]`-integral of
the fiber sums `y ↦ ∑' x : ↥(E ∩ g ⁻¹' {y}), w x` (with `encard` multiplicity when `w = 1`, and
real-valued `∫` and `ncard` versions under `IntegrableOn`).

Each Borel bi-Lipschitz patch reduces the integral to the Euclidean area formula with
multiplicity (`MeasureTheory.Function.AreaFormula.Multiplicity`) via the tangential Jacobian
chain rule from `Rectifiable.Rademacher`, and summing over a disjoint cover gives both the
weighted multiplicity formula and the unweighted injective change-of-variables formula (without
measurability on the target weight). In particular, if `tangentialFDeriv k E g` has rank `< k`
almost everywhere on `E`, then `μHE[k] (g '' E) = 0`.

## References

* H. Federer, *Geometric Measure Theory*, 3.2.20 (area formula for rectifiable sets).
* L. Simon, *Lectures on Geometric Measure Theory*, §12 (area formula).
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff
namespace TauCeti
section Patch
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] {k : ℕ} {E : Set V} {g gExt : V → W}
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] {KExt : ℝ≥0}
    (hgExt_lip : LipschitzWith KExt gExt) {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ
    (Fin k) → V} (hgExt_eq : EqOn g gExt (f '' B)) {K_f L_f : ℝ≥0} (hBm : MeasurableSet B) (hf_lip :
    LipschitzWith K_f f) (hf_anti : AntilipschitzWith L_f (B.domRestrict f)) (hsub : f '' B ⊆ E)
include hEm hgExt_lip hgExt_eq hBm hf_lip hf_anti hsub
omit [MeasurableSpace W] [BorelSpace W] in
private lemma lintegral_patch_tangentialJacobian_mul (w : V → ℝ≥0∞) : (∫⁻ x in f '' B,
    ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) = ∫⁻ u in B, ENNReal.ofReal (fderiv ℝ
    (gExt ∘ f) u).normDet * w (f u) := by
  let U := EuclideanSpace ℝ (Fin k)
  refine (by simpa only [U, finrank_euclideanSpace_fin] using
      hf_lip.lintegral_image_eq_lintegral_normDet_fderiv_mul hBm (injOn_iff_injective.mpr
        hf_anti.injective) _ : _ = ∫⁻ u in B, ENNReal.ofReal (fderiv ℝ f u).normDet *
      (ENNReal.ofReal (tangentialJacobian k E g (f u)) * w (f u))).trans
    (setLIntegral_congr_fun_ae hBm ?_)
  filter_upwards [ae_regular_and_density_on_patch hEm hBm hf_lip hf_anti, (hgExt_lip.comp
    hf_lip).ae_differentiableAt] with u hreg hgf_diff huB
  obtain ⟨hf_diff, -, hdens, hdiff⟩ := hreg huB
  have hmul : tangentialJacobian k E g (f u) * (fderiv ℝ f u).normDet = (fderiv ℝ (gExt ∘ f)
    u).normDet := by
    simpa only [U, finrank_euclideanSpace_fin] using
      hf_diff.hasFDerivAt.hasFDerivWithinAt.tangentialJacobian_mul_normDet hf_anti huB hsub
        hdens (by rwa [finrank_euclideanSpace_fin])
        (hgf_diff.hasFDerivAt.hasFDerivWithinAt.congr
          (fun _ hv => hgExt_eq (mem_image_of_mem f hv)) (hgExt_eq (mem_image_of_mem f huB)))
  rw [← mul_assoc, mul_comm (ENNReal.ofReal (fderiv ℝ f u).normDet), ← ENNReal.ofReal_mul
    (tangentialJacobian_nonneg _ _ _ _), hmul]
private lemma patch_area_formula {w : V → ℝ≥0∞} (hw : Measurable w) : AEMeasurable (fun y => ∑' x :
    ↥((f '' B) ∩ g ⁻¹' {y}), w x) μHE[k] ∧ (∫⁻ x in f '' B, ENNReal.ofReal (tangentialJacobian k E g
    x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
  have htsum_eq (y : W) :
      (∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) = ∑' u : ↥(B ∩ (gExt ∘ f) ⁻¹' {y}), w (f u) :=
    ((injOn_iff_injective.mpr hf_anti.injective).tsum_fiber_image g w y).trans <|
      tsum_congr_set_coe (fun u => w (f u)) <| Set.ext fun u => and_congr_right fun huB => by
        simp only [mem_preimage, mem_singleton_iff, comp_apply, hgExt_eq (mem_image_of_mem f huB)]
  have hgf := hgExt_lip.comp hf_lip; have hwm := hw.comp hf_lip.continuous.measurable
  refine ⟨by simp_rw [htsum_eq]; simpa only [finrank_euclideanSpace_fin, comp_apply] using
      hgf.aemeasurable_tsum_fiber hBm.nullMeasurableSet hwm,
    (lintegral_patch_tangentialJacobian_mul hEm hgExt_lip hgExt_eq hBm hf_lip hf_anti hsub w).trans
      (by simp_rw [htsum_eq]; simpa only [finrank_euclideanSpace_fin, comp_apply] using
        hgf.lintegral_normDet_fderiv_mul_eq_lintegral_tsum hBm.nullMeasurableSet hwm)⟩
end Patch
end TauCeti
section RectifiableAreaFormula
open TauCeti
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] {k : ℕ} {E : Set V} {g : V → W}
local notation "J" => tangentialJacobian k E g
local notation "D" => tangentialFDeriv k E g
local notation "ofReal" => ENNReal.ofReal
namespace LocallyLipschitzOn
variable (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
private lemma aemeasurable_and_lintegral_tsum_fiber {w : V → ℝ≥0∞}
    (hw : AEMeasurable w (μHE[k].restrict E)) :
    AEMeasurable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), w x) μHE[k] ∧
      (∫⁻ x in E, ofReal (J x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
  let w' := hw.mk w; have hw_ae := hg.tsum_fiber_congr_ae_fun hw.ae_eq_mk
  obtain ⟨B, f, gExt, _, _, _, hBm, hTm, hbi, hgExt, hdisj, hsubE, hcover_ae⟩ :=
    hg.exists_disjoint_measurable_bilipschitz_extension_cover hE hEm
  have hp (n : ℕ) := patch_area_formula hEm (hgExt n).1 (hgExt n).2 (hBm n) (hbi n).1 (hbi n).2
    (hsubE n) hw.measurable_mk
  have hunion (y : W) : (∑' x : ↥((⋃ n, f n '' B n) ∩ g ⁻¹' {y}), w' x) = ∑' n, ∑' x : ↥((f n '' B
    n) ∩ g ⁻¹' {y}), w' x := by
    rw [iUnion_inter, _root_.tsum_iUnion]
    exact fun _ _ _ _ hij => (hdisj hij).mono inter_subset_left inter_subset_left
  have hcov_w := hg.tsum_fiber_congr_ae_set (iUnion_subset hsubE) Subset.rfl hcover_ae w'
  refine ⟨((AEMeasurable.tsum fun n => (hp n).1).congr (hcov_w.mono fun y hy => (hunion
    y).symm.trans hy)).congr hw_ae.symm, ?_⟩
  rw [lintegral_congr_ae (hw.ae_eq_mk.mono fun x hx => congrArg (ofReal (J x) * ·) hx),
    setLIntegral_congr hcover_ae.symm, lintegral_iUnion hTm hdisj]
  simp_rw [fun n => (hp n).2]; rw [← lintegral_tsum fun n => (hp n).1]
  exact (lintegral_congr fun y => (hunion y).symm).trans
    ((lintegral_congr_ae hcov_w).trans (lintegral_congr_ae hw_ae.symm))
/-- Measurability of weighted fiber sums for `LocallyLipschitzOn`. -/
theorem aemeasurable_tsum_fiber {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    AEMeasurable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), w x) μHE[k] :=
  (hg.aemeasurable_and_lintegral_tsum_fiber hE hEm hw).1
/-- Weighted tangential area formula with multiplicity for `LocallyLipschitzOn`. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum {w : V → ℝ≥0∞}
    (hw : AEMeasurable w (μHE[k].restrict E)) :
    (∫⁻ x in E, ofReal (J x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] :=
  (hg.aemeasurable_and_lintegral_tsum_fiber hE hEm hw).2
/-- Measurability of extended fiber cardinalities for `LocallyLipschitzOn`. -/
theorem aemeasurable_encard_fiber : AEMeasurable (fun y => ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞)) μHE[k]
    := by simpa only [ENNReal.tsum_set_one] using
      hg.aemeasurable_tsum_fiber hE hEm (w := fun _ => 1) aemeasurable_const
/-- Unweighted tangential area formula with multiplicity for `LocallyLipschitzOn`. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard : (∫⁻ x in E, ofReal (J x) ∂μHE[k]) = ∫⁻ y,
    ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] := by simpa only [mul_one, ENNReal.tsum_set_one] using
  hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm (w := fun _ => 1) aemeasurable_const
/-- Weighted injective tangential area formula for `LocallyLipschitzOn`. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hinj : InjOn g E) (w : W → ℝ≥0∞) : (∫⁻
    y in g '' E, w y ∂μHE[k]) = ∫⁻ x in E, ofReal (J x) * w (g x) ∂μHE[k] := by
  obtain ⟨B, f, gExt, _, _, _, hBm, hTm, hbi, hgExt, hdisj, hsubE, hcover_ae⟩ :=
    hg.exists_disjoint_measurable_bilipschitz_extension_cover hE hEm
  have himg_ae : g '' E =ᵐ[μHE[k]] g '' (⋃ n, f n '' B n) := by
    nth_rw 1 [(union_sdiff_cancel (iUnion_subset hsubE)).symm]; rw [image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr
      (hg.euclideanHausdorffMeasure_image_eq_zero_of_subset sdiff_subset k
        (ae_eq_set.mp hcover_ae).2))
  have hinj_gf (n : ℕ) : InjOn (gExt n ∘ f n) (B n) := fun u₁ hu₁ u₂ hu₂ h =>
    injOn_iff_injective.mpr (hbi n).2.injective hu₁ hu₂ (hinj (hsubE n (mem_image_of_mem _ hu₁))
      (hsubE n (mem_image_of_mem _ hu₂)) (((hgExt n).2 (mem_image_of_mem _ hu₁)).trans
        (h.trans ((hgExt n).2 (mem_image_of_mem _ hu₂)).symm)))
  have himg_eq (n : ℕ) : g '' (f n '' B n) = (gExt n ∘ f n) '' B n :=
    (image_comp g (f n) (B n)).symm ▸ image_congr fun u hu => (hgExt n).2 (mem_image_of_mem _ hu)
  rw [setLIntegral_congr himg_ae, image_iUnion, lintegral_iUnion (fun n => himg_eq n ▸ (hBm
    n).image_of_continuousOn_injOn ((hgExt n).1.comp (hbi n).1).continuous.continuousOn (hinj_gf n))
    (fun i j hij => Disjoint.image (hdisj hij) hinj (hsubE i) (hsubE j)),
    setLIntegral_congr hcover_ae.symm, lintegral_iUnion hTm hdisj]
  refine tsum_congr fun n => ?_
  rw [himg_eq n, lintegral_patch_tangentialJacobian_mul hEm (hgExt n).1 (hgExt n).2 (hBm n) (hbi
    n).1 (hbi n).2 (hsubE n) (fun x => w (g x))]
  exact (by simpa only [finrank_euclideanSpace_fin, comp_apply] using ((hgExt n).1.comp (hbi
    n).1).lintegral_image_eq_lintegral_normDet_fderiv_mul (hBm n) (hinj_gf n) w : _ = ∫⁻ u in B n,
    ofReal (fderiv ℝ (gExt n ∘ f n) u).normDet * w (gExt n (f n u))).trans (setLIntegral_congr_fun
    (hBm n) fun u huB => by simp only [(hgExt n).2 (mem_image_of_mem (f n) huB)])
/-- Injective tangential area formula for `LocallyLipschitzOn`. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image (hinj : InjOn g E) : (∫⁻ x
    in E, ofReal (J x) ∂μHE[k]) = μHE[k] (g '' E) := by
  simpa using (hg.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj 1).symm
/-- Null-image theorem when `tangentialJacobian` vanishes `μHE[k]`-a.e. on `E`. -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero (hzero : ∀ᵐ x
    ∂μHE[k], x ∈ E → J x = 0) : μHE[k] (g '' E) = 0 := by
  refine measure_mono_null ?_
    (ae_iff.mp ((lintegral_eq_zero_iff' (hg.aemeasurable_encard_fiber hE hEm)).mp ?_))
  · rintro _ ⟨x, hxE, rfl⟩ h0
    exact notMem_empty x ((by simpa using h0 : E ∩ g ⁻¹' {g x} = ∅) ▸ ⟨hxE, rfl⟩)
  rw [← hg.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm]
  exact (lintegral_congr_ae ((ae_restrict_iff'₀ hEm).mpr <|
    hzero.mono fun _ hx hxE => by simp [hx hxE])).trans lintegral_zero
/-- Rank-deficient tangential derivatives have `μHE[k]`-null images (`LocallyLipschitzOn`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt (hrank : ∀ᵐ x
    ∂μHE[k], x ∈ E → finrank ℝ (LinearMap.range (D x).toLinearMap) < k) : μHE[k] (g '' E) = 0 :=
  hg.euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero hE hEm
    (hrank.mono fun _ hlt hxE => tangentialJacobian_eq_zero_of_finrank_range_lt (hlt hxE))
/-- Finiteness of the `μHE[k]` integral of extended weighted fiber sums. -/
theorem lintegral_tsum_fiber_ne_top {w : V → ℝ≥0} (hw : AEMeasurable w (μHE[k].restrict E)) (hint :
    IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) :
    (∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ≥0∞) ∂μHE[k]) ≠ ∞ := by
  rw [← hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw.coe_nnreal_ennreal]
  simpa only [ENNReal.ofReal_mul (tangentialJacobian_nonneg _ _ _ _), ENNReal.ofReal_coe_nnreal]
    using hint.lintegral_lt_top.ne
/-- Almost-everywhere summability of real weights on fibers. -/
theorem ae_summable_fiber {w : V → ℝ≥0} (hw : AEMeasurable w (μHE[k].restrict E)) (hint :
    IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) :
    ∀ᵐ y ∂μHE[k], Summable fun x : ↥(E ∩ g ⁻¹' {y}) => (w x : ℝ) :=
  (ae_lt_top' (hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal)
    (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint)).mono fun _ hy =>
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hy.ne
/-- Integrability of the real weighted fiber sum on `W`. -/
theorem integrable_tsum_fiber {w : V → ℝ≥0} (hw : AEMeasurable w (μHE[k].restrict E)) (hint :
    IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) :
    Integrable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ)) μHE[k] :=
  (integrable_toReal_of_lintegral_ne_top (hg.aemeasurable_tsum_fiber hE hEm
    hw.coe_nnreal_ennreal) (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint)).congr <|
    .of_forall fun y => by
      simpa only [ENNReal.coe_toReal] using
        ENNReal.tsum_toReal_eq (f := fun x : ↥(E ∩ g ⁻¹' {y}) => (w x : ℝ≥0∞))
          fun _ => ENNReal.coe_ne_top
/-- Real weighted tangential area formula with multiplicity for `LocallyLipschitzOn`. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum {w : V → ℝ≥0}
    (hw : AEMeasurable w (μHE[k].restrict E)) (hint : IntegrableOn (fun x => J x * (w x : ℝ)) E
    μHE[k]) :
    (∫ x in E, J x * (w x : ℝ) ∂μHE[k]) = ∫ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ) ∂μHE[k] := by
  have hA : AEMeasurable (fun x => ofReal (J x) * (w x : ℝ≥0∞)) (μHE[k].restrict E) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (hg.aemeasurable_tangentialJacobian hE hEm)).mul hw.coe_nnreal_ennreal
  have hG := hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal
  rw [← (integral_toReal hA (.of_forall fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.coe_lt_top)).symm.trans (integral_congr_ae (.of_forall fun _ => by
      simp [ENNReal.toReal_ofReal (tangentialJacobian_nonneg _ _ _ _)])),
    hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw.coe_nnreal_ennreal,
    ← integral_toReal hG (ae_lt_top' hG (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint))]
  exact integral_congr_ae <| .of_forall fun y => by
    simpa only [ENNReal.coe_toReal] using
      ENNReal.tsum_toReal_eq (f := fun x : ↥(E ∩ g ⁻¹' {y}) => (w x : ℝ≥0∞))
        fun _ => ENNReal.coe_ne_top
/-- Almost-everywhere finiteness of fibers when `tangentialJacobian` is integrable on `E`. -/
theorem ae_finite_fiber (hint : IntegrableOn (J) E μHE[k]) : ∀ᵐ y ∂μHE[k], (E ∩ g ⁻¹' {y}).Finite :=
  (hg.ae_summable_fiber hE hEm (w := fun _ => 1) aemeasurable_const (by simpa using hint)).mono
    fun _ hy => Set.finite_coe_iff.mp (Finite.of_summable_const zero_lt_one hy)
/-- Integrability of `ncard` of fibers when `tangentialJacobian` is integrable on `E`. -/
theorem integrable_ncard_fiber (hint : IntegrableOn (J) E μHE[k]) : Integrable (fun y => ((E ∩ g ⁻¹'
    {y}).ncard : ℝ)) μHE[k] := (hg.integrable_tsum_fiber hE hEm (w := fun _ => 1) aemeasurable_const
    (by simpa using hint)).congr ((hg.ae_finite_fiber hE hEm hint).mono fun y hy => by
      let _ : Finite ↥(E ∩ g ⁻¹' {y}) := Set.finite_coe_iff.mpr hy; simp)
/-- Real unweighted tangential area formula for `LocallyLipschitzOn`. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hint : IntegrableOn (J) E μHE[k]) : (∫ x in
    E, J x ∂μHE[k]) = ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] := by
  refine (?_ : _ = ∫ y, ∑' _ : ↥(E ∩ g ⁻¹' {y}), (1 : ℝ) ∂μHE[k]).trans (integral_congr_ae <|
    (hg.ae_finite_fiber hE hEm hint).mono fun y hy => by
      let _ : Finite ↥(E ∩ g ⁻¹' {y}) := Set.finite_coe_iff.mpr hy; simp)
  simpa using hg.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm (w := fun _ => 1)
    aemeasurable_const (by simpa using hint)
end LocallyLipschitzOn
end RectifiableAreaFormula
