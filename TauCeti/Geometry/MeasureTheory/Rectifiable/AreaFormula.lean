/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Rademacher
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import TauCeti.MeasureTheory.Function.AreaFormula.Real
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# The tangential area formula on countably rectifiable sets

Tangential area formulas and rank-deficiency null-image theorems (Federer 3.2.20).
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff
namespace TauCeti
private lemma tsum_fiber_image_of_injOn {U V W : Type*} {f : U → V} {B : Set U} (hinj : InjOn f B)
    (g : V → W) (w : V → ℝ≥0∞) (y : W) : (∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) = ∑' u : ↥(B ∩ (g ∘
    f) ⁻¹' {y}), w (f u) := by
  refine ((Equiv.ofBijective (fun u : ↥(B ∩ (g ∘ f) ⁻¹' {y}) => (⟨f u.1, mem_image_of_mem f u.2.1,
    u.2.2⟩ : ↥((f '' B) ∩ g ⁻¹' {y}))) ⟨?_, ?_⟩).tsum_eq (fun x => w x.1)).symm
  · exact fun u₁ u₂ h => Subtype.ext (hinj u₁.2.1 u₂.2.1 (congrArg Subtype.val h))
  · rintro ⟨_, ⟨u, huB, rfl⟩, hgx⟩; exact ⟨⟨u, huB, hgx⟩, rfl⟩
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
  have hlhs : (∫⁻ x in f '' B, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) = ∫⁻ u in
    B, ENNReal.ofReal (fderiv ℝ f u).normDet * (ENNReal.ofReal (tangentialJacobian k E g (f u)) * w
    (f u)) := by
    simpa only [U, finrank_euclideanSpace_fin] using
      hf_lip.lintegral_image_eq_lintegral_normDet_fderiv_mul hBm (injOn_iff_injective.mpr
      hf_anti.injective) _
  refine hlhs.trans (setLIntegral_congr_fun_ae hBm ?_)
  filter_upwards [ae_regular_and_density_on_patch hEm hBm hf_lip hf_anti, (hgExt_lip.comp
    hf_lip).ae_differentiableAt] with u hreg hgf_diff huB
  obtain ⟨hf_diff, hinj_df, hdens, hdiff⟩ := hreg huB
  have hgf_w : HasFDerivWithinAt (g ∘ f) (fderiv ℝ (gExt ∘ f) u) B u :=
    hgf_diff.hasFDerivAt.hasFDerivWithinAt.congr (fun v hv => hgExt_eq (mem_image_of_mem f hv))
    (hgExt_eq (mem_image_of_mem f huB))
  have hdiff' : Tendsto (fun r => μHE[finrank ℝ U] ((E \ f '' B) ∩ closedBall (f u) r) / volume
    (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [U, finrank_euclideanSpace_fin, ← volume_closedBall_eq_euclidean (0 : EuclideanSpace
      ℝ (Fin k))] using hdiff
  have hmul : tangentialJacobian k E g (f u) * (fderiv ℝ f u).normDet = (fderiv ℝ (gExt ∘ f)
    u).normDet := by
    simpa only [U, finrank_euclideanSpace_fin] using
      hf_diff.hasFDerivAt.hasFDerivWithinAt.tangentialJacobian_mul_normDet hinj_df hf_anti huB hsub
      hdens hdiff' hgf_w
  rw [← mul_assoc, mul_comm (ENNReal.ofReal (fderiv ℝ f u).normDet), ← ENNReal.ofReal_mul
    (tangentialJacobian_nonneg _ _ _ _), hmul]
private lemma patch_area_formula {w : V → ℝ≥0∞} (hw : Measurable w) : AEMeasurable (fun y => ∑' x :
    ↥((f '' B) ∩ g ⁻¹' {y}), w x) μHE[k] ∧ (∫⁻ x in f '' B, ENNReal.ofReal (tangentialJacobian k E g
    x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
  have htsum_eq (y : W) : (∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) = ∑' u : ↥(B ∩ (gExt ∘ f) ⁻¹' {y}),
    w (f u) := (tsum_fiber_image_of_injOn (injOn_iff_injective.mpr hf_anti.injective) g w y).trans
    <| tsum_congr_set_coe (fun u => w (f u)) <| Set.ext fun u => and_congr_right fun huB => by
        simp only [mem_preimage, mem_singleton_iff, comp_apply, hgExt_eq (mem_image_of_mem f huB)]
  refine ⟨?_, (lintegral_patch_tangentialJacobian_mul hEm hgExt_lip hgExt_eq hBm hf_lip hf_anti hsub
    w).trans ?_⟩
  · simp_rw [htsum_eq]; simpa only [finrank_euclideanSpace_fin, comp_apply] using
      (hgExt_lip.comp hf_lip).aemeasurable_tsum_fiber hBm.nullMeasurableSet
        (hw.comp hf_lip.continuous.measurable)
  · simp_rw [htsum_eq]; simpa only [finrank_euclideanSpace_fin, comp_apply] using
      (hgExt_lip.comp hf_lip).lintegral_normDet_fderiv_mul_eq_lintegral_tsum hBm.nullMeasurableSet
        (hw.comp hf_lip.continuous.measurable)
end Patch
end TauCeti
section NullImage
variable {X Y : Type*} [EMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace
    X] [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-- A map locally Lipschitz on `s` maps every `μHE[d]`-null subset `t ⊆ s` to a null set. -/
theorem LocallyLipschitzOn.euclideanHausdorffMeasure_image_eq_zero_of_subset {s t : Set X} {f : X →
    Y} (hf : LocallyLipschitzOn s f) (hts : t ⊆ s) (d : ℕ) (ht0 : μHE[d] t = 0) : μHE[d] (f '' t) =
    0 := by
  obtain ⟨U, K, _, hcov, hLip⟩ := hf.exists_open_cover_lipschitzOnWith
  rw [show t = ⋃ n, t ∩ U n by rw [← inter_iUnion, inter_eq_self_of_subset_left (hts.trans hcov)],
    image_iUnion]
  refine measure_iUnion_null fun n => nonpos_iff_eq_zero.mp <| (((hLip n).mono
    (inter_subset_inter_left _ hts)).euclideanHausdorffMeasure_image_le d).trans_eq
    (by rw [measure_mono_null inter_subset_left ht0, mul_zero])
/-- Null-set congruence of weighted fiber sums in the domain subset. -/
theorem LocallyLipschitzOn.tsum_fiber_congr_ae_set {E s t : Set X} {f : X → Y} (hf :
    LocallyLipschitzOn E f) (hs : s ⊆ E) (ht : t ⊆ E) {d : ℕ} (hst : s =ᵐ[μHE[d]] t) (w : X → ℝ≥0∞)
    : (fun y => ∑' x : ↥(s ∩ f ⁻¹' {y}), w x) =ᵐ[μHE[d]] fun y => ∑' x : ↥(t ∩ f ⁻¹' {y}), w x := by
  have hnull : μHE[d] (f '' (s ∆ t)) = 0 := hf.euclideanHausdorffMeasure_image_eq_zero_of_subset
    (symmDiff_subset_union.trans (union_subset hs ht)) d (measure_symmDiff_eq_zero_iff.mpr hst)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  refine tsum_congr_set_coe w (Set.ext fun x => ?_)
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  exact ⟨fun ⟨hxs, hfx⟩ => ⟨by_contra fun hxt => hy ⟨x, Or.inl ⟨hxs, hxt⟩, hfx⟩, hfx⟩, fun ⟨hxt,
    hfx⟩ => ⟨by_contra fun hxs => hy ⟨x, Or.inr ⟨hxt, hxs⟩, hfx⟩, hfx⟩⟩
/-- Almost-everywhere congruence of weighted fiber sums in the weight function. -/
theorem LocallyLipschitzOn.tsum_fiber_congr_ae_fun {E : Set X} {f : X → Y} (hf : LocallyLipschitzOn
    E f) {d : ℕ} {w₁ w₂ : X → ℝ≥0∞} (hw : w₁ =ᵐ[μHE[d].restrict E] w₂) : (fun y => ∑' x : ↥(E ∩ f
    ⁻¹' {y}), w₁ x) =ᵐ[μHE[d]] fun y => ∑' x : ↥(E ∩ f ⁻¹' {y}), w₂ x := by
  have hN0 : μHE[d] ({x | w₁ x ≠ w₂ x} ∩ E) = 0 := nonpos_iff_eq_zero.mp ((le_restrict_apply E {x |
    w₁ x ≠ w₂ x}).trans_eq (ae_iff.mp hw))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (hf.euclideanHausdorffMeasure_image_eq_zero_of_subset inter_subset_right d hN0)] with y hy
  exact tsum_congr fun x => not_not.mp fun hne => hy ⟨x.1, ⟨hne, x.2.1⟩, x.2.2⟩
end NullImage
section RectifiableAreaFormula
open TauCeti
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] {k : ℕ} {E : Set V} {g : V → W}
local notation "J" => tangentialJacobian k E g
local notation "D" => tangentialFDeriv k E g
local notation "F[" y "]" => Set.Elem (min E (Set.preimage g (singleton y)))
local notation "ofReal" => ENNReal.ofReal
namespace LocallyLipschitzOn
variable (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E
    μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
private lemma aemeasurable_and_lintegral_tsum_fiber {w : V → ℝ≥0∞} (hw : AEMeasurable w
    (μHE[k].restrict E)) : AEMeasurable (fun y => ∑' x : F[y], w x) μHE[k] ∧ (∫⁻ x in E, ofReal (J
    x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : F[y], w x ∂μHE[k] := by
  let w' := hw.mk w; have hw_ae := hg.tsum_fiber_congr_ae_fun hw.ae_eq_mk
  obtain ⟨B, f, gExt, _, _, _, hBm, hTm, hbi, hgExt, hdisj, hsubE, hcover_ae⟩ :=
    hg.exists_disjoint_measurable_bilipschitz_extension_cover hE hEm
  have hp (n : ℕ) := patch_area_formula hEm (hgExt n).1 (hgExt n).2 (hBm n) (hbi n).1 (hbi n).2
    ((subset_iUnion (fun m => f m '' B m) n).trans hsubE) hw.measurable_mk
  have hunion (y : W) : (∑' x : ↥((⋃ n, f n '' B n) ∩ g ⁻¹' {y}), w' x) = ∑' n, ∑' x : ↥((f n '' B
    n) ∩ g ⁻¹' {y}), w' x := by
    rw [iUnion_inter, _root_.tsum_iUnion]
    exact fun i _ j _ hij => (hdisj hij).mono inter_subset_left inter_subset_left
  have hcov_w := hg.tsum_fiber_congr_ae_set hsubE Subset.rfl hcover_ae w'
  refine ⟨((AEMeasurable.tsum fun n => (hp n).1).congr (hcov_w.mono fun y hy => (hunion
    y).symm.trans hy)).congr hw_ae.symm, ?_⟩
  rw [lintegral_congr_ae (hw.ae_eq_mk.mono fun x hx => congrArg (ofReal (J x) * ·) hx),
    setLIntegral_congr hcover_ae.symm, lintegral_iUnion hTm hdisj]
  simp_rw [fun n => (hp n).2]; rw [← lintegral_tsum fun n => (hp n).1]
  exact (lintegral_congr fun y => (hunion y).symm).trans ((lintegral_congr_ae hcov_w).trans
    (lintegral_congr_ae hw_ae.symm))
/-- Measurability of weighted fiber sums for `LocallyLipschitzOn`. -/
theorem aemeasurable_tsum_fiber {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    AEMeasurable (fun y => ∑' x : F[y], w x) μHE[k] := (hg.aemeasurable_and_lintegral_tsum_fiber hE
    hEm hw).1
/-- Weighted tangential area formula with multiplicity for `LocallyLipschitzOn`. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum {w : V → ℝ≥0∞} (hw : AEMeasurable w
    (μHE[k].restrict E)) : (∫⁻ x in E, ofReal (J x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : F[y], w x ∂μHE[k]
    := (hg.aemeasurable_and_lintegral_tsum_fiber hE hEm hw).2
/-- Measurability of extended fiber cardinalities for `LocallyLipschitzOn`. -/
theorem aemeasurable_encard_fiber : AEMeasurable (fun y => ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞)) μHE[k]
    := by
  simpa only [ENNReal.tsum_set_one] using hg.aemeasurable_tsum_fiber hE hEm (w := fun _ => 1)
    aemeasurable_const
/-- Unweighted tangential area formula with multiplicity for `LocallyLipschitzOn`. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard : (∫⁻ x in E, ofReal (J x) ∂μHE[k]) = ∫⁻ y,
    ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] := by
  simpa only [mul_one, ENNReal.tsum_set_one] using
    hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm (w := fun _ => 1)
    aemeasurable_const
/-- Weighted injective tangential area formula for `LocallyLipschitzOn`. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hinj : InjOn g E) (w : W → ℝ≥0∞) : (∫⁻
    y in g '' E, w y ∂μHE[k]) = ∫⁻ x in E, ofReal (J x) * w (g x) ∂μHE[k] := by
  obtain ⟨B, f, gExt, _, _, _, hBm, hTm, hbi, hgExt, hdisj, hsubE, hcover_ae⟩ :=
    hg.exists_disjoint_measurable_bilipschitz_extension_cover hE hEm
  have hdiff0 : μHE[k] (E \ ⋃ n, f n '' B n) = 0 := measure_mono_null
    (fun _ ⟨hxE, hxU⟩ => Or.inr ⟨hxE, hxU⟩) (measure_symmDiff_eq_zero_iff.mpr hcover_ae)
  have himg_ae : g '' E =ᵐ[μHE[k]] g '' (⋃ n, f n '' B n) := by
    nth_rw 1 [(union_sdiff_cancel hsubE).symm]; rw [image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr
      (hg.euclideanHausdorffMeasure_image_eq_zero_of_subset sdiff_subset k hdiff0))
  have hsub_n (n : ℕ) : f n '' B n ⊆ E := (subset_iUnion (fun m => f m '' B m) n).trans hsubE
  have hinj_gf (n : ℕ) : InjOn (gExt n ∘ f n) (B n) := fun u₁ hu₁ u₂ hu₂ h => by
    have h' : g (f n u₁) = g (f n u₂) := by
      simpa only [comp_apply, ← (hgExt n).2 (mem_image_of_mem (f n) hu₁), ← (hgExt n).2
        (mem_image_of_mem (f n) hu₂)] using h
    exact injOn_iff_injective.mpr (hbi n).2.injective hu₁ hu₂ (hinj (hsub_n n (mem_image_of_mem (f
      n) hu₁)) (hsub_n n (mem_image_of_mem (f n) hu₂)) h')
  have himg_eq (n : ℕ) : g '' (f n '' B n) = (gExt n ∘ f n) '' B n := by
    rw [← image_comp]; exact image_congr fun u hu => (hgExt n).2 (mem_image_of_mem (f n) hu)
  have hIm (n : ℕ) : MeasurableSet (g '' (f n '' B n)) := himg_eq n ▸ (hBm
    n).image_of_continuousOn_injOn ((hgExt n).1.comp (hbi n).1).continuous.continuousOn (hinj_gf n)
  rw [setLIntegral_congr himg_ae, image_iUnion, lintegral_iUnion hIm (fun i j hij => Disjoint.image
    (hdisj hij) hinj (hsub_n i) (hsub_n j)), setLIntegral_congr hcover_ae.symm, lintegral_iUnion hTm
    hdisj]
  refine tsum_congr fun n => ?_
  rw [himg_eq n, lintegral_patch_tangentialJacobian_mul hEm (hgExt n).1 (hgExt n).2 (hBm n) (hbi
    n).1 (hbi n).2 (hsub_n n) (fun x => w (g x))]
  refine (?_ : _ = ∫⁻ u in B n, ofReal (fderiv ℝ (gExt n ∘ f n) u).normDet * w (gExt n (f n
    u))).trans (setLIntegral_congr_fun (hBm n) fun u huB => by
      simp only [(hgExt n).2 (mem_image_of_mem (f n) huB)])
  simpa only [finrank_euclideanSpace_fin, comp_apply] using ((hgExt n).1.comp (hbi
    n).1).lintegral_image_eq_lintegral_normDet_fderiv_mul (hBm n) (hinj_gf n) w
/-- Injective tangential area formula for `LocallyLipschitzOn`. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image (hinj : InjOn g E) : (∫⁻ x
    in E, ofReal (J x) ∂μHE[k]) = μHE[k] (g '' E) := by
  simpa using (hg.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj 1).symm
/-- Null-image theorem when `tangentialJacobian` vanishes `μHE[k]`-a.e. on `E`. -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero (hzero : ∀ᵐ x ∂μHE[k],
    x ∈ E → J x = 0) : μHE[k] (g '' E) = 0 := by
  have hlint : (∫⁻ y, ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k]) = 0 := by
    rw [← hg.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm]
    refine (lintegral_congr_ae ((ae_restrict_iff'₀ hEm).mpr ?_)).trans lintegral_zero
    filter_upwards [hzero] with x hx hxE; simp [hx hxE]
  refine measure_mono_null ?_ (ae_iff.mp ((lintegral_eq_zero_iff' (hg.aemeasurable_encard_fiber hE
    hEm)).mp hlint))
  rintro _ ⟨x, hxE, rfl⟩ h0
  exact notMem_empty x ((by simpa using h0 : E ∩ g ⁻¹' {g x} = ∅) ▸ ⟨hxE, rfl⟩)
/-- Rank-deficient tangential derivatives have `μHE[k]`-null images (`LocallyLipschitzOn`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt (hrank : ∀ᵐ x
    ∂μHE[k], x ∈ E → finrank ℝ (LinearMap.range (D x).toLinearMap) < k) : μHE[k] (g '' E) = 0 :=
    hg.euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero hE hEm (hrank.mono fun
    _ hlt hxE => tangentialJacobian_eq_zero_of_finrank_range_lt (hlt hxE))
/-- Finiteness of the `μHE[k]` integral of extended weighted fiber sums. -/
theorem lintegral_tsum_fiber_ne_top {w : V → ℝ≥0} (hw : AEMeasurable w (μHE[k].restrict E)) (hint :
    IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) : (∫⁻ y, ∑' x : F[y], (w x : ℝ≥0∞) ∂μHE[k]) ≠
    ∞ := by
  rw [← hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw.coe_nnreal_ennreal]
  simpa only [ENNReal.ofReal_mul (tangentialJacobian_nonneg _ _ _ _), ENNReal.ofReal_coe_nnreal]
    using hint.lintegral_lt_top.ne
/-- Almost-everywhere summability of real weights on fibers. -/
theorem ae_summable_fiber {w : V → ℝ≥0} (hw : AEMeasurable w (μHE[k].restrict E)) (hint :
    IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) : ∀ᵐ y ∂μHE[k], Summable fun x : F[y] => (w x
    : ℝ) := (ae_lt_top' (hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal)
    (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint)).mono fun _ hy =>
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hy.ne
/-- Integrability of the real weighted fiber sum on `W`. -/
theorem integrable_tsum_fiber {w : V → ℝ≥0} (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) :
    Integrable (fun y => ∑' x : F[y], (w x : ℝ)) μHE[k] :=
  (integrable_toReal_of_lintegral_ne_top (hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal)
    (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint)).congr <| .of_forall fun y => by
      simpa only [ENNReal.coe_toReal] using ENNReal.tsum_toReal_eq
        (f := fun x : F[y] => (w x : ℝ≥0∞)) fun _ => ENNReal.coe_ne_top
/-- Real weighted tangential area formula with multiplicity for `LocallyLipschitzOn`. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum {w : V → ℝ≥0} (hw : AEMeasurable w
    (μHE[k].restrict E)) (hint : IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) : (∫ x in E, J x
    * (w x : ℝ) ∂μHE[k]) = ∫ y, ∑' x : F[y], (w x : ℝ) ∂μHE[k] := by
  let A : V → ℝ≥0∞ := fun x => ofReal (J x) * (w x : ℝ≥0∞)
  let G : W → ℝ≥0∞ := fun y => ∑' x : F[y], (w x : ℝ≥0∞)
  have hA : AEMeasurable A (μHE[k].restrict E) := (ENNReal.measurable_ofReal.comp_aemeasurable
    (hg.aemeasurable_tangentialJacobian hE hEm)).mul hw.coe_nnreal_ennreal
  have hG : AEMeasurable G μHE[k] := hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal
  have h1 : (∫ x in E, J x * (w x : ℝ) ∂μHE[k]) = (∫⁻ x in E, A x ∂μHE[k]).toReal := by
    rw [← integral_toReal hA (.of_forall fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.coe_lt_top)]
    exact integral_congr_ae (.of_forall fun x => by simp only [A, ENNReal.toReal_mul,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal (tangentialJacobian_nonneg _ _ _ _)])
  have h2 := congrArg ENNReal.toReal
    (hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw.coe_nnreal_ennreal)
  have h3 :=
    (integral_toReal hG (ae_lt_top' hG (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint))).symm
  exact (h1.trans (h2.trans h3)).trans <| integral_congr_ae <| .of_forall fun y => by
    simpa only [G, ENNReal.coe_toReal] using
      ENNReal.tsum_toReal_eq (f := fun x : F[y] => (w x : ℝ≥0∞)) fun _ => ENNReal.coe_ne_top
/-- Almost-everywhere finiteness of fibers when `tangentialJacobian` is integrable on `E`. -/
theorem ae_finite_fiber (hint : IntegrableOn (J) E μHE[k]) :
    ∀ᵐ y ∂μHE[k], (E ∩ g ⁻¹' {y}).Finite :=
  (hg.ae_summable_fiber hE hEm (w := fun _ => 1) aemeasurable_const (by simpa using hint)).mono
    fun _ hy => Set.finite_coe_iff.mp (Finite.of_summable_const zero_lt_one hy)
/-- Integrability of `ncard` of fibers when `tangentialJacobian` is integrable on `E`. -/
theorem integrable_ncard_fiber (hint : IntegrableOn (J) E μHE[k]) : Integrable (fun y => ((E ∩ g ⁻¹'
    {y}).ncard : ℝ)) μHE[k] := by
  refine (hg.integrable_tsum_fiber hE hEm (w := fun _ => 1) aemeasurable_const
    (by simpa using hint)).congr ?_
  filter_upwards [hg.ae_finite_fiber hE hEm hint] with y hy
  let _ : Finite F[y] := Set.finite_coe_iff.mpr hy; simp
/-- Real unweighted tangential area formula for `LocallyLipschitzOn`. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hint : IntegrableOn (J) E μHE[k]) : (∫ x in
    E, J x ∂μHE[k]) = ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] := by
  have h := hg.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm (w := fun _ => 1)
    aemeasurable_const (by simpa using hint)
  refine (by simpa using h : _ = ∫ y, ∑' _ : F[y], (1 : ℝ) ∂μHE[k]).trans (integral_congr_ae ?_)
  filter_upwards [hg.ae_finite_fiber hE hEm hint] with y hy
  let _ : Finite F[y] := Set.finite_coe_iff.mpr hy; simp
end LocallyLipschitzOn
namespace LipschitzOnWith
variable {K : ℝ≥0} (hg : LipschitzOnWith K g E) (hE : CountablyRectifiable k E) (hEm :
    NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
/-- Measurability of weighted fiber sums for `LipschitzOnWith`. -/
theorem aemeasurable_tsum_fiber {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    AEMeasurable (fun y => ∑' x : F[y], w x) μHE[k] := hg.locallyLipschitzOn.aemeasurable_tsum_fiber
    hE hEm hw
/-- Weighted tangential area formula with multiplicity for `LipschitzOnWith`. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum {w : V → ℝ≥0∞} (hw : AEMeasurable w
    (μHE[k].restrict E)) : (∫⁻ x in E, ofReal (J x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : F[y], w x ∂μHE[k]
    := hg.locallyLipschitzOn.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw
/-- Weighted injective tangential area formula for `LipschitzOnWith`. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hinj : InjOn g E) (w : W → ℝ≥0∞) : (∫⁻
    y in g '' E, w y ∂μHE[k]) = ∫⁻ x in E, ofReal (J x) * w (g x) ∂μHE[k] :=
    hg.locallyLipschitzOn.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj w
/-- Unweighted tangential area formula with multiplicity for `LipschitzOnWith`. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard : (∫⁻ x in E, ofReal (J x) ∂μHE[k]) = ∫⁻ y,
    ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] :=
    hg.locallyLipschitzOn.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm
/-- Injective tangential area formula for `LipschitzOnWith`. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image (hinj : InjOn g E) : (∫⁻ x
    in E, ofReal (J x) ∂μHE[k]) = μHE[k] (g '' E) :=
    hg.locallyLipschitzOn.lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image hE hEm
    hinj
/-- Rank-deficient tangential derivatives have null images (`LipschitzOnWith`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt (hrank : ∀ᵐ x
    ∂μHE[k], x ∈ E → finrank ℝ (LinearMap.range (D x).toLinearMap) < k) : μHE[k] (g '' E) = 0 :=
    hg.locallyLipschitzOn
    |>.euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt hE hEm hrank
/-- Real weighted tangential area formula with multiplicity for `LipschitzOnWith`. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum {w : V → ℝ≥0} (hw : AEMeasurable w
    (μHE[k].restrict E)) (hint : IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) : (∫ x in E, J x
    * (w x : ℝ) ∂μHE[k]) = ∫ y, ∑' x : F[y], (w x : ℝ) ∂μHE[k] :=
    hg.locallyLipschitzOn.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm hw hint
/-- Real unweighted tangential area formula for `LipschitzOnWith`. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hint : IntegrableOn (J) E μHE[k]) : (∫ x in
    E, J x ∂μHE[k]) = ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] :=
    hg.locallyLipschitzOn.integral_tangentialJacobian_eq_integral_ncard hE hEm hint
end LipschitzOnWith
namespace LipschitzWith
variable {K : ℝ≥0} (hg : LipschitzWith K g) (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet
    E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
/-- Weighted tangential area formula with multiplicity for `K`-Lipschitz maps. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum {w : V → ℝ≥0∞} (hw : AEMeasurable w
    (μHE[k].restrict E)) : (∫⁻ x in E, ofReal (J x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : F[y], w x ∂μHE[k]
    := hg.lipschitzOnWith.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw
/-- Unweighted tangential area formula with multiplicity for `K`-Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard : (∫⁻ x in E, ofReal (J x) ∂μHE[k]) = ∫⁻ y,
    ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] :=
    hg.lipschitzOnWith.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm
/-- Weighted injective tangential area formula for `K`-Lipschitz maps. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hinj : InjOn g E) (w : W → ℝ≥0∞) : (∫⁻
    y in g '' E, w y ∂μHE[k]) = ∫⁻ x in E, ofReal (J x) * w (g x) ∂μHE[k] :=
    hg.lipschitzOnWith.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj w
/-- Injective tangential area formula for `K`-Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image (hinj : InjOn g E) : (∫⁻ x
    in E, ofReal (J x) ∂μHE[k]) = μHE[k] (g '' E) :=
    hg.lipschitzOnWith.lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image hE hEm hinj
/-- Rank-deficient tangential derivatives have null images (`LipschitzWith`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt (hrank : ∀ᵐ x
    ∂μHE[k], x ∈ E → finrank ℝ (LinearMap.range (D x).toLinearMap) < k) : μHE[k] (g '' E) = 0 :=
    hg.lipschitzOnWith
    |>.euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt hE hEm hrank
/-- Real weighted tangential area formula with multiplicity for `K`-Lipschitz maps. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum {w : V → ℝ≥0} (hw : AEMeasurable w
    (μHE[k].restrict E)) (hint : IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) : (∫ x in E, J x
    * (w x : ℝ) ∂μHE[k]) = ∫ y, ∑' x : F[y], (w x : ℝ) ∂μHE[k] :=
    hg.lipschitzOnWith.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm hw hint
/-- Real unweighted tangential area formula for `K`-Lipschitz maps. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hint : IntegrableOn (J) E μHE[k]) : (∫ x in
    E, J x ∂μHE[k]) = ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] :=
    hg.lipschitzOnWith.integral_tangentialJacobian_eq_integral_ncard hE hEm hint
end LipschitzWith
namespace LocallyLipschitz
variable (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E
    μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
include hg hE hEm
/-- Weighted tangential area formula with multiplicity for locally Lipschitz maps. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum {w : V → ℝ≥0∞} (hw : AEMeasurable w
    (μHE[k].restrict E)) : (∫⁻ x in E, ofReal (J x) * w x ∂μHE[k]) = ∫⁻ y, ∑' x : F[y], w x ∂μHE[k]
    := hg.locallyLipschitzOn.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw
/-- Unweighted tangential area formula with multiplicity for locally Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard : (∫⁻ x in E, ofReal (J x) ∂μHE[k]) = ∫⁻ y,
    ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] :=
    hg.locallyLipschitzOn.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm
/-- Weighted injective tangential area formula for locally Lipschitz maps. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hinj : InjOn g E) (w : W → ℝ≥0∞) : (∫⁻
    y in g '' E, w y ∂μHE[k]) = ∫⁻ x in E, ofReal (J x) * w (g x) ∂μHE[k] :=
    hg.locallyLipschitzOn.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj w
/-- Injective tangential area formula for locally Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image (hinj : InjOn g E) : (∫⁻ x
    in E, ofReal (J x) ∂μHE[k]) = μHE[k] (g '' E) :=
    hg.locallyLipschitzOn.lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image hE hEm
      hinj
/-- Rank-deficient tangential derivatives have null images (`LocallyLipschitz`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt (hrank : ∀ᵐ x
    ∂μHE[k], x ∈ E → finrank ℝ (LinearMap.range (D x).toLinearMap) < k) : μHE[k] (g '' E) = 0 :=
    hg.locallyLipschitzOn
    |>.euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt hE hEm hrank
/-- Real weighted tangential area formula with multiplicity for locally Lipschitz maps. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum {w : V → ℝ≥0} (hw : AEMeasurable w
    (μHE[k].restrict E)) (hint : IntegrableOn (fun x => J x * (w x : ℝ)) E μHE[k]) : (∫ x in E, J x
    * (w x : ℝ) ∂μHE[k]) = ∫ y, ∑' x : F[y], (w x : ℝ) ∂μHE[k] :=
    hg.locallyLipschitzOn.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm hw hint
/-- Real unweighted tangential area formula for locally Lipschitz maps. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hint : IntegrableOn (J) E μHE[k]) : (∫ x in
    E, J x ∂μHE[k]) = ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] :=
    hg.locallyLipschitzOn.integral_tangentialJacobian_eq_integral_ncard hE hEm hint
end LocallyLipschitz
end RectifiableAreaFormula
