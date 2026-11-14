/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Rademacher
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import TauCeti.MeasureTheory.Function.AreaFormula.Real
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# The tangential area formula on countably rectifiable sets

For a map `g : V → W` between finite-dimensional real inner product spaces that is locally
Lipschitz on a null-measurable, countably `k`-rectifiable set `E ⊆ V` with locally finite `μHE[k]`
measure, integrating the `k`-dimensional tangential Jacobian `tangentialJacobian k E g` against an
`ℝ≥0∞`-valued `μHE[k].restrict E`-almost everywhere measurable weight `w` equals the `μHE[k]`
integral over `W` of the extended fiber sum `y ↦ ∑' x : ↥(E ∩ g ⁻¹' {y}), w x`. Infinite fibers
contribute `∞` where `w` is positive rather than defaulting to `0`.

The proof first treats `LipschitzOnWith K g E`: extending `g|_E` to a globally Lipschitz map via
`LipschitzOnWith.extend_finite_dimension` and covering `E` up to a `μHE[k]`-null set by pairwise
disjoint Borel bi-Lipschitz patches `f n '' B n ⊆ E` reduces each patch to the Euclidean area
formula with multiplicity on `B n ⊆ EuclideanSpace ℝ (Fin k)` via the parametrization identity
`HasFDerivWithinAt.tangentialJacobian_mul_normDet` and the injective Euclidean area formula for
`f n`. Disjointing a countable open cover (`LocallyLipschitzOn.exists_open_cover_lipschitzOnWith`)
and weighting by `disjointed` indicators extends both measurability of the fiber sum and the
weighted identity to `LocallyLipschitzOn E g`.

From the weighted formula we derive:
* the unweighted multiplicity formula (`lintegral_tangentialJacobian_eq_lintegral_encard`);
* the injective tangential area formula for arbitrary nonnegative weights without measurability of
  the target weight (`lintegral_image_eq_lintegral_tangentialJacobian_mul`) and for Hausdorff
  measure (`lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image`);
* the null-image theorem when `tangentialJacobian` vanishes almost everywhere or the tangential
  derivative has rank strictly less than `k`
  (`euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero`,
  `euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt`);
* real-valued integrable area formulas with multiplicity (`ae_summable_fiber`,
  `integrable_tsum_fiber`, `integral_tangentialJacobian_mul_eq_integral_tsum`, `ae_finite_fiber`,
  `integrable_ncard_fiber`, `integral_tangentialJacobian_eq_integral_ncard`), together with
  `LipschitzOnWith`, `LipschitzWith`, and `LocallyLipschitz` specializations.

## References

* H. Federer, *Geometric Measure Theory*, 3.2.20.
* L. Simon, *Lectures on Geometric Measure Theory*, §12 (the area formula on rectifiable sets).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 2.91.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology symmDiff

namespace TauCeti

/-- Bijection between the fiber of `g` over `y` inside an injective image `f '' B` and the fiber
of `g ∘ f` over `y` inside `B`. -/
private lemma tsum_fiber_image_of_injOn {U V W : Type*} {f : U → V} {B : Set U}
    (hinj : InjOn f B) (g : V → W) (w : V → ℝ≥0∞) (y : W) :
    (∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) = ∑' u : ↥(B ∩ (g ∘ f) ⁻¹' {y}), w (f u) := by
  have hbij : Bijective (fun u : ↥(B ∩ (g ∘ f) ⁻¹' {y}) =>
      (⟨f u.1, mem_image_of_mem f u.2.1, u.2.2⟩ : ↥((f '' B) ∩ g ⁻¹' {y}))) := by
    refine ⟨fun u₁ u₂ h => Subtype.ext (hinj u₁.2.1 u₂.2.1 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, ⟨u, huB, rfl⟩, hgx⟩
    exact ⟨⟨u, huB, hgx⟩, rfl⟩
  exact ((Equiv.ofBijective _ hbij).tsum_eq (fun x => w x.1)).symm

/-- Summing `D.indicator w` over `(E ∩ O) ∩ g ⁻¹' {y}` when `D ⊆ O` restricts the fiber sum to
`(E ∩ D) ∩ g ⁻¹' {y}`. -/
private lemma tsum_fiber_indicator_of_subset {V W : Type*} {E O D : Set V} (hDO : D ⊆ O)
    (g : V → W) (w : V → ℝ≥0∞) (y : W) :
    (∑' x : ↥((E ∩ O) ∩ g ⁻¹' {y}), D.indicator w x) =
      ∑' x : ↥((E ∩ D) ∩ g ⁻¹' {y}), w x := by
  let S := (E ∩ O) ∩ g ⁻¹' {y}
  let T : Set ↥S := {x | x.1 ∈ D}
  have hind : (fun x : ↥S => D.indicator w x.1) = T.indicator (fun x : ↥S => w x.1) := by
    ext x
    by_cases hx : x.1 ∈ D <;> simp [T, hx]
  rw [hind, ← tsum_subtype T (fun x : ↥S => w x.1)]
  let e : ↥T ≃ ↥((E ∩ D) ∩ g ⁻¹' {y}) :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2.1.1, x.2⟩, x.1.2.2⟩
      invFun := fun x => ⟨⟨x.1, ⟨x.2.1.1, hDO x.2.1.2⟩, x.2.2⟩, x.2.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.tsum_eq (fun x => w x.1)

end TauCeti

namespace LocallyLipschitzOn

open TauCeti

section NullImage

variable {X Y : Type*} [EMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A map locally Lipschitz on `s` in a second-countable Borel `EMetricSpace` maps every
`μHE[d]`-null subset `t ⊆ s` to a `μHE[d]`-null set. -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_subset {s t : Set X} {f : X → Y}
    (hf : LocallyLipschitzOn s f) (hts : t ⊆ s) (d : ℕ) (ht0 : μHE[d] t = 0) :
    μHE[d] (f '' t) = 0 := by
  obtain ⟨U, K, _, hcov, hLip⟩ := hf.exists_open_cover_lipschitzOnWith
  have ht_eq : t = ⋃ n, t ∩ U n := by
    rw [← inter_iUnion, inter_eq_self_of_subset_left (hts.trans hcov)]
  rw [ht_eq, image_iUnion]
  refine measure_iUnion_null fun n => nonpos_iff_eq_zero.mp ?_
  calc μHE[d] (f '' (t ∩ U n))
      ≤ (K n : ℝ≥0∞) ^ d * μHE[d] (t ∩ U n) :=
        ((hLip n).mono (inter_subset_inter_left _ hts)).euclideanHausdorffMeasure_image_le d
    _ = 0 := by rw [measure_mono_null inter_subset_left ht0, mul_zero]

/-- Modifying a subset of `E` on a `μHE[d]`-null set changes weighted fiber sums under a map
locally Lipschitz on `E` only on a `μHE[d]`-null set. -/
theorem tsum_fiber_congr_ae_set {E s t : Set X} {f : X → Y} (hf : LocallyLipschitzOn E f)
    (hs : s ⊆ E) (ht : t ⊆ E) {d : ℕ} (hst : s =ᵐ[μHE[d]] t) (w : X → ℝ≥0∞) :
    (fun y => ∑' x : ↥(s ∩ f ⁻¹' {y}), w x) =ᵐ[μHE[d]]
      fun y => ∑' x : ↥(t ∩ f ⁻¹' {y}), w x := by
  have hnull : μHE[d] (f '' (s ∆ t)) = 0 :=
    hf.euclideanHausdorffMeasure_image_eq_zero_of_subset
      (symmDiff_subset_union.trans (union_subset hs ht)) d
      (measure_symmDiff_eq_zero_iff.mpr hst)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  apply tsum_congr_set_coe w
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  refine ⟨fun ⟨hxs, hfx⟩ => ⟨?_, hfx⟩, fun ⟨hxt, hfx⟩ => ⟨?_, hfx⟩⟩
  · by_contra hxt
    exact hy ⟨x, Or.inl ⟨hxs, hxt⟩, hfx⟩
  · by_contra hxs
    exact hy ⟨x, Or.inr ⟨hxt, hxs⟩, hfx⟩

/-- Modifying a weight `μHE[d].restrict E`-almost everywhere changes weighted fiber sums under a
map locally Lipschitz on `E` only on a `μHE[d]`-null set. -/
theorem tsum_fiber_congr_ae_fun {E : Set X} {f : X → Y} (hf : LocallyLipschitzOn E f)
    {d : ℕ} {w₁ w₂ : X → ℝ≥0∞} (hw : w₁ =ᵐ[μHE[d].restrict E] w₂) :
    (fun y => ∑' x : ↥(E ∩ f ⁻¹' {y}), w₁ x) =ᵐ[μHE[d]]
      fun y => ∑' x : ↥(E ∩ f ⁻¹' {y}), w₂ x := by
  let N := {x | w₁ x ≠ w₂ x} ∩ E
  have hN0 : μHE[d] N = 0 :=
    nonpos_iff_eq_zero.mp ((le_restrict_apply E {x | w₁ x ≠ w₂ x}).trans_eq (ae_iff.mp hw))
  have hnull : μHE[d] (f '' N) = 0 :=
    hf.euclideanHausdorffMeasure_image_eq_zero_of_subset inter_subset_right d hN0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  refine tsum_congr fun x => not_not.mp fun hne => hy ⟨x.1, ⟨hne, x.2.1⟩, x.2.2⟩

end NullImage

end LocallyLipschitzOn

namespace LipschitzOnWith

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

/-- On a Borel bi-Lipschitz patch `f '' B ⊆ E`, `tangentialJacobian k E g (f u) * ‖det Df(u)‖`
agrees with `‖det D(gExt ∘ f)(u)‖` at `volume`-almost every parameter `u ∈ B`. -/
private lemma ae_patch_tangentialJacobian_mul_normDet (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {gExt : V → W} {KExt : ℝ≥0} (hgExt_lip : LipschitzWith KExt gExt) (hgExt_eq : EqOn g gExt E)
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → V}
    {K_f L_f : ℝ≥0} (hBm : MeasurableSet B) (hf_lip : LipschitzWith K_f f)
    (hf_anti : AntilipschitzWith L_f (B.domRestrict f)) (hsub : f '' B ⊆ E) :
    ∀ᵐ u ∂volume, u ∈ B →
      tangentialJacobian k E g (f u) * (fderiv ℝ f u).normDet =
        (fderiv ℝ (gExt ∘ f) u).normDet := by
  let U := EuclideanSpace ℝ (Fin k)
  filter_upwards [ae_regular_and_density_on_patch hEm hBm hf_lip hf_anti,
    (hgExt_lip.comp hf_lip).ae_differentiableAt] with u hreg hgf_diff huB
  obtain ⟨hf_diff, hinj_df, hdens, hdiff⟩ := hreg huB
  have hgf_within : HasFDerivWithinAt (g ∘ f) (fderiv ℝ (gExt ∘ f) u) B u :=
    hgf_diff.hasFDerivAt.hasFDerivWithinAt.congr
      (fun v hv => hgExt_eq (hsub (mem_image_of_mem f hv)))
      (hgExt_eq (hsub (mem_image_of_mem f huB)))
  have hdiff' : Tendsto (fun r =>
      μHE[finrank ℝ U] ((E \ f '' B) ∩ closedBall (f u) r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ U))) r))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [U, finrank_euclideanSpace_fin,
      ← volume_closedBall_eq_euclidean (0 : EuclideanSpace ℝ (Fin k))] using hdiff
  simpa only [U, finrank_euclideanSpace_fin] using
    hf_diff.hasFDerivAt.hasFDerivWithinAt.tangentialJacobian_mul_normDet hinj_df hf_anti huB
      hsub hdens hdiff' hgf_within

variable [MeasurableSpace W] [BorelSpace W]

/-- Patch-level identity: on a Borel bi-Lipschitz patch `f '' B ⊆ E`, the weighted tangential
Jacobian integral equals the weighted fiber-sum integral, and the patch fiber sum is
`μHE[k]`-almost everywhere measurable. -/
private lemma patch_area_formula (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {gExt : V → W} {KExt : ℝ≥0} (hgExt_lip : LipschitzWith KExt gExt) (hgExt_eq : EqOn g gExt E)
    {B : Set (EuclideanSpace ℝ (Fin k))} {f : EuclideanSpace ℝ (Fin k) → V}
    {K_f L_f : ℝ≥0} (hBm : MeasurableSet B) (hf_lip : LipschitzWith K_f f)
    (hf_anti : AntilipschitzWith L_f (B.domRestrict f)) (hsub : f '' B ⊆ E)
    {w : V → ℝ≥0∞} (hw : Measurable w) :
    AEMeasurable (fun y => ∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) μHE[k] ∧
      (∫⁻ x in f '' B, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
        ∫⁻ y, ∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
  let U := EuclideanSpace ℝ (Fin k)
  have hinj_f : InjOn f B := injOn_iff_injective.mpr hf_anti.injective
  have hset_eq (y : W) : B ∩ (g ∘ f) ⁻¹' {y} = B ∩ (gExt ∘ f) ⁻¹' {y} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, comp_apply]
    exact and_congr_right fun huB => by rw [hgExt_eq (hsub (mem_image_of_mem f huB))]
  have htsum_eq (y : W) :
      (∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) = ∑' u : ↥(B ∩ (gExt ∘ f) ⁻¹' {y}), w (f u) :=
    (tsum_fiber_image_of_injOn hinj_f g w y).trans
      (tsum_congr_set_coe (fun u => w (f u)) (hset_eq y))
  have hae_meas : AEMeasurable (fun y => ∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x) μHE[k] := by
    simp_rw [htsum_eq]
    simpa only [U, finrank_euclideanSpace_fin, comp_apply] using
      (hgExt_lip.comp hf_lip).aemeasurable_tsum_fiber hBm.nullMeasurableSet
        (hw.comp hf_lip.continuous.measurable)
  refine ⟨hae_meas, ?_⟩
  have hlhs : (∫⁻ x in f '' B, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ u in B, ENNReal.ofReal (fderiv ℝ f u).normDet *
        (ENNReal.ofReal (tangentialJacobian k E g (f u)) * w (f u)) := by
    simpa only [U, finrank_euclideanSpace_fin] using
      hf_lip.lintegral_image_eq_lintegral_normDet_fderiv_mul hBm hinj_f
        (fun x => ENNReal.ofReal (tangentialJacobian k E g x) * w x)
  have hcongr : (∫⁻ u in B, ENNReal.ofReal (fderiv ℝ f u).normDet *
        (ENNReal.ofReal (tangentialJacobian k E g (f u)) * w (f u))) =
      ∫⁻ u in B, ENNReal.ofReal (fderiv ℝ (gExt ∘ f) u).normDet * w (f u) := by
    refine setLIntegral_congr_fun_ae hBm ?_
    filter_upwards [ae_patch_tangentialJacobian_mul_normDet (g := g) hEm hgExt_lip hgExt_eq
      hBm hf_lip hf_anti hsub] with u hmul huB
    rw [← mul_assoc, mul_comm (ENNReal.ofReal (fderiv ℝ f u).normDet),
      ← ENNReal.ofReal_mul (tangentialJacobian_nonneg _ _ _ _), hmul huB]
  have hrhs : (∫⁻ u in B, ENNReal.ofReal (fderiv ℝ (gExt ∘ f) u).normDet * w (f u)) =
      ∫⁻ y, ∑' x : ↥((f '' B) ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
    simp_rw [htsum_eq]
    simpa only [U, finrank_euclideanSpace_fin, comp_apply] using
      (hgExt_lip.comp hf_lip).lintegral_normDet_fderiv_mul_eq_lintegral_tsum hBm.nullMeasurableSet
        (hw.comp hf_lip.continuous.measurable)
  exact hlhs.trans (hcongr.trans hrhs)

/-- Weighted fiber sums of a `K`-Lipschitz map on a null-measurable, countably `k`-rectifiable set
with locally finite `μHE[k]` measure are `μHE[k]`-almost everywhere measurable. -/
theorem aemeasurable_tsum_fiber (hg : LipschitzOnWith K g E) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    AEMeasurable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), w x) μHE[k] := by
  let w' := hw.mk w
  have hw'm : Measurable w' := hw.measurable_mk
  suffices h : AEMeasurable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), w' x) μHE[k] from
    h.congr (hg.locallyLipschitzOn.tsum_fiber_congr_ae_fun hw.ae_eq_mk).symm
  obtain ⟨gExt, hgExt_lip, hgExt_eq⟩ := hg.extend_finite_dimension
  obtain ⟨B, f, K_f, L_f, hBm, _, hbi, hdisj, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  have hpatch (n : ℕ) := (patch_area_formula hEm hgExt_lip hgExt_eq (hBm n) (hbi n).1 (hbi n).2
    ((subset_iUnion (fun m => f m '' B m) n).trans hsubE) hw'm).1
  have htsum_union (y : W) : (∑' x : ↥((⋃ n, f n '' B n) ∩ g ⁻¹' {y}), w' x) =
      ∑' n, ∑' x : ↥((f n '' B n) ∩ g ⁻¹' {y}), w' x := by
    rw [iUnion_inter, _root_.tsum_iUnion]
    intro i _ j _ hij
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  have hsum_meas :
      AEMeasurable (fun y => ∑' n, ∑' x : ↥((f n '' B n) ∩ g ⁻¹' {y}), w' x) μHE[k] :=
    AEMeasurable.tsum hpatch
  refine hsum_meas.congr ?_
  filter_upwards [hg.locallyLipschitzOn.tsum_fiber_congr_ae_set hsubE Subset.rfl hcover_ae w']
    with y hy
  exact (htsum_union y).symm.trans hy

/-- **The weighted tangential area formula with multiplicity (`LipschitzOnWith`).** -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
  let w' := hw.mk w
  have hw'm : Measurable w' := hw.measurable_mk
  have hlhs_w : (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w' x ∂μHE[k] :=
    lintegral_congr_ae
      (hw.ae_eq_mk.mono fun x hx => congrArg (ENNReal.ofReal (tangentialJacobian k E g x) * ·) hx)
  have hrhs_w : (∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w' x ∂μHE[k]) =
      ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] :=
    lintegral_congr_ae (hg.locallyLipschitzOn.tsum_fiber_congr_ae_fun hw.ae_eq_mk).symm
  rw [hlhs_w, ← hrhs_w]
  obtain ⟨gExt, hgExt_lip, hgExt_eq⟩ := hg.extend_finite_dimension
  obtain ⟨B, f, K_f, L_f, hBm, hTm, hbi, hdisj, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  have hp (n : ℕ) := patch_area_formula hEm hgExt_lip hgExt_eq (hBm n) (hbi n).1 (hbi n).2
    ((subset_iUnion (fun m => f m '' B m) n).trans hsubE) hw'm
  rw [setLIntegral_congr hcover_ae.symm, lintegral_iUnion hTm hdisj]
  simp_rw [fun n => (hp n).2]
  rw [← lintegral_tsum fun n => (hp n).1]
  refine (lintegral_congr fun y => ?_).trans
    (lintegral_congr_ae (hg.locallyLipschitzOn.tsum_fiber_congr_ae_set hsubE Subset.rfl
      hcover_ae w'))
  rw [iUnion_inter, _root_.tsum_iUnion]
  intro i _ j _ hij
  exact (hdisj hij).mono inter_subset_left inter_subset_left

/-- **The weighted injective tangential area formula (`LipschitzOnWith`).** When `g` is injective
on `E`, the weight `w : W → ℝ≥0∞` on the target need not be measurable. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hinj : InjOn g E) (w : W → ℝ≥0∞) :
    (∫⁻ y in g '' E, w y ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k] := by
  obtain ⟨gExt, hgExt_lip, hgExt_eq⟩ := hg.extend_finite_dimension
  obtain ⟨B, f, K_f, L_f, hBm, hTm, hbi, hdisj, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  let U := EuclideanSpace ℝ (Fin k)
  let E' := ⋃ n, f n '' B n
  have hdiff0 : μHE[k] (E \ E') = 0 :=
    measure_mono_null (fun _ ⟨hxE, hxU⟩ => Or.inr ⟨hxE, hxU⟩)
      (measure_symmDiff_eq_zero_iff.mpr hcover_ae)
  have himg_ae : g '' E =ᵐ[μHE[k]] g '' E' := by
    have hsplit : E = E' ∪ (E \ E') := (union_sdiff_cancel hsubE).symm
    nth_rw 1 [hsplit]
    rw [image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr
      (hg.locallyLipschitzOn.euclideanHausdorffMeasure_image_eq_zero_of_subset sdiff_subset k
        hdiff0))
  have hsub_n (n : ℕ) : f n '' B n ⊆ E := (subset_iUnion (fun m => f m '' B m) n).trans hsubE
  have hinj_gf (n : ℕ) : InjOn (gExt ∘ f n) (B n) := by
    intro u₁ hu₁ u₂ hu₂ h
    have h' : g (f n u₁) = g (f n u₂) := by
      simpa only [comp_apply, ← hgExt_eq (hsub_n n (mem_image_of_mem (f n) hu₁)),
        ← hgExt_eq (hsub_n n (mem_image_of_mem (f n) hu₂))] using h
    exact injOn_iff_injective.mpr (hbi n).2.injective hu₁ hu₂
      (hinj (hsub_n n (mem_image_of_mem (f n) hu₁)) (hsub_n n (mem_image_of_mem (f n) hu₂)) h')
  have himg_eq (n : ℕ) : g '' (f n '' B n) = (gExt ∘ f n) '' B n := by
    rw [← image_comp]
    exact image_congr fun u hu => hgExt_eq (hsub_n n (mem_image_of_mem (f n) hu))
  have hIm (n : ℕ) : MeasurableSet (g '' (f n '' B n)) := by
    rw [himg_eq n]
    exact (hBm n).image_of_continuousOn_injOn
      (hgExt_lip.comp (hbi n).1).continuous.continuousOn (hinj_gf n)
  have hIdisj : Pairwise (Disjoint on fun n => g '' (f n '' B n)) := by
    intro i j hij
    exact Disjoint.image (hdisj hij) hinj (hsub_n i) (hsub_n j)
  -- Compare each Borel patch `f n '' B n` and its Borel image via the Euclidean injective formula.
  have hpiece (n : ℕ) : (∫⁻ y in g '' (f n '' B n), w y ∂μHE[k]) =
      ∫⁻ x in f n '' B n, ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k] := by
    have h1 : (∫⁻ y in g '' (f n '' B n), w y ∂μHE[k]) =
        ∫⁻ u in B n, ENNReal.ofReal (fderiv ℝ (gExt ∘ f n) u).normDet * w (gExt (f n u)) := by
      rw [himg_eq n]
      simpa only [U, finrank_euclideanSpace_fin, comp_apply] using
        (hgExt_lip.comp (hbi n).1).lintegral_image_eq_lintegral_normDet_fderiv_mul (hBm n)
          (hinj_gf n) w
    have h2 : (∫⁻ x in f n '' B n,
          ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k]) =
        ∫⁻ u in B n, ENNReal.ofReal (fderiv ℝ (f n) u).normDet *
          (ENNReal.ofReal (tangentialJacobian k E g (f n u)) * w (g (f n u))) := by
      simpa only [U, finrank_euclideanSpace_fin] using
        (hbi n).1.lintegral_image_eq_lintegral_normDet_fderiv_mul (hBm n)
          (injOn_iff_injective.mpr (hbi n).2.injective)
          (fun x => ENNReal.ofReal (tangentialJacobian k E g x) * w (g x))
    rw [h1, h2]
    refine setLIntegral_congr_fun_ae (hBm n) ?_
    filter_upwards [ae_patch_tangentialJacobian_mul_normDet (g := g) hEm hgExt_lip hgExt_eq
      (hBm n) (hbi n).1 (hbi n).2 (hsub_n n)] with u hmul huB
    rw [← hgExt_eq (hsub_n n (mem_image_of_mem (f n) huB)), ← mul_assoc,
      mul_comm (ENNReal.ofReal (fderiv ℝ (f n) u).normDet),
      ← ENNReal.ofReal_mul (tangentialJacobian_nonneg _ _ _ _), hmul huB]
  rw [setLIntegral_congr himg_ae, image_iUnion, lintegral_iUnion hIm hIdisj,
    setLIntegral_congr hcover_ae.symm, lintegral_iUnion hTm hdisj]
  exact tsum_congr hpiece

end LipschitzOnWith

namespace LocallyLipschitzOn

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  {k : ℕ} {E : Set V} {g : V → W}

/-- **Measurability of weighted fiber sums (`LocallyLipschitzOn`).** -/
theorem aemeasurable_tsum_fiber (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    AEMeasurable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), w x) μHE[k] := by
  let w' := hw.mk w
  have hw'm : Measurable w' := hw.measurable_mk
  suffices h : AEMeasurable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), w' x) μHE[k] from
    h.congr (hg.tsum_fiber_congr_ae_fun hw.ae_eq_mk).symm
  obtain ⟨O, K, hO, hcov, hLip⟩ := hg.exists_open_cover_lipschitzOnWith
  let D : ℕ → Set V := disjointed O
  have hDm (m : ℕ) : MeasurableSet (D m) :=
    MeasurableSet.disjointed (fun n => (hO n).measurableSet) m
  have hDO (m : ℕ) : D m ⊆ O m := disjointed_subset O m
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed O
  have hDcov : E ⊆ ⋃ m, D m := by simpa only [D, iUnion_disjointed] using hcov
  have hED : (⋃ m, E ∩ D m) = E := by rw [← inter_iUnion, inter_eq_self_of_subset_left hDcov]
  have hpiece (m : ℕ) :
      AEMeasurable (fun y => ∑' x : ↥((E ∩ D m) ∩ g ⁻¹' {y}), w' x) μHE[k] := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E ∩ O m)) := by
      rw [inter_comm, ← Measure.restrict_restrict (hO m).measurableSet]
      infer_instance
    have hm := (hLip m).aemeasurable_tsum_fiber (hE.mono inter_subset_left)
      (hEm.inter (hO m).measurableSet.nullMeasurableSet)
      (hw'm.indicator (hDm m)).aemeasurable
    simpa only [tsum_fiber_indicator_of_subset (hDO m) g w'] using hm
  have hdecomp (y : W) :
      (∑' x : ↥(E ∩ g ⁻¹' {y}), w' x) = ∑' m, ∑' x : ↥((E ∩ D m) ∩ g ⁻¹' {y}), w' x := by
    refine (tsum_congr_set_coe w' (by nth_rw 1 [← hED]; rw [iUnion_inter])).trans
      (_root_.tsum_iUnion ?_)
    intro i _ j _ hij
    exact ((hDdisj hij).mono inter_subset_right inter_subset_right).mono
      inter_subset_left inter_subset_left
  simp_rw [hdecomp]
  exact AEMeasurable.tsum hpiece

/-- **The weighted tangential area formula with multiplicity (`LocallyLipschitzOn`).** For a map
locally Lipschitz on a null-measurable, countably `k`-rectifiable set `E` with locally finite
`μHE[k]` measure, integrating `tangentialJacobian k E g` against a nonnegative
`μHE[k].restrict E`-almost everywhere measurable weight `w` equals the `μHE[k]` integral of the
extended sum of `w` over each fiber. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum (hg : LocallyLipschitzOn E g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] := by
  let w' := hw.mk w
  have hw'm : Measurable w' := hw.measurable_mk
  have hlhs_w : (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w' x ∂μHE[k] :=
    lintegral_congr_ae
      (hw.ae_eq_mk.mono fun x hx => congrArg (ENNReal.ofReal (tangentialJacobian k E g x) * ·) hx)
  have hrhs_w : (∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w' x ∂μHE[k]) =
      ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] :=
    lintegral_congr_ae (hg.tsum_fiber_congr_ae_fun hw.ae_eq_mk).symm
  rw [hlhs_w, ← hrhs_w]
  -- Partition `E` by `D := disjointed O` and apply `LipschitzOnWith` on `E ∩ O m`.
  obtain ⟨O, K, hO, hcov, hLip⟩ := hg.exists_open_cover_lipschitzOnWith
  let D : ℕ → Set V := disjointed O
  have hDm (m : ℕ) : MeasurableSet (D m) :=
    MeasurableSet.disjointed (fun n => (hO n).measurableSet) m
  have hDO (m : ℕ) : D m ⊆ O m := disjointed_subset O m
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed O
  have hDcov : E ⊆ ⋃ m, D m := by simpa only [D, iUnion_disjointed] using hcov
  have hED : (⋃ m, E ∩ D m) = E := by rw [← inter_iUnion, inter_eq_self_of_subset_left hDcov]
  let F : V → ℝ≥0∞ := fun x => ENNReal.ofReal (tangentialJacobian k E g x) * w' x
  have hpiece_meas (m : ℕ) :
      AEMeasurable (fun y => ∑' x : ↥((E ∩ D m) ∩ g ⁻¹' {y}), w' x) μHE[k] := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E ∩ O m)) := by
      rw [inter_comm, ← Measure.restrict_restrict (hO m).measurableSet]
      infer_instance
    simpa only [tsum_fiber_indicator_of_subset (hDO m) g w'] using
      (hLip m).aemeasurable_tsum_fiber (hE.mono inter_subset_left)
        (hEm.inter (hO m).measurableSet.nullMeasurableSet)
        (hw'm.indicator (hDm m)).aemeasurable
  have hpiece_eq (m : ℕ) :
      (∫⁻ x in E ∩ D m, F x ∂μHE[k]) =
        ∫⁻ y, ∑' x : ↥((E ∩ D m) ∩ g ⁻¹' {y}), w' x ∂μHE[k] := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E ∩ O m)) := by
      rw [inter_comm, ← Measure.restrict_restrict (hO m).measurableSet]
      infer_instance
    have hEOm : NullMeasurableSet (E ∩ O m) μHE[k] :=
      hEm.inter (hO m).measurableSet.nullMeasurableSet
    have hstep := (hLip m).lintegral_tangentialJacobian_mul_eq_lintegral_tsum
      (hE.mono inter_subset_left) hEOm (hw'm.indicator (hDm m)).aemeasurable
    simp_rw [tsum_fiber_indicator_of_subset (hDO m) g w'] at hstep
    rw [← hstep]
    have hinter_eq : D m ∩ (E ∩ O m) = E ∩ D m := by
      ext x
      exact ⟨fun hx => ⟨hx.2.1, hx.1⟩, fun hx => ⟨hx.2, hx.1, hDO m hx.2⟩⟩
    rw [← hinter_eq, ← Measure.restrict_restrict (hDm m), ← lintegral_indicator (hDm m)]
    refine lintegral_congr_ae ((ae_restrict_iff'₀ hEOm).mpr (Eventually.of_forall fun x hx => ?_))
    have hnhds : (E ∩ O m : Set V) =ᶠ[𝓝 x] E := by
      filter_upwards [(hO m).mem_nhds hx.2] with z hz
      simp [hz]
    by_cases hxD : x ∈ D m <;> simp [F, hxD, tangentialJacobian_congr_nhds_set hnhds]
  have hlhs_sum : (∫⁻ x in E, F x ∂μHE[k]) = ∑' m, ∫⁻ x in E ∩ D m, F x ∂μHE[k] := by
    nth_rw 1 [← hED]
    exact lintegral_iUnion₀ (fun m => hEm.inter (hDm m).nullMeasurableSet)
      (fun i j hij => ((hDdisj hij).mono inter_subset_right inter_subset_right).aedisjoint) F
  rw [hlhs_sum]
  simp_rw [hpiece_eq]
  rw [← lintegral_tsum hpiece_meas]
  refine lintegral_congr fun y => Eq.symm ?_
  refine (tsum_congr_set_coe w' (by nth_rw 1 [← hED]; rw [iUnion_inter])).trans
    (_root_.tsum_iUnion ?_)
  intro i _ j _ hij
  exact ((hDdisj hij).mono inter_subset_right inter_subset_right).mono
    inter_subset_left inter_subset_left

/-- Extended fiber cardinalities of a map locally Lipschitz on a null-measurable, countably
`k`-rectifiable set with locally finite `μHE[k]` measure are `μHE[k]`-almost everywhere
measurable. -/
theorem aemeasurable_encard_fiber (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    AEMeasurable (fun y => ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞)) μHE[k] := by
  simpa only [ENNReal.tsum_set_one] using
    hg.aemeasurable_tsum_fiber hE hEm (w := fun _ => 1) aemeasurable_const

/-- **The unweighted tangential area formula with multiplicity (`LocallyLipschitzOn`).**
Infinite fibers contribute `∞` via `Set.encard`. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard (hg : LocallyLipschitzOn E g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) =
      ∫⁻ y, ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] := by
  simpa only [mul_one, ENNReal.tsum_set_one] using
    hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm
      (w := fun _ => 1) aemeasurable_const

/-- **The weighted injective tangential area formula (`LocallyLipschitzOn`).** When `g` is
injective on `E`, the weight `w : W → ℝ≥0∞` on the target need not be measurable. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hg : LocallyLipschitzOn E g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hinj : InjOn g E) (w : W → ℝ≥0∞) :
    (∫⁻ y in g '' E, w y ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k] := by
  -- Step 1: replace `E` up to `μHE[k]`-null sets by the Borel union `E'` of bi-Lipschitz patches,
  -- ensuring each piece `g '' (E' ∩ D m)` is Borel measurable by `image_of_continuousOn_injOn`.
  obtain ⟨B, f, _, _, _, hTm, _, _, hsubE, hcover_ae⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  let E' := ⋃ n, f n '' B n
  have hE'm : MeasurableSet E' := MeasurableSet.iUnion hTm
  have hE'_rect : CountablyRectifiable k E' := hE.mono hsubE
  have : IsLocallyFiniteMeasure (μHE[k].restrict E') := by
    rw [Measure.restrict_congr_set hcover_ae]
    infer_instance
  have hdiff0 : μHE[k] (E \ E') = 0 :=
    measure_mono_null (fun _ ⟨hxE, hxU⟩ => Or.inr ⟨hxE, hxU⟩)
      (measure_symmDiff_eq_zero_iff.mpr hcover_ae)
  have himg_ae : g '' E =ᵐ[μHE[k]] g '' E' := by
    have hsplit : E = E' ∪ (E \ E') := (union_sdiff_cancel hsubE).symm
    nth_rw 1 [hsplit]
    rw [image_union]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr
      (hg.euclideanHausdorffMeasure_image_eq_zero_of_subset sdiff_subset k hdiff0))
  have hrhs_E' : (∫⁻ x in E', ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x) ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k] := by
    refine (setLIntegral_congr_fun hE'm fun x _ => ?_).trans (setLIntegral_congr hcover_ae)
    rw [tangentialJacobian_congr_ae_set (k := k) (hcover_ae : E' =ᵐ[μHE[k]] E) g x]
  rw [setLIntegral_congr himg_ae, ← hrhs_E']
  -- Step 2: partition `E'` by `D := disjointed O` with weights `(g '' (E' ∩ D m)).indicator w`.
  obtain ⟨O, K, hO, hcov, hLip⟩ := (hg.mono hsubE).exists_open_cover_lipschitzOnWith
  let D : ℕ → Set V := disjointed O
  have hDm (m : ℕ) : MeasurableSet (D m) :=
    MeasurableSet.disjointed (fun n => (hO n).measurableSet) m
  have hDO (m : ℕ) : D m ⊆ O m := disjointed_subset O m
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed O
  have hDcov : E' ⊆ ⋃ m, D m := by simpa only [D, iUnion_disjointed] using hcov
  have hED : (⋃ m, E' ∩ D m) = E' := by rw [← inter_iUnion, inter_eq_self_of_subset_left hDcov]
  have hinj' : InjOn g E' := hinj.mono hsubE
  have hIm (m : ℕ) : MeasurableSet (g '' (E' ∩ D m)) :=
    (hE'm.inter (hDm m)).image_of_continuousOn_injOn
      ((hLip m).mono (inter_subset_inter_right E' (hDO m))).continuousOn
      (hinj'.mono inter_subset_left)
  have hIdisj : Pairwise (Disjoint on fun m => g '' (E' ∩ D m)) := by
    intro i j hij
    exact Disjoint.image ((hDdisj hij).mono inter_subset_right inter_subset_right)
      hinj' inter_subset_left inter_subset_left
  have hpiece (m : ℕ) : (∫⁻ y in g '' (E' ∩ D m), w y ∂μHE[k]) =
      ∫⁻ x in E' ∩ D m, ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x) ∂μHE[k] := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E' ∩ O m)) := by
      rw [inter_comm, ← Measure.restrict_restrict (hO m).measurableSet]
      infer_instance
    have hEOm : MeasurableSet (E' ∩ O m) := hE'm.inter (hO m).measurableSet
    have hstep := (hLip m).lintegral_image_eq_lintegral_tangentialJacobian_mul
      (hE'_rect.mono inter_subset_left) hEOm.nullMeasurableSet
      (hinj'.mono inter_subset_left) ((g '' (E' ∩ D m)).indicator w)
    have htarget : (∫⁻ y in g '' (E' ∩ O m), (g '' (E' ∩ D m)).indicator w y ∂μHE[k]) =
        ∫⁻ y in g '' (E' ∩ D m), w y ∂μHE[k] := by
      have hsub_img : g '' (E' ∩ D m) ⊆ g '' (E' ∩ O m) :=
        image_mono (inter_subset_inter_right E' (hDO m))
      rw [lintegral_indicator (hIm m), Measure.restrict_restrict (hIm m),
        inter_eq_self_of_subset_left hsub_img]
    have hsource : (∫⁻ x in E' ∩ O m, ENNReal.ofReal (tangentialJacobian k (E' ∩ O m) g x) *
          (g '' (E' ∩ D m)).indicator w (g x) ∂μHE[k]) =
        ∫⁻ x in E' ∩ D m, ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x) ∂μHE[k] := by
      let F : V → ℝ≥0∞ := fun x => ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x)
      have hinter_eq : D m ∩ (E' ∩ O m) = E' ∩ D m := by
        ext x
        exact ⟨fun hx => ⟨hx.2.1, hx.1⟩, fun hx => ⟨hx.2, hx.1, hDO m hx.2⟩⟩
      have hsource_ind : (∫⁻ x in E' ∩ D m, F x ∂μHE[k]) =
          ∫⁻ x in E' ∩ O m, (D m).indicator F x ∂μHE[k] := by
        rw [← hinter_eq, ← Measure.restrict_restrict (hDm m), lintegral_indicator (hDm m)]
      rw [hsource_ind]
      refine setLIntegral_congr_fun hEOm fun x hx => ?_
      have hnhds : (E' ∩ O m : Set V) =ᶠ[𝓝 x] E' := by
        filter_upwards [(hO m).mem_nhds hx.2] with z hz
        simp [hz]
      rw [tangentialJacobian_congr_nhds_set hnhds]
      by_cases hxD : x ∈ D m
      · have hxg : g x ∈ g '' (E' ∩ D m) := mem_image_of_mem g ⟨hx.1, hxD⟩
        rw [indicator_of_mem hxg, indicator_of_mem hxD]
      · have hxg : g x ∉ g '' (E' ∩ D m) := fun ⟨z, ⟨hzE', hzD⟩, hgz⟩ =>
          hxD (hinj' hzE' hx.1 hgz ▸ hzD)
        rw [indicator_of_notMem hxg, indicator_of_notMem hxD, mul_zero]
    exact htarget.symm.trans (hstep.trans hsource)
  have hlhs_u : (∫⁻ y in g '' E', w y ∂μHE[k]) = ∑' m, ∫⁻ y in g '' (E' ∩ D m), w y ∂μHE[k] := by
    nth_rw 1 [← hED]
    rw [image_iUnion, lintegral_iUnion hIm hIdisj]
  have hrhs_u : (∫⁻ x in E', ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x) ∂μHE[k]) =
      ∑' m, ∫⁻ x in E' ∩ D m,
        ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x) ∂μHE[k] := by
    nth_rw 1 [← hED]
    exact lintegral_iUnion (fun m => hE'm.inter (hDm m))
      (fun i j hij => (hDdisj hij).mono inter_subset_right inter_subset_right)
      (fun x => ENNReal.ofReal (tangentialJacobian k E' g x) * w (g x))
  rw [hlhs_u, hrhs_u]
  exact tsum_congr hpiece

/-- **The injective tangential area formula (`LocallyLipschitzOn`).** -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image
    (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hinj : InjOn g E) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) = μHE[k] (g '' E) := by
  simpa using (hg.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj 1).symm

/-- **Zero tangential Jacobians have null images.** If `tangentialJacobian k E g` vanishes
`μHE[k]`-almost everywhere on `E`, then `μHE[k] (g '' E) = 0`. No injectivity of `g` is needed. -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero
    (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hzero : ∀ᵐ x ∂μHE[k], x ∈ E → tangentialJacobian k E g x = 0) :
    μHE[k] (g '' E) = 0 := by
  have hlint : (∫⁻ y, ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k]) = 0 := by
    rw [← hg.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm]
    refine (lintegral_congr_ae ((ae_restrict_iff'₀ hEm).mpr ?_)).trans lintegral_zero
    filter_upwards [hzero] with x hx hxE
    simp [hx hxE]
  have hae_zero := (lintegral_eq_zero_iff' (hg.aemeasurable_encard_fiber hE hEm)).mp hlint
  refine measure_mono_null ?_ (ae_iff.mp hae_zero)
  rintro _ ⟨x, hxE, rfl⟩ h0
  have hempty : E ∩ g ⁻¹' {g x} = ∅ := by simpa using h0
  exact notMem_empty x (hempty ▸ ⟨hxE, rfl⟩)

/-- **Rank-deficient tangential derivatives have null images.** If `g` is locally Lipschitz on `E`
and `finrank ℝ (LinearMap.range (tangentialFDeriv k E g x).toLinearMap) < k` at `μHE[k]`-almost
every `x ∈ E` (in particular whenever `finrank ℝ W < k`), then `μHE[k] (g '' E) = 0`. -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt
    (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hrank : ∀ᵐ x ∂μHE[k], x ∈ E →
      finrank ℝ (LinearMap.range (tangentialFDeriv k E g x).toLinearMap) < k) :
    μHE[k] (g '' E) = 0 := by
  refine hg.euclideanHausdorffMeasure_image_eq_zero_of_tangentialJacobian_ae_zero hE hEm ?_
  filter_upwards [hrank] with x hlt hxE
  exact tangentialJacobian_eq_zero_of_finrank_range_lt (hlt hxE)

section RealValued

variable {w : V → ℝ≥0}

/-- If the weighted tangential Jacobian is integrable on `E`, then the extended weighted fiber sum
has finite `μHE[k]` integral. -/
theorem lintegral_tsum_fiber_ne_top (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    (∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ≥0∞) ∂μHE[k]) ≠ ∞ := by
  rw [← hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw.coe_nnreal_ennreal]
  simpa only [ENNReal.ofReal_mul (tangentialJacobian_nonneg _ _ _ _), ENNReal.ofReal_coe_nnreal]
    using hint.lintegral_lt_top.ne

/-- If the weighted tangential Jacobian is integrable on `E`, then the real weights on
`μHE[k]`-almost every fiber are summable. -/
theorem ae_summable_fiber (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    ∀ᵐ y ∂μHE[k], Summable fun x : ↥(E ∩ g ⁻¹' {y}) => (w x : ℝ) := by
  let G : W → ℝ≥0∞ := fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ≥0∞)
  have hG : AEMeasurable G μHE[k] := hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal
  have hfin : ∫⁻ y, G y ∂μHE[k] ≠ ∞ := hg.lintegral_tsum_fiber_ne_top hE hEm hw hint
  filter_upwards [ae_lt_top' hG hfin] with y hy
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hy.ne

/-- If the weighted tangential Jacobian is integrable on `E`, then the real weighted fiber sum is
`μHE[k]`-integrable on `W`. -/
theorem integrable_tsum_fiber (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    Integrable (fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ)) μHE[k] := by
  let G : W → ℝ≥0∞ := fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ≥0∞)
  have hG : AEMeasurable G μHE[k] := hg.aemeasurable_tsum_fiber hE hEm hw.coe_nnreal_ennreal
  have hfin : ∫⁻ y, G y ∂μHE[k] ≠ ∞ := hg.lintegral_tsum_fiber_ne_top hE hEm hw hint
  refine (integrable_toReal_of_lintegral_ne_top hG hfin).congr ?_
  exact Eventually.of_forall fun y => by
    simpa only [ENNReal.coe_toReal] using
      (ENNReal.tsum_toReal_eq
        (f := fun x : ↥(E ∩ g ⁻¹' {y}) => (w x : ℝ≥0∞)) fun _ => ENNReal.coe_ne_top)

/-- **The real weighted tangential area formula with multiplicity (`LocallyLipschitzOn`).** -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum (hg : LocallyLipschitzOn E g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x * (w x : ℝ) ∂μHE[k]) =
      ∫ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ) ∂μHE[k] := by
  let A : V → ℝ≥0∞ := fun x => ENNReal.ofReal (tangentialJacobian k E g x) * (w x : ℝ≥0∞)
  let G : W → ℝ≥0∞ := fun y => ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ≥0∞)
  have hw' : AEMeasurable (fun x => (w x : ℝ≥0∞)) (μHE[k].restrict E) := hw.coe_nnreal_ennreal
  have hA : AEMeasurable A (μHE[k].restrict E) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (hg.aemeasurable_tangentialJacobian hE hEm)).mul hw'
  have hApoint : ∀ x, A x < ∞ :=
    fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top
  have hG : AEMeasurable G μHE[k] := hg.aemeasurable_tsum_fiber hE hEm hw'
  have harea := hg.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw'
  have hGpoint : ∀ᵐ y ∂μHE[k], G y < ∞ :=
    ae_lt_top' hG (hg.lintegral_tsum_fiber_ne_top hE hEm hw hint)
  calc
    (∫ x in E, tangentialJacobian k E g x * (w x : ℝ) ∂μHE[k]) =
        (∫⁻ x in E, A x ∂μHE[k]).toReal := by
      rw [← integral_toReal hA (Eventually.of_forall hApoint)]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        simp only [A, ENNReal.toReal_mul, ENNReal.toReal_ofReal (tangentialJacobian_nonneg _ _ _ _),
          ENNReal.coe_toReal])
    _ = (∫⁻ y, G y ∂μHE[k]).toReal := congrArg ENNReal.toReal harea
    _ = ∫ y, (G y).toReal ∂μHE[k] := (integral_toReal hG hGpoint).symm
    _ = ∫ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ) ∂μHE[k] := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simpa only [G, ENNReal.coe_toReal] using
        (ENNReal.tsum_toReal_eq
          (f := fun x : ↥(E ∩ g ⁻¹' {y}) => (w x : ℝ≥0∞)) fun _ => ENNReal.coe_ne_top)

/-- If `tangentialJacobian k E g` is integrable on `E`, then `μHE[k]`-almost every fiber
`E ∩ g ⁻¹' {y}` is finite. -/
theorem ae_finite_fiber (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hint : IntegrableOn (tangentialJacobian k E g) E μHE[k]) :
    ∀ᵐ y ∂μHE[k], (E ∩ g ⁻¹' {y}).Finite := by
  have hsum := hg.ae_summable_fiber hE hEm (w := fun _ => 1) aemeasurable_const
    (by simpa using hint)
  filter_upwards [hsum] with y hy
  exact Set.finite_coe_iff.mp (Finite.of_summable_const zero_lt_one hy)

/-- If `tangentialJacobian k E g` is integrable on `E`, then the real fiber cardinality `ncard` is
`μHE[k]`-integrable on `W`. -/
theorem integrable_ncard_fiber (hg : LocallyLipschitzOn E g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hint : IntegrableOn (tangentialJacobian k E g) E μHE[k]) :
    Integrable (fun y => ((E ∩ g ⁻¹' {y}).ncard : ℝ)) μHE[k] := by
  have h := hg.integrable_tsum_fiber hE hEm (w := fun _ => 1) aemeasurable_const
    (by simpa using hint)
  refine h.congr ?_
  filter_upwards [hg.ae_finite_fiber hE hEm hint] with y hy
  let _ : Finite ↥(E ∩ g ⁻¹' {y}) := Set.finite_coe_iff.mpr hy
  simp

/-- **The real unweighted tangential area formula (`LocallyLipschitzOn`).** -/
theorem integral_tangentialJacobian_eq_integral_ncard (hg : LocallyLipschitzOn E g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hint : IntegrableOn (tangentialJacobian k E g) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x ∂μHE[k]) =
      ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] := by
  have h := hg.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm (w := fun _ => 1)
    aemeasurable_const (by simpa using hint)
  calc
    (∫ x in E, tangentialJacobian k E g x ∂μHE[k]) =
        ∫ y, ∑' _ : ↥(E ∩ g ⁻¹' {y}), (1 : ℝ) ∂μHE[k] := by simpa using h
    _ = ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] := by
      refine integral_congr_ae ?_
      filter_upwards [hg.ae_finite_fiber hE hEm hint] with y hy
      let _ : Finite ↥(E ∩ g ⁻¹' {y}) := Set.finite_coe_iff.mpr hy
      simp

end RealValued

end LocallyLipschitzOn

namespace LipschitzOnWith

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

/-- Unweighted tangential area formula with multiplicity for `LipschitzOnWith`. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) =
      ∫⁻ y, ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] :=
  hg.locallyLipschitzOn.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm

/-- Injective tangential area formula for `LipschitzOnWith`. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image
    (hg : LipschitzOnWith K g E) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hinj : InjOn g E) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) = μHE[k] (g '' E) :=
  hg.locallyLipschitzOn.lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image hE hEm hinj

/-- Rank-deficient tangential derivatives have null images (`LipschitzOnWith`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt
    (hg : LipschitzOnWith K g E) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hrank : ∀ᵐ x ∂μHE[k], x ∈ E →
      finrank ℝ (LinearMap.range (tangentialFDeriv k E g x).toLinearMap) < k) :
    μHE[k] (g '' E) = 0 :=
  hg.locallyLipschitzOn.euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt
    hE hEm hrank

/-- Real weighted tangential area formula with multiplicity for `LipschitzOnWith`. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] {w : V → ℝ≥0}
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x * (w x : ℝ) ∂μHE[k]) =
      ∫ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ) ∂μHE[k] :=
  hg.locallyLipschitzOn.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm hw hint

/-- Real unweighted tangential area formula for `LipschitzOnWith`. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hg : LipschitzOnWith K g E)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hint : IntegrableOn (tangentialJacobian k E g) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x ∂μHE[k]) =
      ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] :=
  hg.locallyLipschitzOn.integral_tangentialJacobian_eq_integral_ncard hE hEm hint

end LipschitzOnWith

namespace LipschitzWith

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  {k : ℕ} {E : Set V} {g : V → W} {K : ℝ≥0}

/-- Weighted tangential area formula with multiplicity for globally `K`-Lipschitz maps. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum (hg : LipschitzWith K g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] :=
  hg.lipschitzOnWith.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw

/-- Unweighted tangential area formula with multiplicity for globally `K`-Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard (hg : LipschitzWith K g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) =
      ∫⁻ y, ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] :=
  hg.lipschitzOnWith.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm

/-- Weighted injective tangential area formula for globally `K`-Lipschitz maps. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hg : LipschitzWith K g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hinj : InjOn g E) (w : W → ℝ≥0∞) :
    (∫⁻ y in g '' E, w y ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k] :=
  hg.lipschitzOnWith.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj w

/-- Injective tangential area formula for globally `K`-Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image
    (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hinj : InjOn g E) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) = μHE[k] (g '' E) :=
  hg.lipschitzOnWith.lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image hE hEm hinj

/-- Rank-deficient tangential derivatives have null images (`LipschitzWith`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt
    (hg : LipschitzWith K g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hrank : ∀ᵐ x ∂μHE[k], x ∈ E →
      finrank ℝ (LinearMap.range (tangentialFDeriv k E g x).toLinearMap) < k) :
    μHE[k] (g '' E) = 0 :=
  hg.lipschitzOnWith.euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt
    hE hEm hrank

/-- Real weighted tangential area formula with multiplicity for globally `K`-Lipschitz maps. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum (hg : LipschitzWith K g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] {w : V → ℝ≥0}
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x * (w x : ℝ) ∂μHE[k]) =
      ∫ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ) ∂μHE[k] :=
  hg.lipschitzOnWith.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm hw hint

/-- Real unweighted tangential area formula for globally `K`-Lipschitz maps. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hg : LipschitzWith K g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hint : IntegrableOn (tangentialJacobian k E g) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x ∂μHE[k]) =
      ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] :=
  hg.lipschitzOnWith.integral_tangentialJacobian_eq_integral_ncard hE hEm hint

end LipschitzWith

namespace LocallyLipschitz

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  {k : ℕ} {E : Set V} {g : V → W}

/-- Weighted tangential area formula with multiplicity for locally Lipschitz maps. -/
theorem lintegral_tangentialJacobian_mul_eq_lintegral_tsum (hg : LocallyLipschitz g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    {w : V → ℝ≥0∞} (hw : AEMeasurable w (μHE[k].restrict E)) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w x ∂μHE[k]) =
      ∫⁻ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), w x ∂μHE[k] :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.lintegral_tangentialJacobian_mul_eq_lintegral_tsum hE hEm hw

/-- Unweighted tangential area formula with multiplicity for locally Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_lintegral_encard (hg : LocallyLipschitz g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) =
      ∫⁻ y, ((E ∩ g ⁻¹' {y}).encard : ℝ≥0∞) ∂μHE[k] :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.lintegral_tangentialJacobian_eq_lintegral_encard hE hEm

/-- Weighted injective tangential area formula for locally Lipschitz maps. -/
theorem lintegral_image_eq_lintegral_tangentialJacobian_mul (hg : LocallyLipschitz g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] (hinj : InjOn g E) (w : W → ℝ≥0∞) :
    (∫⁻ y in g '' E, w y ∂μHE[k]) =
      ∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) * w (g x) ∂μHE[k] :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.lintegral_image_eq_lintegral_tangentialJacobian_mul hE hEm hinj w

/-- Injective tangential area formula for locally Lipschitz maps. -/
theorem lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image
    (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hinj : InjOn g E) :
    (∫⁻ x in E, ENNReal.ofReal (tangentialJacobian k E g x) ∂μHE[k]) = μHE[k] (g '' E) :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.lintegral_tangentialJacobian_eq_euclideanHausdorffMeasure_image hE hEm hinj

/-- Rank-deficient tangential derivatives have null images (`LocallyLipschitz`). -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt
    (hg : LocallyLipschitz g) (hE : CountablyRectifiable k E)
    (hEm : NullMeasurableSet E μHE[k]) [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hrank : ∀ᵐ x ∂μHE[k], x ∈ E →
      finrank ℝ (LinearMap.range (tangentialFDeriv k E g x).toLinearMap) < k) :
    μHE[k] (g '' E) = 0 :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.euclideanHausdorffMeasure_image_eq_zero_of_finrank_range_tangentialFDeriv_lt hE hEm hrank

/-- Real weighted tangential area formula with multiplicity for locally Lipschitz maps. -/
theorem integral_tangentialJacobian_mul_eq_integral_tsum (hg : LocallyLipschitz g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] {w : V → ℝ≥0}
    (hw : AEMeasurable w (μHE[k].restrict E))
    (hint : IntegrableOn (fun x => tangentialJacobian k E g x * (w x : ℝ)) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x * (w x : ℝ) ∂μHE[k]) =
      ∫ y, ∑' x : ↥(E ∩ g ⁻¹' {y}), (w x : ℝ) ∂μHE[k] :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.integral_tangentialJacobian_mul_eq_integral_tsum hE hEm hw hint

/-- Real unweighted tangential area formula for locally Lipschitz maps. -/
theorem integral_tangentialJacobian_eq_integral_ncard (hg : LocallyLipschitz g)
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)]
    (hint : IntegrableOn (tangentialJacobian k E g) E μHE[k]) :
    (∫ x in E, tangentialJacobian k E g x ∂μHE[k]) =
      ∫ y, ((E ∩ g ⁻¹' {y}).ncard : ℝ) ∂μHE[k] :=
  (hg.comp_locallyLipschitzOn (LipschitzWith.id.lipschitzOnWith.locallyLipschitzOn (s := E)))
    |>.integral_tangentialJacobian_eq_integral_ncard hE hEm hint

end LocallyLipschitz
