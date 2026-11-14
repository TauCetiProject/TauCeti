/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Analysis.ConstantSpeed
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.EVariationComparison
import TauCeti.MeasureTheory.Covering.DisjointCover
import TauCeti.MeasureTheory.Measure.Stieltjes
import TauCeti.Topology.EMetricSpace.CurveLength

/-!
# The area formula for curves in a Riemannian manifold

Let `γ : ℝ → M` be a `C¹` curve on an open parameter set `O` in a Riemannian manifold, and let
`μH[1]` be the one-dimensional Hausdorff measure of the Riemannian extended distance. For a
measurable `B ⊆ O`, the trace measure of `γ '' B` is at most the integral of the speed `‖γ'‖` over
`B`; when `γ` is injective on `B` the two are equal. Equivalently, pushing forward the
speed-weighted Lebesgue measure on an injective parameter set gives the Hausdorff measure of its
image, so that `∫⁻ y in γ '' A, g y ∂μH[1] = ∫⁻ s in A, ‖γ' s‖ g (γ s)` for every weight `g`.

## The argument

On a compact interval `[p, q] ⊆ O` the trace measure is at most the total variation, which is the
Riemannian length `∫_[p, q] ‖γ'‖` (`TauCeti.Manifold.eVariationOn_eq_pathELength`). On a compact
interval `K ⊆ O`, the set function `B ↦ μH[1] (γ '' (B ∩ K))` is an outer measure bounded on every
interval `(a, b]` by the finite measure `ν` with density `‖γ'‖` on `K`. Writing `ν` as the measure
of its cumulative Stieltjes function, whose outer measure is the largest outer measure with these
interval values, the bound extends to every measurable set
(`MeasureTheory.OuterMeasure.le_measure_of_Ioc_le`). Countably many disjoint measurable pieces of
compact intervals cover `B` (`TauCeti.exists_disjoint_measurableSet_cover_of_mem_nhds`), which
gives the upper bound.

For the equality, the points where the velocity vanishes contribute nothing to either side. Near
a point with nonzero velocity `γ` is injective on a compact interval `J` around that point
(`ContMDiffAt.exists_mem_nhds_injOn_of_curveVelocity_ne_zero`). There the trace measure of
`γ '' J` is again the length (`ContinuousOn.eVariationOn_eq_hausdorffMeasure_image`), which is
finite, and the upper bound on the complement turns into the lower bound on every measurable
subset of `J`. The images of disjoint measurable subsets of an injective parameter set are disjoint
and measurable by the Lusin–Souslin theorem, so the local equalities add up.

## Main statements

* `TauCeti.Manifold.hausdorffMeasure_image_le_setLIntegral`: the trace measure of `γ '' B` is at
  most the integral of the speed over `B`.
* `TauCeti.Manifold.hausdorffMeasure_image_eq_setLIntegral`: equality on a measurable set on which
  `γ` is injective.
* `TauCeti.Manifold.restrict_map_withDensity_enorm_curveVelocity_eq_hausdorffMeasure` and
  `TauCeti.Manifold.map_withDensity_enorm_curveVelocity_eq_hausdorffMeasure`: the speed-weighted
  Lebesgue measure on an injective parameter set is carried by the curve to the trace measure.
* `TauCeti.Manifold.lintegral_image_eq_lintegral_enorm_curveVelocity_mul`: the weighted area
  formula.

## References

* H. Federer, *Geometric Measure Theory*, Theorem 2.10.13 and Section 3.2.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  Section 3.3.
* The measure-theoretic statements, and the passage from the identity of measures to the weighted
  formula, follow the Euclidean area formula for injective parametrizations in
  `TauCeti.MeasureTheory.Function.AreaFormula.Integral`, namely
  `TauCeti.restrict_map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure` and
  `TauCeti.lintegral_image_eq_lintegral_normDet_fderiv_mul`, with the speed of the curve in place
  of the Jacobian.
-/

public section

open Bundle Filter Function MeasureTheory Set Topology
open scoped ENNReal Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  {γ : ℝ → M} {O : Set ℝ}

variable [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M]

/-- On a compact interval inside the parameter set, the trace measure is at most the length. -/
private theorem hausdorffMeasure_image_Icc_le (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O) {p q : ℝ}
    (hpq : Icc p q ⊆ O) :
    μH[1] (γ '' Icc p q) ≤ ∫⁻ s in Ioo p q, ‖curveVelocity I γ s‖ₑ := by
  calc μH[1] (γ '' Icc p q) ≤ eVariationOn γ (Icc p q) := eVariationOn.hausdorffMeasure_image_le _ _
    _ = Manifold.pathELength I γ p q := eVariationOn_eq_pathELength (hγ.mono hpq)
    _ = _ := pathELength_eq_setLIntegral_enorm_curveVelocity_Ioo

/-- The upper bound of the area formula on the part of a measurable set lying in a compact
interval inside the parameter set. -/
private theorem hausdorffMeasure_image_inter_Icc_le (hO : IsOpen O)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O) {u v : ℝ} (huv : Icc u v ⊆ O) {B : Set ℝ}
    (hB : MeasurableSet B) :
    μH[1] (γ '' (B ∩ Icc u v)) ≤ ∫⁻ s in B ∩ Icc u v, ‖curveVelocity I γ s‖ₑ := by
  set ν := (volume.restrict (Icc u v)).withDensity fun s ↦ ‖curveVelocity I γ s‖ₑ
  have hν {s : Set ℝ} (hs : MeasurableSet s) :
      ν s = ∫⁻ t in s ∩ Icc u v, ‖curveVelocity I γ t‖ₑ := by
    rw [withDensity_apply _ hs, Measure.restrict_restrict hs]
  have key := OuterMeasure.le_measure_of_Ioc_le
    (OuterMeasure.restrict (Icc u v) (OuterMeasure.comap γ μH[1].toOuterMeasure)) ν
    (fun t ↦ by
      rw [hν measurableSet_Iic]
      exact ((lintegral_mono_set inter_subset_right).trans_lt
        (hγ.setLIntegral_enorm_curveVelocity_lt_top hO isCompact_Icc huv)).ne)
    (fun a b ↦ ?_) hB
  · rwa [OuterMeasure.restrict_apply, OuterMeasure.comap_apply, Measure.coe_toOuterMeasure,
      hν hB] at key
  · rw [OuterMeasure.restrict_apply, OuterMeasure.comap_apply, Measure.coe_toOuterMeasure,
      hν measurableSet_Ioc]
    calc μH[1] (γ '' (Ioc a b ∩ Icc u v)) ≤ μH[1] (γ '' Icc (max a u) (min b v)) :=
          measure_mono (image_mono fun t ht ↦
            ⟨max_le ht.1.1.le ht.2.1, le_min ht.1.2 ht.2.2⟩)
      _ ≤ ∫⁻ s in Ioo (max a u) (min b v), ‖curveVelocity I γ s‖ₑ :=
          hausdorffMeasure_image_Icc_le hγ
            ((Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)).trans huv)
      _ ≤ ∫⁻ s in Ioc a b ∩ Icc u v, ‖curveVelocity I γ s‖ₑ := lintegral_mono_set fun t ht ↦
          ⟨⟨(le_max_left _ _).trans_lt ht.1, ht.2.le.trans (min_le_left _ _)⟩,
            (le_max_right _ _).trans ht.1.le, ht.2.le.trans (min_le_right _ _)⟩

/-- **The area formula for curves, upper bound.** For a `C¹` curve `γ` on an open parameter set
`O` and a measurable `B ⊆ O`, the one-dimensional Hausdorff measure of `γ '' B` is at most the
integral of the speed of `γ` over `B`. No injectivity is needed. -/
theorem hausdorffMeasure_image_le_setLIntegral (hO : IsOpen O) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O)
    {B : Set ℝ} (hB : MeasurableSet B) (hBO : B ⊆ O) :
    μH[1] (γ '' B) ≤ ∫⁻ s in B, ‖curveVelocity I γ s‖ₑ := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · simp
  choose! a b _ hab hsub using fun x (hx : x ∈ B) ↦
    exists_Icc_mem_subset_of_mem_nhds (hO.mem_nhds (hBO hx))
  obtain ⟨D, hDm, hDd, hBD, hDN⟩ := exists_disjoint_measurableSet_cover_of_mem_nhds hne
    (fun x ↦ Icc (a x) (b x)) hab fun _ _ ↦ measurableSet_Icc
  have hB' : B = ⋃ n, B ∩ D n := by rw [← inter_iUnion, inter_eq_left.2 hBD]
  calc μH[1] (γ '' B) = μH[1] (⋃ n, γ '' (B ∩ D n)) := by rw [← image_iUnion, ← hB']
    _ ≤ ∑' n, μH[1] (γ '' (B ∩ D n)) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ s in B ∩ D n, ‖curveVelocity I γ s‖ₑ := tsum_le_tsum fun n ↦ by
        obtain ⟨x, hx, hDx⟩ := hDN n
        have := hausdorffMeasure_image_inter_Icc_le hO hγ (hsub x hx) (hB.inter (hDm n))
        rwa [inter_eq_left.2 (inter_subset_right.trans hDx)] at this
    _ = ∫⁻ s in B, ‖curveVelocity I γ s‖ₑ := by
        rw [← lintegral_iUnion (fun n ↦ hB.inter (hDm n))
          fun i j hij ↦ (hDd hij).mono inter_subset_right inter_subset_right, ← hB']

/-- The lower bound of the area formula on measurable subsets of a compact interval on which the
curve is injective. -/
private theorem setLIntegral_le_hausdorffMeasure_image (hO : IsOpen O)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O) {u v : ℝ} (huv : Icc u v ⊆ O) (hinj : InjOn γ (Icc u v))
    {B : Set ℝ} (hB : MeasurableSet B) (hBJ : B ⊆ Icc u v) :
    ∫⁻ s in B, ‖curveVelocity I γ s‖ₑ ≤ μH[1] (γ '' B) := by
  have hJ : μH[1] (γ '' Icc u v) = ∫⁻ s in Icc u v, ‖curveVelocity I γ s‖ₑ := by
    rw [← (hγ.continuousOn.mono huv).eVariationOn_eq_hausdorffMeasure_image
      (hinj.mono Ioo_subset_Icc_self), eVariationOn_eq_pathELength (hγ.mono huv),
      pathELength_eq_setLIntegral_enorm_curveVelocity_Icc]
  have hfin : ∫⁻ s in Icc u v \ B, ‖curveVelocity I γ s‖ₑ ≠ ∞ :=
    ((lintegral_mono_set sdiff_subset).trans_lt
      (hγ.setLIntegral_enorm_curveVelocity_lt_top hO isCompact_Icc huv)).ne
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc (∫⁻ s in B, ‖curveVelocity I γ s‖ₑ) + ∫⁻ s in Icc u v \ B, ‖curveVelocity I γ s‖ₑ
        = ∫⁻ s in Icc u v, ‖curveVelocity I γ s‖ₑ := by
          rw [← lintegral_union (measurableSet_Icc.diff hB) disjoint_sdiff_right,
            union_sdiff_cancel hBJ]
    _ = μH[1] (γ '' Icc u v) := hJ.symm
    _ ≤ μH[1] (γ '' B) + μH[1] (γ '' (Icc u v \ B)) :=
          le_of_eq_of_le (by rw [← image_union, union_sdiff_cancel hBJ]) (measure_union_le _ _)
    _ ≤ μH[1] (γ '' B) + ∫⁻ s in Icc u v \ B, ‖curveVelocity I γ s‖ₑ := by
          gcongr
          exact hausdorffMeasure_image_le_setLIntegral hO hγ (measurableSet_Icc.diff hB)
            (sdiff_subset.trans huv)

/-- **The area formula for injective curves.** For a `C¹` curve `γ` on an open parameter set `O`
and a measurable `A ⊆ O` on which `γ` is injective, the one-dimensional Hausdorff measure of
`γ '' A` is the integral of the speed of `γ` over `A`. -/
theorem hausdorffMeasure_image_eq_setLIntegral (hO : IsOpen O) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O)
    {A : Set ℝ} (hA : MeasurableSet A) (hAO : A ⊆ O) (hinj : InjOn γ A) :
    μH[1] (γ '' A) = ∫⁻ s in A, ‖curveVelocity I γ s‖ₑ := by
  refine (hausdorffMeasure_image_le_setLIntegral hO hγ hA hAO).antisymm ?_
  set S := {s ∈ A | curveVelocity I γ s ≠ 0}
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine le_of_eq_of_le ((setLIntegral_congr_fun hA fun s hs ↦ ?_).trans lintegral_zero)
      zero_le
    by_contra hne
    exact hS.subset ⟨hs, fun h ↦ hne (by simp [h])⟩
  have hloc (x : ℝ) (hx : x ∈ S) :
      ∃ a b, Icc a b ∈ 𝓝 x ∧ Icc a b ⊆ O ∧ InjOn γ (Icc a b) := by
    have hxO := hO.mem_nhds (hAO hx.1)
    obtain ⟨t, ht, htinj⟩ :=
      (hγ.contMDiffAt hxO).exists_mem_nhds_injOn_of_curveVelocity_ne_zero one_ne_zero hx.2
    obtain ⟨a, b, -, hab, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (inter_mem ht hxO)
    exact ⟨a, b, hab, fun s hs ↦ (hsub hs).2, htinj.mono fun s hs ↦ (hsub hs).1⟩
  choose! a b hab hsub hinjab using hloc
  obtain ⟨D, hDm, hDd, hSD, hDN⟩ := exists_disjoint_measurableSet_cover_of_mem_nhds hS
    (fun x ↦ Icc (a x) (b x)) hab fun _ _ ↦ measurableSet_Icc
  have hzero : ∫⁻ s in A \ ⋃ n, D n, ‖curveVelocity I γ s‖ₑ = 0 := by
    refine (setLIntegral_congr_fun (hA.diff (.iUnion hDm)) fun s hs ↦ ?_).trans lintegral_zero
    by_contra hne
    exact hs.2 (hSD ⟨hs.1, fun h ↦ hne (by simp [h])⟩)
  have hDinj (n : ℕ) : InjOn γ (A ∩ D n) := hinj.mono inter_subset_left
  calc ∫⁻ s in A, ‖curveVelocity I γ s‖ₑ
        = ∫⁻ s in ⋃ n, A ∩ D n, ‖curveVelocity I γ s‖ₑ := by
          rw [← lintegral_inter_add_sdiff _ A (.iUnion hDm), hzero, add_zero, inter_iUnion]
    _ = ∑' n, ∫⁻ s in A ∩ D n, ‖curveVelocity I γ s‖ₑ :=
          lintegral_iUnion (fun n ↦ hA.inter (hDm n))
            (fun i j hij ↦ (hDd hij).mono inter_subset_right inter_subset_right) _
    _ ≤ ∑' n, μH[1] (γ '' (A ∩ D n)) := tsum_le_tsum fun n ↦ by
          obtain ⟨x, hx, hDx⟩ := hDN n
          exact setLIntegral_le_hausdorffMeasure_image hO hγ (hsub x hx) (hinjab x hx)
            (hA.inter (hDm n)) (inter_subset_right.trans hDx)
    _ = μH[1] (⋃ n, γ '' (A ∩ D n)) := by
          refine (measure_iUnion (fun i j hij ↦ ?_) fun n ↦ ?_).symm
          · refine Set.disjoint_left.2 ?_
            rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
            exact (hDd hij).ne_of_mem hs.2 ht.2 (hinj hs.1 ht.1 hts.symm)
          · exact (hA.inter (hDm n)).image_of_continuousOn_injOn
              (hγ.continuousOn.mono (inter_subset_left.trans hAO)) (hDinj n)
    _ ≤ μH[1] (γ '' A) := measure_mono (iUnion_subset fun n ↦ image_mono inter_subset_left)

/-- **The area formula for injective curves, as an identity of measures.** For a `C¹` curve `γ`
on an open parameter set `O` and a measurable `A ⊆ O` on which `γ` is injective, the restriction
of `γ` to `A` carries Lebesgue measure on `A`, weighted by the speed of `γ`, to the
one-dimensional Hausdorff measure restricted to `γ '' A`. -/
theorem restrict_map_withDensity_enorm_curveVelocity_eq_hausdorffMeasure (hO : IsOpen O)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O) {A : Set ℝ} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hinj : InjOn γ A) :
    Measure.map (A.domRestrict γ)
        (Measure.comap (↑) (volume.withDensity fun s ↦ ‖curveVelocity I γ s‖ₑ)) =
      μH[1].restrict (γ '' A) := by
  have hemb := ContinuousOn.measurableEmbedding hA (hγ.continuousOn.mono hAO) hinj
  ext T hT
  have hpre : ((↑) : A → ℝ) '' (A.domRestrict γ ⁻¹' T) = A ∩ γ ⁻¹' T :=
    Subtype.image_preimage_coe A (γ ⁻¹' T)
  have hmeas : MeasurableSet (A ∩ γ ⁻¹' T) := hpre ▸ hA.subtype_image (hemb.measurable hT)
  rw [Measure.map_apply hemb.measurable hT, Measure.restrict_apply hT,
    Measure.comap_apply _ Subtype.coe_injective (fun _ ↦ hA.subtype_image) _
      (hemb.measurable hT), hpre, withDensity_apply _ hmeas,
    ← hausdorffMeasure_image_eq_setLIntegral hO hγ hmeas (inter_subset_left.trans hAO)
      (hinj.mono inter_subset_left), image_inter_preimage, inter_comm]

/-- **The area formula for injective curves, as a pushforward.** For a `C¹` curve `γ` on an open
parameter set `O` and a measurable `A ⊆ O` on which `γ` is injective, the pushforward along `γ` of
Lebesgue measure on `A`, weighted by the speed of `γ`, is the one-dimensional Hausdorff measure
restricted to `γ '' A`. The curve need not be measurable outside `O`. -/
theorem map_withDensity_enorm_curveVelocity_eq_hausdorffMeasure (hO : IsOpen O)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O) {A : Set ℝ} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hinj : InjOn γ A) :
    Measure.map γ ((volume.restrict A).withDensity fun s ↦ ‖curveVelocity I γ s‖ₑ) =
      μH[1].restrict (γ '' A) := by
  have hγA : AEMeasurable γ (Measure.map (↑) (Measure.comap ((↑) : A → ℝ)
      (volume.withDensity fun s ↦ ‖curveVelocity I γ s‖ₑ))) := by
    rw [map_comap_subtype_coe hA]
    exact (hγ.continuousOn.mono hAO).aemeasurable hA
  rw [← restrict_withDensity hA, ← map_comap_subtype_coe hA,
    hγA.map_map_of_aemeasurable measurable_subtype_coe.aemeasurable]
  exact restrict_map_withDensity_enorm_curveVelocity_eq_hausdorffMeasure hO hγ hA hAO hinj

/-- **The weighted area formula for injective curves.** For a `C¹` curve `γ` on an open parameter
set `O`, a measurable `A ⊆ O` on which `γ` is injective, and any weight `g`, the integral of `g`
over `γ '' A` against the one-dimensional Hausdorff measure is the integral over `A` of
`g ∘ γ` weighted by the speed of `γ`. The weight need not be measurable. -/
theorem lintegral_image_eq_lintegral_enorm_curveVelocity_mul (hO : IsOpen O)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ O) {A : Set ℝ} (hA : MeasurableSet A) (hAO : A ⊆ O)
    (hinj : InjOn γ A) (g : M → ℝ≥0∞) :
    ∫⁻ y in γ '' A, g y ∂μH[1] = ∫⁻ s in A, ‖curveVelocity I γ s‖ₑ * g (γ s) := by
  have hspeed : AEMeasurable (fun s ↦ ‖curveVelocity I γ s‖ₑ) (volume.restrict A) := by
    simpa only [ofReal_norm] using
      (((hγ.continuousOn_norm_curveVelocity hO).mono hAO).aemeasurable hA).ennreal_ofReal
  rw [← restrict_map_withDensity_enorm_curveVelocity_eq_hausdorffMeasure hO hγ hA hAO hinj,
    (ContinuousOn.measurableEmbedding hA (hγ.continuousOn.mono hAO) hinj).lintegral_map]
  simp only [domRestrict_apply]
  rw [← (MeasurableEmbedding.subtype_coe hA).lintegral_map (fun s ↦ g (γ s)),
    map_comap_subtype_coe hA,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hspeed _ hA
      (.of_forall fun _ ↦ eNorm_lt_top)]
  simp only [Pi.mul_apply]

end TauCeti.Manifold
