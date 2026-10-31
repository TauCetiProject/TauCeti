/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.AreaFormula.Integral
import TauCeti.MeasureTheory.Function.Jacobian.Decomposition
import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Zero Jacobians and the area formula for injective Lipschitz maps

Let `U` and `V` be finite-dimensional real inner product spaces, `m = dim U`, and let
`J f x = (fderiv ℝ f x).normDet` be the `m`-dimensional Jacobian of `f : U → V`. This file shows
that the points where `f` is not differentiable with injective derivative do not matter for the
area formula of a Lipschitz map:

* **Zero Jacobians have null images.** If `f` is differentiable at every point of a set `s` and
  `J f = 0` on `s`, then `μHE[m] (f '' s) = 0`. No Lipschitz, measurability, or injectivity
  hypothesis is needed. This is the rectangular counterpart of Mathlib's
  `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, measured by the normalized Hausdorff measure
  `μHE[m]` of the target rather than by its volume.
* **The area formula for injective Lipschitz maps.** If `f` is Lipschitz and injective on a
  measurable set `s`, then `∫⁻ x in s, J f x = μHE[m] (f '' s)`, with a weighted form for an
  arbitrary nonnegative weight on the target. Unlike
  `MeasureTheory.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`, neither
  differentiability nor injectivity of the derivative is assumed.

## The argument

For the first statement, `f` is lifted to `g ε x = (f x, ε x)` in the Euclidean product of `V` and
`U`. For `ε ≠ 0` the lift is injective with injective derivative, so the injective area formula
applies to it, and `f` is the composition of `g ε` with the `1`-Lipschitz first projection. Hence
`μHE[m] (f '' s) ≤ ∫⁻ x in s, J (g ε) x`. As `ε → 0`, the derivative of `g ε` tends to the
derivative of `x ↦ (f x, 0)`, whose Jacobian is `J f x = 0`. On bounded pieces of `s` where
`fderiv ℝ f` is bounded, dominated convergence shows that the integrals tend to zero.

For the second statement, Rademacher's theorem `LipschitzWith.ae_differentiableAt` makes the set
of nondifferentiability points null, so its image is null, while the first statement makes the
image of the points with zero Jacobian null. On the remaining points the derivative is injective
and the regular injective area formula applies.

## Main declarations

* `TauCeti.euclideanHausdorffMeasure_image_eq_zero_of_normDet_fderiv_eq_zero`: zero Jacobians
  have null images.
* `LipschitzWith.euclideanHausdorffMeasure_image_setOf_normDet_fderiv_eq_zero`: the image of the
  set where the Jacobian of a Lipschitz map vanishes is null.
* `LipschitzWith.exists_bilipschitz_cover`: countably many disjoint Borel patches with Lipschitz
  inverse coordinates cover the image up to a null set, using
  `TauCeti.exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt` on the regular points.
* `LipschitzWith.lintegral_image_eq_lintegral_normDet_fderiv_mul`: the weighted area formula for
  a Lipschitz map injective on a measurable set.
* `LipschitzWith.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`: the area formula
  for a Lipschitz map injective on a measurable set.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  Section 3.3 (the area formula), whose proof of the zero Jacobian statement for Lipschitz maps,
  by lifting to `x ↦ (f x, ε x)`, this file follows.
-/

public section

open MeasureTheory Measure Set Filter Metric Module Function
open scoped NNReal ENNReal Topology

namespace TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U}

omit [MeasurableSpace V] [BorelSpace V] in
/-- The set of differentiability points with nonzero geometric Jacobian is Borel measurable. -/
theorem measurableSet_setOf_differentiableAt_normDet_ne_zero (f : U → V) :
    MeasurableSet {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0} :=
  (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ f)) measurable_const).compl

/-- The zero Jacobian statement on a bounded measurable piece on which the derivative is
bounded. -/
private theorem euclideanHausdorffMeasure_image_eq_zero_of_bounded (hs : MeasurableSet s)
    (R : ℝ) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (h0 : ∀ x ∈ s, (fderiv ℝ f x).normDet = 0)
    (hR : ∀ x ∈ s, ‖x‖ ≤ R) (hR' : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ R) :
    μHE[finrank ℝ U] (f '' s) = 0 := by
  -- Lift `f` to `x ↦ ι₁ (f x) + ε • ι₂ x = (f x, ε x)` in the Euclidean product of `V` and `U`;
  -- its derivative at `x` is `D ε (fderiv ℝ f x)`.
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V U).symm.toContinuousLinearMap
  let ι₁ : V →L[ℝ] WithLp 2 (V × U) := e ∘L ContinuousLinearMap.inl ℝ V U
  let ι₂ : U →L[ℝ] WithLp 2 (V × U) := e ∘L ContinuousLinearMap.inr ℝ V U
  let D : ℝ → (U →L[ℝ] V) → U →L[ℝ] WithLp 2 (V × U) := fun ε A => ι₁ ∘L A + ε • ι₂
  have hDsnd (ε : ℝ) (A : U →L[ℝ] V) (v : U) : (D ε A v).snd = ε • v := by
    simp [D, ι₁, ι₂, e]
  -- For `ε ≠ 0`, the lift is injective with injective derivative, and `f` is its first component.
  have hle (ε : ℝ) (hε : ε ≠ 0) : μHE[finrank ℝ U] (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal (D ε (fderiv ℝ f x)).normDet :=
    euclideanHausdorffMeasure_image_le_lintegral_normDet hs
      (LipschitzWith.of_edist_le WithLp.edist_fst_le).lipschitzOnWith
      (fun x _ => by simp [ι₁, ι₂, e])
      (fun x hx => (ι₁.hasFDerivAt.comp x (hd x hx).hasFDerivAt).add
        (ι₂.hasFDerivAt.const_smul ε))
      (fun x _ v w h => smul_right_injective U hε (by simpa [hDsnd] using congrArg WithLp.snd h))
      (fun x _ y _ h => smul_right_injective U hε
        (by simpa [ι₁, ι₂, e] using congrArg WithLp.snd h))
  -- The Jacobian of `D ε A` is bounded for `|ε| ≤ 1` and `‖A‖ ≤ R`, by compactness.
  have hcont : Continuous fun B : U →L[ℝ] WithLp 2 (V × U) => B.normDet :=
    ContinuousLinearMap.continuous_normDet
  have hDcont : Continuous fun p : ℝ × (U →L[ℝ] V) => D p.1 p.2 :=
    (continuous_const.clm_comp continuous_snd).add (continuous_fst.smul continuous_const)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : U →L[ℝ] V) R))
    |>.exists_bound_of_continuousOn (hcont.comp hDcont).continuousOn
  have hlim : Tendsto (fun ε => ∫⁻ x in s, ENNReal.ofReal (D ε (fderiv ℝ f x)).normDet) (𝓝 0)
      (𝓝 (∫⁻ x in s, ENNReal.ofReal (D 0 (fderiv ℝ f x)).normDet)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => ENNReal.ofReal C)
      (Eventually.of_forall fun ε => ?_) ?_ ?_ (Eventually.of_forall fun x => ?_)
    · exact ENNReal.measurable_ofReal.comp ((hcont.comp (continuous_const.clm_comp
        continuous_id |>.add continuous_const)).measurable.comp (measurable_fderiv ℝ f))
    · filter_upwards [Icc_mem_nhds (neg_one_lt_zero : (-1 : ℝ) < 0) zero_lt_one] with ε hε
      refine (ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => ?_)
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        (hC (ε, fderiv ℝ f x) ⟨hε, mem_closedBall_zero_iff.2 (hR' x hx)⟩))
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((measure_mono fun x hx =>
        mem_closedBall_zero_iff.2 (hR x hx)).trans_lt measure_closedBall_lt_top).ne
    · exact (ENNReal.continuous_ofReal.comp (hcont.comp
        (hDcont.comp (continuous_id.prodMk continuous_const)))).tendsto 0
  -- At `ε = 0` the Jacobian is that of `x ↦ (f x, 0)`, which vanishes on `s`.
  have hzero : ∫⁻ x in s, ENNReal.ofReal (D 0 (fderiv ℝ f x)).normDet = 0 := by
    refine (setLIntegral_congr_fun hs fun x hx => ?_).trans lintegral_zero
    have h : (D 0 (fderiv ℝ f x) : U →ₗ[ℝ] WithLp 2 (V × U)) =
        (ι₁ : V →ₗ[ℝ] WithLp 2 (V × U)) ∘ₗ (fderiv ℝ f x : U →ₗ[ℝ] V) := by
      simp [D]
    rw [h, LinearMap.normDet_comp]
    simp [h0 x hx]
  rw [hzero] at hlim
  exact le_antisymm (ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)))
    (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)) bot_le

/-- **Zero Jacobians have null images.** Let `U` and `V` be finite-dimensional real inner product
spaces. If `f : U → V` is differentiable at every point of `s` and its `dim U`-dimensional
Jacobian `(fderiv ℝ f x).normDet` vanishes there, then `f '' s` is null for the
`dim U`-dimensional Euclidean Hausdorff measure. The set `s` need not be measurable. -/
theorem euclideanHausdorffMeasure_image_eq_zero_of_normDet_fderiv_eq_zero
    (hd : ∀ x ∈ s, DifferentiableAt ℝ f x) (h0 : ∀ x ∈ s, (fderiv ℝ f x).normDet = 0) :
    μHE[finrank ℝ U] (f '' s) = 0 := by
  -- Cover `s` by measurable pieces on which `‖x‖` and `‖fderiv ℝ f x‖` are bounded.
  let t : ℕ → Set U := fun n => {x | DifferentiableAt ℝ f x} ∩ {x | (fderiv ℝ f x).normDet = 0} ∩
    {x | ‖x‖ ≤ n} ∩ {x | ‖fderiv ℝ f x‖ ≤ n}
  have ht (n : ℕ) : MeasurableSet (t n) :=
    (((measurableSet_of_differentiableAt ℝ f).inter
      (measurableSet_eq_fun (ContinuousLinearMap.continuous_normDet.measurable.comp
        (measurable_fderiv ℝ f)) measurable_const)).inter
      (measurableSet_le measurable_norm measurable_const)).inter
      (measurableSet_le (measurable_fderiv ℝ f).norm measurable_const)
  have hst : s ⊆ ⋃ n, t n := fun x hx => by
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ‖fderiv ℝ f x‖)
    exact mem_iUnion.2 ⟨n, ⟨⟨hd x hx, h0 x hx⟩, (le_max_left _ _).trans hn⟩,
      (le_max_right _ _).trans hn⟩
  refine measure_mono_null (image_mono hst) ?_
  rw [image_iUnion]
  exact measure_iUnion_null fun n => euclideanHausdorffMeasure_image_eq_zero_of_bounded (ht n) n
    (fun x hx => hx.1.1.1) (fun x hx => hx.1.1.2) (fun x hx => hx.1.2) (fun x hx => hx.2)

end TauCeti

namespace LipschitzWith

open TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] {f : U → V} {s : Set U}
  {K : ℝ≥0}

/-- A Lipschitz map sends the complement of its regular points, where it is differentiable with
nonzero Jacobian, to a null set. -/
theorem euclideanHausdorffMeasure_image_compl_setOf_regular (hf : LipschitzWith K f) :
    μHE[finrank ℝ U]
      (f '' {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}ᶜ) = 0 := by
  -- By Rademacher's theorem, the nondifferentiability points form a null set.
  have hN : μHE[finrank ℝ U] {x | ¬DifferentiableAt ℝ f x} = 0 := by
    rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
    exact ae_iff.1 hf.ae_differentiableAt
  have hsub : {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}ᶜ ⊆
      {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet = 0} ∪
        {x | ¬DifferentiableAt ℝ f x} := fun x hx => by
    by_cases h : DifferentiableAt ℝ f x
    exacts [Or.inl ⟨h, not_not.1 fun h' => hx ⟨h, h'⟩⟩, Or.inr h]
  refine measure_mono_null ((image_mono hsub).trans (image_union _ _ _).subset)
    (measure_union_null ?_ ?_)
  · exact euclideanHausdorffMeasure_image_eq_zero_of_normDet_fderiv_eq_zero (fun x hx => hx.1)
      (fun x hx => hx.2)
  · exact le_antisymm ((hf.lipschitzOnWith.euclideanHausdorffMeasure_image_le _).trans
      (by rw [hN, mul_zero])) bot_le

/-- The image of a Lipschitz map is covered up to a null set by images of countably many
disjoint Borel sets on which the map has a Lipschitz inverse. The forward Lipschitz bound
is inherited from the original map. -/
theorem exists_bilipschitz_cover (hf : LipschitzWith K f) :
    ∃ A : ℕ → Set U, (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧
      (∀ n, ∃ L : ℝ≥0, AntilipschitzWith L ((A n).domRestrict f)) ∧
      μHE[finrank ℝ U] (range f \ ⋃ n, f '' A n) = 0 := by
  let G := {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}
  have hG : MeasurableSet G := measurableSet_setOf_differentiableAt_normDet_ne_zero f
  have hi (x : U) (hx : x ∈ G) : Injective (fderiv ℝ f x) :=
    ((fderiv ℝ f x).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hx.2
  obtain ⟨A, K', L', hAm, hdisj, hcover, hbi⟩ :=
    TauCeti.exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt hG
      (fun x (hx : x ∈ G) ↦ hx.1.hasFDerivAt.hasFDerivWithinAt) hi
  refine ⟨A, hAm, hdisj, fun n ↦ ⟨L' n, (hbi n).2⟩, ?_⟩
  refine measure_mono_null ?_ hf.euclideanHausdorffMeasure_image_compl_setOf_regular
  rintro y ⟨⟨x, rfl⟩, hy⟩
  refine ⟨x, ?_, rfl⟩
  intro hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm.subset hx)
  exact hy (mem_iUnion.mpr ⟨n, x, hn, rfl⟩)

/-- **Sard's lemma for Lipschitz maps.** The image of the set where the `dim U`-dimensional
Jacobian of a Lipschitz map `f : U → V` vanishes is null for the `dim U`-dimensional Euclidean
Hausdorff measure. -/
theorem euclideanHausdorffMeasure_image_setOf_normDet_fderiv_eq_zero (hf : LipschitzWith K f) :
    μHE[finrank ℝ U] (f '' {x | (fderiv ℝ f x).normDet = 0}) = 0 := by
  refine measure_mono_null (image_mono ?_) hf.euclideanHausdorffMeasure_image_compl_setOf_regular
  exact fun x hx h => h.2 hx

/-- **The weighted area formula for injective Lipschitz maps.** If `f : U → V` is Lipschitz and
injective on a measurable set `s`, then for every weight `g : V → ℝ≥0∞` the integral of `g` over
`f '' s` for the `dim U`-dimensional Euclidean Hausdorff measure is the integral over `s` of
`g ∘ f` weighted by the Jacobian `(fderiv ℝ f x).normDet`. The weight need not be measurable. -/
theorem lintegral_image_eq_lintegral_normDet_fderiv_mul (hf : LipschitzWith K f)
    (hs : MeasurableSet s) (hinj : InjOn f s) (g : V → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ U] =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * g (f x) := by
  -- Split `s` into its regular points `s ∩ G` and the rest, which contributes to neither side.
  set G := {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}
  have hG : MeasurableSet G := measurableSet_setOf_differentiableAt_normDet_ne_zero f
  have himage : f '' s =ᵐ[μHE[finrank ℝ U]] f '' (s ∩ G) := by
    rw [← inter_union_sdiff s G, image_union, inter_union_sdiff]
    exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (measure_mono_null
      (image_mono (sdiff_subset_compl _ _)) hf.euclideanHausdorffMeasure_image_compl_setOf_regular))
  have hzero : ∫⁻ x in s \ G, ENNReal.ofReal (fderiv ℝ f x).normDet * g (f x) = 0 := by
    refine (setLIntegral_congr_fun_ae (hs.diff hG) ?_).trans lintegral_zero
    filter_upwards [hf.ae_differentiableAt] with x hx hxs
    rw [not_not.1 fun h => hxs.2 ⟨hx, h⟩, ENNReal.ofReal_zero, zero_mul]
  rw [setLIntegral_congr himage, ← lintegral_inter_add_sdiff _ s hG, hzero, add_zero]
  refine TauCeti.lintegral_image_eq_lintegral_normDet_fderiv_mul (hs.inter hG)
    (fun x hx => hx.2.1) (fun x hx => ?_) (hinj.mono inter_subset_left) g
  exact ((fderiv ℝ f x).toLinearMap.normDet_ne_zero_tfae.out 1 5).mp hx.2.2

/-- **The area formula for injective Lipschitz maps.** If `f : U → V` is Lipschitz and injective
on a measurable set `s`, then the integral over `s` of the `dim U`-dimensional Jacobian
`(fderiv ℝ f x).normDet` is the `dim U`-dimensional Euclidean Hausdorff measure of `f '' s`. -/
theorem lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image (hf : LipschitzWith K f)
    (hs : MeasurableSet s) (hinj : InjOn f s) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet = μHE[finrank ℝ U] (f '' s) := by
  simpa using (hf.lintegral_image_eq_lintegral_normDet_fderiv_mul hs hinj 1).symm

end LipschitzWith
