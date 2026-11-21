/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.OneDimensional.ReducedBoundary
import TauCeti.Analysis.BoundedVariation.RelativeIsoperimetric
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Covering.HausdorffDensity
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Federer's structure theorem for sets of locally finite perimeter

Let `E` be a finite-dimensional real inner product space of dimension `n` carrying an additive Haar
measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`. Throughout,
`n - 1` denotes truncated natural subtraction, so when `n = 0` we have `n - 1 = 0` and `Hⁿ⁻¹`,
`μH[n - 1]`, and `μHE[n - 1]` refer to zero-dimensional Hausdorff measure. By
`TauCeti.reducedBoundary_subset_essentialBoundary`, the reduced boundary `∂*s` (`reducedBoundary`)
is contained in `Ω ∩ ∂ᵉs`, where `∂ᵉs` (`essentialBoundary`) is the measure-theoretic boundary
consisting of points at which `s` has neither density `1` nor density `0`. This file proves
**Federer's structure theorem**: the set difference `(Ω ∩ ∂ᵉs) \ ∂*s` is `Hⁿ⁻¹`-null, so `∂*s` and
`Ω ∩ ∂ᵉs` agree `Hⁿ⁻¹`-almost everywhere (`TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary`),
and at `Hⁿ⁻¹`-almost every point of `Ω` the set `s` has density `0`, `1 / 2`, or `1`
(`TauCeti.ae_hasDensityAt_zero_or_one_half_or_one`).

In dimension `n ≤ 1`, `∂*s = Ω ∩ ∂ᵉs` literally as sets
(`TauCeti.reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one`). In dimension `n ≥ 2`:

1. The Radon perimeter measure `|Dχ_s|` on `Ω` is concentrated on `∂*s`
   (`TauCeti.ae_mem_reducedBoundary`), so `((↑) : Ω → E) ⁻¹' (∂ᵉs \ ∂*s)` is `|Dχ_s|`-null.
2. Because `|Dχ_s|` is outer regular, for `Hⁿ⁻¹`-almost every point `y` of `Ω` outside `∂*s`, the
   `(n - 1)`-dimensional density `|Dχ_s|(closedBall y r) / r ^ (n - 1)` tends to `0` as `r → 0⁺`
   (`MeasureTheory.Measure.ae_tendsto_measure_closedBall_div_of_measure_eq_zero`), and hence so does
   `P(s; ball y r) / r ^ (n - 1)`
   (`TauCeti.eventually_perimeter_ball_le_variationMeasure_closedBall`).
3. By the relative isoperimetric criterion
   (`TauCeti.notMem_essentialBoundary_of_tendsto_perimeter_ball_div`), vanishing
   `(n - 1)`-dimensional perimeter density at `y ∈ Ω` forces `s` to have density `0` or `1` at
   `y`, excluding `y ∈ ∂ᵉs`; hence `Hⁿ⁻¹`-almost every point of `Ω` outside `∂*s` lies outside
   `∂ᵉs`.

## Main results

* `TauCeti.hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero` and
  `TauCeti.euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero`:
  `((Ω ∩ ∂ᵉs) \ ∂*s)` is `Hⁿ⁻¹`-null for a set of locally finite perimeter in `Ω`.
* `TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary_hausdorffMeasure` and
  `TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary`: `∂*s =ᵐ Ω ∩ ∂ᵉs` for raw and
  Euclidean-normalized `(n - 1)`-dimensional Hausdorff measure, together with finite-perimeter
  specializations `TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary_of_perimeter_ne_top` and
  `TauCeti.reducedBoundary_top_ae_eq_essentialBoundary_of_perimeter_ne_top`.
* `TauCeti.ae_hasDensityAt_of_mem_essentialBoundary` and
  `TauCeti.ae_hasDensityAt_zero_or_one_half_or_one`: `Hⁿ⁻¹`-almost every point of `Ω ∩ ∂ᵉs` has
  density `1 / 2`, and `Hⁿ⁻¹`-almost every point of `Ω` has density `0`, `1 / 2`, or `1`, together
  with finite-perimeter specializations
  `TauCeti.ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_ne_top` and
  `TauCeti.ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_top_ne_top`.

## References

* H. Federer, *Geometric Measure Theory*, §4.5.6.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 16.2.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.8, Theorem 5.17.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.61.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric Module
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E}

/-- Federer's null-difference estimate in dimension `n ≥ 2`: for `μH[n - 1]`-almost every point of
`Ω` outside `∂*s`, `|Dχ_s|` has zero `(n - 1)`-dimensional density, forcing `μH[n - 1]`-almost
every point of `Ω` outside `∂*s` to lie outside `∂ᵉs` as well. -/
private theorem hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero_of_two_le
    (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μH[((finrank ℝ E - 1 : ℕ) : ℝ)]
      (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 := by
  set d : ℕ := finrank ℝ E - 1
  set lam := variationMeasure μ Ω (s.indicator 1)
  set A : Set Ω := ((↑) : Ω → E) ⁻¹' (essentialBoundary μ s \ reducedBoundary μ Ω s) with hA
  have himg : ((↑) : Ω → E) '' A =
      ((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s := by
    rw [hA, Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_comm,
      ← Set.inter_sdiff_assoc]
  rw [← himg, isometry_subtypeVal.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg d)),
    measure_eq_zero_iff_ae_notMem]
  have hlamA : lam A = 0 :=
    measure_mono_null (fun _ hy => hy.2) (ae_iff.1 ae_mem_reducedBoundary)
  have hs : NullMeasurableSet s (μ.restrict Ω) :=
    (aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable
  have h20 : (2 : ℝ≥0∞) ^ d ≠ 0 := by simp
  have h2t : (2 : ℝ≥0∞) ^ d ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  filter_upwards [lam.ae_tendsto_measure_closedBall_div_of_measure_eq_zero hlamA] with y hy hyA
  have hlam0 : Tendsto (fun r => lam (closedBall y r) / ENNReal.ofReal r ^ d) (𝓝[>] 0) (𝓝 0) := by
    have hmul : Tendsto (fun r => (lam (closedBall y r) / ENNReal.ofReal (2 * r) ^ (d : ℝ)) *
        (2 : ℝ≥0∞) ^ d) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const (hy hyA) (.inr h2t)
    refine hmul.congr' (eventually_mem_nhdsWithin.mono fun r (_ : 0 < r) => ?_)
    dsimp only
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_pow,
      mul_comm ((2 : ℝ≥0∞) ^ d), ← ENNReal.mul_div_right_comm,
      ENNReal.mul_div_mul_right _ _ h20 h2t]
  have hP0 : Tendsto (fun r => perimeter μ ⟨ball (y : E) r, isOpen_ball⟩ s /
      ENNReal.ofReal r ^ d) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlam0
      (.of_forall fun _ => zero_le)
      ((eventually_perimeter_ball_le_variationMeasure_closedBall hu hfin y.property).mono
        fun r hr => by
        rw [Subtype.preimage_closedBall] at hr
        exact ENNReal.div_le_div_right hr _)
  exact notMem_essentialBoundary_of_tendsto_perimeter_ball_div hn hs y.property hP0 hyA.1

/-- **Federer's structure theorem, null-difference form (raw Hausdorff measure).** For a set `s` of
locally finite perimeter in an open set `Ω` against an additive Haar measure `μ`, the part of the
essential boundary in `Ω` outside the reduced boundary is `μH[n - 1]`-null (`n = dim E`). -/
theorem hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μH[((finrank ℝ E - 1 : ℕ) : ℝ)]
      (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 := by
  rcases le_or_gt (finrank ℝ E) 1 with hn | hn
  · rw [← reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one hn hu hfin, sdiff_self,
      measure_empty]
  · exact hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero_of_two_le
      hn hu hfin

/-- **Federer's structure theorem, null-difference form.** For a set `s` of locally finite perimeter
in an open set `Ω` against an additive Haar measure `μ`, the part of the essential boundary in `Ω`
outside the reduced boundary is `μHE[n - 1]`-null (`n = dim E`). -/
theorem euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 :=
  Measure.euclideanHausdorffMeasure_eq_zero_iff.2
    (hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero hu hfin)

/-- **Federer's structure theorem (raw Hausdorff measure).** For a set `s` of locally finite
perimeter in an open set `Ω` against an additive Haar measure `μ`, the reduced boundary `∂*s` agrees
`μH[n - 1]`-almost everywhere with `Ω ∩ ∂ᵉs` (`n = dim E`). -/
theorem reducedBoundary_ae_eq_inter_essentialBoundary_hausdorffMeasure
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    reducedBoundary μ Ω s =ᵐ[μH[((finrank ℝ E - 1 : ℕ) : ℝ)]]
      (Ω : Set E) ∩ essentialBoundary μ s :=
  ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 (subset_inter reducedBoundary_subset
      reducedBoundary_subset_essentialBoundary), measure_empty],
    hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_eq_zero hu hfin⟩

/-- **Federer's structure theorem.** For a set `s` of locally finite perimeter in an open set `Ω`
against an additive Haar measure `μ`, the reduced boundary `∂*s` agrees `μHE[n - 1]`-almost
everywhere with `Ω ∩ ∂ᵉs` (`n = dim E`). -/
theorem reducedBoundary_ae_eq_inter_essentialBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    reducedBoundary μ Ω s =ᵐ[μHE[finrank ℝ E - 1]] (Ω : Set E) ∩ essentialBoundary μ s := by
  rw [Measure.euclideanHausdorffMeasure_def]
  exact Measure.ae_smul_measure
    (reducedBoundary_ae_eq_inter_essentialBoundary_hausdorffMeasure hu hfin) _

/-- **Federer's structure theorem** for a set of finite perimeter in `Ω`: if `s` is null-measurable
on `Ω` and `P(s; Ω) ≠ ∞`, then `∂*s =ᵐ[μHE[n - 1]] Ω ∩ ∂ᵉs` (`n = dim E`). -/
theorem reducedBoundary_ae_eq_inter_essentialBoundary_of_perimeter_ne_top
    (hs : NullMeasurableSet s (μ.restrict Ω)) (hP : perimeter μ Ω s ≠ ∞) :
    reducedBoundary μ Ω s =ᵐ[μHE[finrank ℝ E - 1]] (Ω : Set E) ∩ essentialBoundary μ s :=
  reducedBoundary_ae_eq_inter_essentialBoundary (locallyIntegrableOn_indicator_const hs 1)
    fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩

/-- **Federer's structure theorem** for a set of finite perimeter in the whole space: if `s` is
null-measurable and `P(s; ⊤) ≠ ∞`, then `∂*s =ᵐ[μHE[n - 1]] ∂ᵉs` (`n = dim E`). -/
theorem reducedBoundary_top_ae_eq_essentialBoundary_of_perimeter_ne_top
    (hs : NullMeasurableSet s μ) (hP : perimeter μ ⊤ s ≠ ∞) :
    reducedBoundary μ ⊤ s =ᵐ[μHE[finrank ℝ E - 1]] essentialBoundary μ s := by
  simpa using reducedBoundary_ae_eq_inter_essentialBoundary_of_perimeter_ne_top
    (Ω := ⊤) (hs.mono Measure.restrict_le_self) hP

/-- **Density one half almost everywhere on the essential boundary.** For a set `s` of locally
finite perimeter in `Ω` against an additive Haar measure `μ`, `s` has density `1 / 2` at
`μHE[n - 1]`-almost every point of `Ω ∩ ∂ᵉs` (`n = dim E`). -/
theorem ae_hasDensityAt_of_mem_essentialBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω → x ∈ essentialBoundary μ s → HasDensityAt μ s x (1 / 2) := by
  filter_upwards [eventuallyEqSet_iff.1
    (reducedBoundary_ae_eq_inter_essentialBoundary hu hfin)] with x hx hxΩ hxeb
  exact hasDensityAt_of_mem_reducedBoundary (hx.2 ⟨hxΩ, hxeb⟩)

/-- **Federer's `0`–`1/2`–`1` density theorem.** For a set `s` of locally finite perimeter in an
open set `Ω` against an additive Haar measure `μ`, at `μHE[n - 1]`-almost every point of `Ω` the set
`s` has density `0`, `1 / 2`, or `1` (`n = dim E`). -/
theorem ae_hasDensityAt_zero_or_one_half_or_one
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω →
      HasDensityAt μ s x 0 ∨ HasDensityAt μ s x (1 / 2) ∨ HasDensityAt μ s x 1 := by
  filter_upwards [ae_hasDensityAt_of_mem_essentialBoundary hu hfin] with x hx hxΩ
  by_cases h0 : HasDensityAt μ s x 0
  · exact .inl h0
  · by_cases h1 : HasDensityAt μ s x 1
    · exact .inr (.inr h1)
    · exact .inr (.inl (hx hxΩ
        (mem_essentialBoundary.2 ⟨mt mem_essentialInterior.1 h1, mt mem_essentialExterior.1 h0⟩)))

/-- **Federer's `0`–`1/2`–`1` density theorem** for a set of finite perimeter in `Ω`: if `s` is
null-measurable on `Ω` and `P(s; Ω) ≠ ∞`, then at `μHE[n - 1]`-almost every `x ∈ Ω` the set `s`
has density `0`, `1 / 2`, or `1`. -/
theorem ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_ne_top
    (hs : NullMeasurableSet s (μ.restrict Ω)) (hP : perimeter μ Ω s ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω →
      HasDensityAt μ s x 0 ∨ HasDensityAt μ s x (1 / 2) ∨ HasDensityAt μ s x 1 :=
  ae_hasDensityAt_zero_or_one_half_or_one (locallyIntegrableOn_indicator_const hs 1)
    fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩

/-- **Federer's `0`–`1/2`–`1` density theorem** for a set of finite perimeter in the whole space:
if `s` is null-measurable and `P(s; ⊤) ≠ ∞`, then at `μHE[n - 1]`-almost every `x : E` the set `s`
has density `0`, `1 / 2`, or `1`. -/
theorem ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_top_ne_top
    (hs : NullMeasurableSet s μ) (hP : perimeter μ ⊤ s ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1],
      HasDensityAt μ s x 0 ∨ HasDensityAt μ s x (1 / 2) ∨ HasDensityAt μ s x 1 := by
  filter_upwards [ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_ne_top (Ω := ⊤)
    (hs.mono Measure.restrict_le_self) hP] with x hx
  exact hx trivial

end TauCeti

end
