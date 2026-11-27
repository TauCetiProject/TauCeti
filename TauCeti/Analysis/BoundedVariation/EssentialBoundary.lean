/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary.Basic
public import TauCeti.MeasureTheory.Covering.EssentialBoundary.Basic
import TauCeti.Analysis.BoundedVariation.DeGiorgi
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates
import TauCeti.Analysis.BoundedVariation.OneDimensional.LocalClassification
import TauCeti.Analysis.BoundedVariation.RelativeIsoperimetric
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.LinearAlgebra.Dimension.FinrankOne
import TauCeti.MeasureTheory.Covering.HausdorffDensity
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The essential boundary and the reduced boundary

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`. The reduced
boundary `∂*s` (`TauCeti.reducedBoundary`) lies in the essential boundary `∂ᵉs`
(`TauCeti.essentialBoundary`, see `TauCeti.reducedBoundary_subset_essentialBoundary`), and hence
the perimeter measure `|Dχ_s|` is concentrated on `∂ᵉs` (`TauCeti.ae_mem_essentialBoundary`). This
file proves **Federer's theorem**: in `Ω` the two boundaries differ by an `Hⁿ⁻¹`-null set,

`Hⁿ⁻¹((∂ᵉs ∩ Ω) \ ∂*s) = 0`

(`TauCeti.euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero`),
where `Hⁿ⁻¹ = μHE[n - 1]` is the normalized Euclidean Hausdorff measure with `n - 1` denoting
truncated natural subtraction (so `0 - 1 = 0` when `n = 0`, where `μHE[0]` is zero-dimensional
Hausdorff / counting measure and both boundaries are empty). Equivalently, `∂ᵉs ∩ Ω` and `∂*s`
agree `Hⁿ⁻¹`-almost everywhere (`TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`). Combined
with De Giorgi's theorem `P(s; Ω) = Hⁿ⁻¹(∂*s)`
(`TauCeti.perimeter_eq_euclideanHausdorffMeasure_reducedBoundary`), this expresses the perimeter as
the measure of the essential boundary in dimension `n ≥ 2`, `P(s; Ω) = Hⁿ⁻¹(∂ᵉs ∩ Ω)`
(`TauCeti.perimeter_eq_euclideanHausdorffMeasure_essentialBoundary_inter`).

In dimension `n ≤ 1`, `∂ᵉs ∩ Ω = ∂*s` literally as sets
(`TauCeti.essentialBoundary_inter_eq_reducedBoundary_of_finrank_le_one`).

## Proof

At a point `x` of the essential boundary, the proportion of `s` in `closedBall x r` tends neither
to `0` nor to `1` as `r → 0⁺`. It depends continuously on `r`, so for some `a > 0` both `s` and
its complement fill a proportion at least `a` of arbitrarily small balls around `x`
(`TauCeti.exists_pos_frequently_ofReal_mul_measure_closedBall_le`). When `s` is null-measurable on
a neighborhood `U` of `x`, in dimension `n ≥ 2` the normalized relative isoperimetric inequality
(`TauCeti.exists_min_div_closedBall_rpow_le_mul_perimeter_div`) gives
`c r ^ (n - 1) ≤ P(s; ball x r)` for arbitrarily small `r`, with `c > 0` depending on `x`, while in
dimension `1` local constancy below unit normalized perimeter
(`TauCeti.ae_eq_empty_or_univ_of_perimeter_ball_lt`) gives the same bound with `n - 1 = 0` (and in
dimension `0` the essential boundary is empty). This needs no assumption on the perimeter of `s`
beyond null-measurability near `x`
(`TauCeti.exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball`).

The perimeter measure `|Dχ_s|` therefore has positive upper `(n - 1)`-dimensional density at every
point of `∂ᵉs ∩ Ω` (`TauCeti.exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall`).
Since `|Dχ_s|` is outer regular and carried by the reduced boundary
(`TauCeti.ae_mem_reducedBoundary`), it has `(n - 1)`-density zero at `μH[n - 1]`-almost every point
of `(∂ᵉs ∩ Ω) \ ∂*s` (`MeasureTheory.Measure.ae_tendsto_measure_closedBall_div_of_measure_eq_zero`),
forcing that difference to be `Hⁿ⁻¹`-null.

## Main results

* `TauCeti.ae_mem_essentialBoundary`: `|Dχ_s|`-almost every point of `Ω` lies in `∂ᵉs` in every
  dimension.
* `TauCeti.exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball`: in every dimension, if `s` is
  null-measurable on a neighborhood of a point `x` of its essential boundary, then
  `c r ^ (n - 1) ≤ P(s; ball x r)` for some `c > 0` and arbitrarily small `r > 0`.
* `TauCeti.notMem_essentialBoundary_of_tendsto_perimeter_ball_div`: in every dimension, if `s` is
  null-measurable on a neighborhood of `x` and `P(s; ball x r) / r ^ (n - 1) → 0` as `r → 0⁺`,
  then `x ∉ ∂ᵉs`.
* `TauCeti.exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall`: in every dimension,
  for a set `s` of locally finite perimeter in `Ω`, the perimeter measure has positive upper
  `(n - 1)`-dimensional density at every point of `∂ᵉs ∩ Ω`.
* `TauCeti.euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero`:
  **Federer's theorem** in every dimension, `Hⁿ⁻¹((∂ᵉs ∩ Ω) \ ∂*s) = 0`.
* `TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary` (and its finite-perimeter
  specialization): `∂ᵉs ∩ Ω = ∂*s` up to an `Hⁿ⁻¹`-null set in every dimension.
* `TauCeti.ae_forall_exists_hasDensityAt`: in every dimension, off an `Hⁿ⁻¹`-null set, countably
  many sets of locally finite perimeter each have density `0`, `1/2` or `1` at every point of `Ω`,
  with density `1/2` exactly on the reduced boundary.
* `TauCeti.perimeter_eq_euclideanHausdorffMeasure_essentialBoundary_inter`: in dimension `n ≥ 2`,
  the perimeter is the measure of the essential boundary, `P(s; Ω) = Hⁿ⁻¹(∂ᵉs ∩ Ω)`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Theorem 16.2.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §5.8, Lemma 5.5.
* L. Ambrosio, N. Fusco and D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.61.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E}

/-- **The perimeter measure is concentrated on the essential boundary.** Against an additive Haar
measure on a finite-dimensional real inner product space, `|Dχ_s|`-almost every point of `Ω` lies in
`∂ᵉs`. -/
theorem ae_mem_essentialBoundary :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1), (y : E) ∈ essentialBoundary μ s :=
  ae_mem_reducedBoundary.mono fun _ hy => reducedBoundary_subset_essentialBoundary hy

/-- Normalized perimeter lower bound at the essential boundary: if `s` is null-measurable on a
neighborhood `U` of `x ∈ ∂ᵉs`, then `c ≤ P(s; ball x r) / r ^ (n - 1)` for some `c > 0` and
arbitrarily small `r > 0`. -/
private theorem exists_pos_frequently_le_perimeter_ball_div
    {U : Set E} (hU : U ∈ 𝓝 x) (hs : NullMeasurableSet s (μ.restrict U))
    (hx : x ∈ essentialBoundary μ s) :
    ∃ c > 0, ∃ᶠ r in 𝓝[>] 0, ENNReal.ofReal c ≤
      perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  rcases lt_or_ge (finrank ℝ E) 2 with hn | hn
  · rcases subsingleton_or_finrank_eq_one_of_le_one (Nat.lt_succ_iff.1 hn) with _ | h1
    · simp at hx
    · set a := Measure.addHaarScalarFactor μ volume
      refine ⟨(a : ℝ), Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume,
        (Eventually.frequently (Ioo_mem_nhdsGT hε)).mono fun r ⟨hr0, hrε⟩ => ?_⟩
      have hsr : NullMeasurableSet s (μ.restrict (ball x r)) :=
        hs.mono (Measure.restrict_mono ((ball_subset_ball hrε.le).trans hεU) le_rfl)
      rw [h1, Nat.sub_self, pow_zero, div_one, ENNReal.ofReal_coe_nnreal]
      by_contra! hlt
      exact notMem_essentialBoundary_of_ae_eq_empty_or_univ isOpen_ball (mem_ball_self hr0)
        (ae_eq_empty_or_univ_of_perimeter_ball_lt h1 hsr hlt) hx
  · obtain ⟨a, ha, hfreq⟩ := exists_pos_frequently_ofReal_mul_measure_closedBall_le hx
    obtain ⟨C, hCtop, hC⟩ := exists_min_div_closedBall_rpow_le_mul_perimeter_div hn μ
    set C' : ℝ≥0∞ := max C 1
    have hC'top : C' ≠ ∞ := max_ne_top hCtop ENNReal.one_ne_top
    have hC'pos : 0 < C'.toReal := ENNReal.toReal_pos
      (lt_of_lt_of_le one_pos (le_max_right _ _)).ne' hC'top
    set q : ℝ := 1 - (finrank ℝ E : ℝ)⁻¹
    have hq : 0 ≤ q :=
      sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ finrank ℝ E)))
    refine ⟨a ^ q / C'.toReal, by positivity,
      (hfreq.and_eventually (Ioo_mem_nhdsGT hε)).mono fun r ⟨⟨h₁, h₂⟩, hr0, hrε⟩ => ?_⟩
    have hiso := hC hr0 (hs.mono (Measure.restrict_mono ((ball_subset_ball hrε.le).trans hεU)
      le_rfl))
    have hcb0 : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hr0).ne'
    have hcbtop : μ (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
    have hmin : ENNReal.ofReal a ≤
        min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r) := by
      rw [ENNReal.le_div_iff_mul_le (.inl hcb0) (.inl hcbtop)]
      exact le_min h₁ h₂
    rw [ENNReal.ofReal_div_of_pos hC'pos]
    refine ENNReal.div_le_of_le_mul ?_
    calc ENNReal.ofReal (a ^ q) = ENNReal.ofReal a ^ q :=
          (ENNReal.ofReal_rpow_of_nonneg ha.le hq).symm
      _ ≤ (min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) ^ q :=
          ENNReal.rpow_le_rpow hmin hq
      _ ≤ C * (perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1)) :=
          hiso
      _ ≤ ENNReal.ofReal C'.toReal *
          (perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1)) := by
          rw [ENNReal.ofReal_toReal hC'top]
          exact mul_le_mul_left (le_max_left _ _) _
      _ = (perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1)) *
          ENNReal.ofReal C'.toReal := mul_comm _ _

/-- **Perimeter lower bound at the essential boundary.** Let `s` be null-measurable on a
neighborhood `U` of a point `x` of its essential boundary. Then for some `c > 0` and arbitrarily
small radii `r > 0`, the perimeter of `s` in `ball x r` is at least `c r ^ (n - 1)`, where
`n = dim E`. -/
theorem exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball
    {U : Set E} (hU : U ∈ 𝓝 x) (hs : NullMeasurableSet s (μ.restrict U))
    (hx : x ∈ essentialBoundary μ s) :
    ∃ c > 0, ∃ᶠ r in 𝓝[>] 0,
      ENNReal.ofReal (c * r ^ (finrank ℝ E - 1)) ≤ perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
  obtain ⟨c, hc, hfreq⟩ := exists_pos_frequently_le_perimeter_ball_div hU hs hx
  refine ⟨c, hc, (hfreq.and_eventually self_mem_nhdsWithin).mono fun r ⟨hr, (hr0 : 0 < r)⟩ => ?_⟩
  have hr0_pow : ENNReal.ofReal r ^ (finrank ℝ E - 1) ≠ 0 :=
    pow_ne_zero _ (ENNReal.ofReal_pos.2 hr0).ne'
  have hrtop_pow : ENNReal.ofReal r ^ (finrank ℝ E - 1) ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_pow hr0.le]
  exact (ENNReal.le_div_iff_mul_le (.inl hr0_pow) (.inl hrtop_pow)).1 hr

/-- If `s` is null-measurable on a neighborhood `U` of `x` and
`P(s; ball x r) / r ^ (n - 1) → 0` as `r → 0⁺`, then `x` does not lie in the essential boundary
of `s`. -/
theorem notMem_essentialBoundary_of_tendsto_perimeter_ball_div
    {U : Set E} (hU : U ∈ 𝓝 x) (hs : NullMeasurableSet s (μ.restrict U))
    (htend : Tendsto (fun r : ℝ => perimeter μ ⟨ball x r, isOpen_ball⟩ s /
      ENNReal.ofReal r ^ (finrank ℝ E - 1)) (𝓝[>] 0) (𝓝 0)) :
    x ∉ essentialBoundary μ s := by
  intro hx
  obtain ⟨c, hc, hfreq⟩ := exists_pos_frequently_le_perimeter_ball_div hU hs hx
  exact (ENNReal.ofReal_pos.2 hc).not_ge (ge_of_tendsto_of_frequently htend hfreq)

/-- **The perimeter measure at the essential boundary.** For a set `s` of locally finite perimeter
in an open set `Ω` and a point `x ∈ Ω` of the essential boundary of `s`, the perimeter measure
`|Dχ_s|` has positive upper `(n - 1)`-dimensional density at `x`: for some `c > 0` and arbitrarily
small radii `r > 0`, `c r ^ (n - 1) ≤ |Dχ_s|(closedBall x r)`. -/
theorem exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞)
    (hxΩ : x ∈ Ω) (hx : x ∈ essentialBoundary μ s) :
    ∃ c > 0, ∃ᶠ r in 𝓝[>] 0, ENNReal.ofReal (c * r ^ (finrank ℝ E - 1)) ≤
      variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨c, hc, hfreq⟩ := exists_pos_frequently_ofReal_mul_pow_le_perimeter_ball
    (Ω.isOpen.mem_nhds hxΩ)
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable) hx
  exact ⟨c, hc, (hfreq.and_eventually (eventually_perimeter_ball_le_variationMeasure_closedBall
    hu hfin hxΩ)).mono fun _ h => h.1.trans h.2⟩

/-- **Federer's theorem.** For a set `s` of locally finite perimeter in an open set `Ω`, the part of
the essential boundary `∂ᵉs` in `Ω` lying off the reduced boundary `∂*s` is `μHE[n - 1]`-null,
where `n = dim E` and `n - 1` is truncated natural subtraction (so `0 - 1 = 0` when `n = 0`). -/
theorem euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] ((essentialBoundary μ s ∩ Ω) \ reducedBoundary μ Ω s) = 0 := by
  set n := finrank ℝ E
  set d : ℝ := ((n - 1 : ℕ) : ℝ)
  set lam := variationMeasure μ Ω (s.indicator 1)
  -- The points of `Ω` in the essential boundary but not in the reduced boundary.
  set A : Set Ω := (↑) ⁻¹' (essentialBoundary μ s \ reducedBoundary μ Ω s)
  have hA0 : lam A = 0 := measure_mono_null (t := {y : Ω | ↑y ∉ reducedBoundary μ Ω s})
    (fun _ hy => hy.2) (ae_iff.1 ae_mem_reducedBoundary)
  have hAe : ∀ᵐ y ∂μH[d], y ∈ A →
      Tendsto (fun r => lam (closedBall y r) / ENNReal.ofReal (2 * r) ^ d) (𝓝[>] 0) (𝓝 0) :=
    Measure.ae_tendsto_measure_closedBall_div_of_measure_eq_zero lam hA0
  have hA : μH[d] A = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hAe)
    intro hlim
    obtain ⟨c, hc, hfreq⟩ := exists_pos_frequently_ofReal_mul_pow_le_variationMeasure_closedBall
      hu hfin y.property hy.1
    simp_rw [Subtype.preimage_closedBall] at hfreq
    have hfreq' := Measure.frequently_ofReal_div_mul_rpow_le_measure_closedBall hfreq
    have hc_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (c / 2 ^ (n - 1)) :=
      ENNReal.ofReal_pos.2 (by positivity)
    have hfreq_div : ∃ᶠ r in 𝓝[>] 0, ENNReal.ofReal (c / 2 ^ (n - 1)) ≤
        lam (closedBall y r) / ENNReal.ofReal (2 * r) ^ d := by
      refine (hfreq'.and_eventually self_mem_nhdsWithin).mono fun r ⟨hr, (hr0 : 0 < r)⟩ => ?_
      have h2r0 : ENNReal.ofReal (2 * r) ^ d ≠ 0 :=
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_ne_top).ne'
      have h2rtop : ENNReal.ofReal (2 * r) ^ d ≠ ∞ :=
        ENNReal.rpow_ne_top_of_nonneg (Nat.cast_nonneg _) ENNReal.ofReal_ne_top
      exact (ENNReal.le_div_iff_mul_le (.inl h2r0) (.inl h2rtop)).2 hr
    exact hc_pos.not_ge (ge_of_tendsto_of_frequently (hlim hy) hfreq_div)
  have himg : ((↑) : Ω → E) '' A = (essentialBoundary μ s ∩ Ω) \ reducedBoundary μ Ω s :=
    (Subtype.image_preimage_coe _ _).trans (by rw [← inter_sdiff_assoc, inter_comm])
  rw [Measure.euclideanHausdorffMeasure_eq_zero_iff, ← himg,
    isometry_subtypeVal.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _))]
  exact hA

/-- **The essential and reduced boundaries agree up to a `μHE[n - 1]`-null set.** For a set `s`
of locally finite perimeter in an open set `Ω`, the part of the essential boundary `∂ᵉs` in `Ω` and
the reduced boundary `∂*s` agree `μHE[n - 1]`-almost everywhere, where `n = dim E` and `n - 1` is
truncated natural subtraction (so `0 - 1 = 0` when `n = 0`). -/
theorem essentialBoundary_inter_ae_eq_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    (essentialBoundary μ s ∩ Ω : Set E) =ᵐ[μHE[finrank ℝ E - 1]] reducedBoundary μ Ω s := by
  refine ae_eq_set.2
    ⟨euclideanHausdorffMeasure_essentialBoundary_inter_sdiff_reducedBoundary_eq_zero hu hfin, ?_⟩
  rw [sdiff_eq_empty.2 (subset_inter reducedBoundary_subset_essentialBoundary
    reducedBoundary_subset), measure_empty]

/-- **Federer's structure theorem** for a set of finite perimeter in `Ω`: if `s` is null-measurable
on `Ω` and `P(s; Ω) ≠ ∞`, then `∂ᵉs ∩ Ω =ᵐ[μHE[n - 1]] ∂*s`, where `n = dim E` and `n - 1` is
truncated natural subtraction (so `0 - 1 = 0` when `n = 0`). -/
theorem essentialBoundary_inter_ae_eq_reducedBoundary_of_perimeter_ne_top
    (hs : NullMeasurableSet s (μ.restrict Ω)) (hP : perimeter μ Ω s ≠ ∞) :
    (essentialBoundary μ s ∩ Ω : Set E) =ᵐ[μHE[finrank ℝ E - 1]] reducedBoundary μ Ω s :=
  essentialBoundary_inter_ae_eq_reducedBoundary (locallyIntegrableOn_indicator_const hs 1)
    fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩

/-- **Densities of sets of locally finite perimeter.** In every dimension, for countably many sets
`s i` of locally finite perimeter in an open set `Ω`, off an `Hⁿ⁻¹`-null set every `s i` has
density `0`, `1/2` or `1` at each point of `Ω`, and density `1/2` exactly on its reduced
boundary. -/
theorem ae_forall_exists_hasDensityAt {ι : Type*} [Countable ι]
    {s : ι → Set E}
    (hu : ∀ i, LocallyIntegrableOn ((s i).indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ i K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U ((s i).indicator 1) ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω → ∀ i, ∃ d : ℝ≥0∞, (d = 0 ∨ d = 1 / 2 ∨ d = 1) ∧
      HasDensityAt μ (s i) x d ∧ (d = 1 / 2 ↔ x ∈ reducedBoundary μ Ω (s i)) := by
  have hne : (1 / 2 : ℝ≥0∞) ≠ 0 := by simp
  have hne1 : (1 / 2 : ℝ≥0∞) ≠ 1 := (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top).ne
  filter_upwards [ae_all_iff.2 fun i => essentialBoundary_inter_ae_eq_reducedBoundary (hu i)
    (hfin i)] with x hx hxΩ i
  by_cases hr : x ∈ reducedBoundary μ Ω (s i)
  · exact ⟨1 / 2, Or.inr (Or.inl rfl), hasDensityAt_of_mem_reducedBoundary hr,
      iff_of_true rfl hr⟩
  · have hb : x ∉ essentialBoundary μ (s i) := fun hb => hr ((hx i).1 ⟨hb, hxΩ⟩)
    simp only [mem_essentialBoundary, not_and_or, not_not, mem_essentialInterior,
      mem_essentialExterior] at hb
    rcases hb with h1 | h0
    · exact ⟨1, Or.inr (Or.inr rfl), h1, iff_of_false hne1.symm hr⟩
    · exact ⟨0, Or.inl rfl, h0, iff_of_false hne.symm hr⟩

/-- **The perimeter is the measure of the essential boundary.** In dimension `n ≥ 2`, a set `s` of
locally finite perimeter in an open set `Ω` has `P(s; Ω) = Hⁿ⁻¹(∂ᵉs ∩ Ω)`. -/
theorem perimeter_eq_euclideanHausdorffMeasure_essentialBoundary_inter (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞) :
    perimeter volume Ω s = μHE[finrank ℝ E - 1] (essentialBoundary volume s ∩ Ω) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hn hu hfin,
    measure_congr (essentialBoundary_inter_ae_eq_reducedBoundary hu hfin)]

end TauCeti
