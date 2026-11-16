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
measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`. By
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
2. Because `|Dχ_s|` is outer regular, its `(n - 1)`-dimensional density
   `|Dχ_s|(closedBall y r) / r ^ (n - 1)` tends to `0` as `r → 0⁺` at `Hⁿ⁻¹`-almost every point
   outside `∂*s` (`MeasureTheory.Measure.ae_tendsto_measure_closedBall_div_of_measure_eq_zero`),
   and hence so does `P(s; ball y r) / r ^ (n - 1)`
   (`TauCeti.eventually_perimeter_ball_le_variationMeasure_closedBall`).
3. Combining the relative isoperimetric inequality in a ball
   (`TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`) with the zero-one density dichotomy
   (`TauCeti.notMem_essentialBoundary_of_tendsto_min_div`), vanishing `(n - 1)`-dimensional
   perimeter density forces `s` to have density `0` or `1` at `y`, excluding `y ∈ ∂ᵉs`.

## Main results

* `TauCeti.ae_mem_essentialBoundary`: `|Dχ_s|` is concentrated on `∂ᵉs`.
* `TauCeti.hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary` and
  `TauCeti.euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary`:
  `((Ω ∩ ∂ᵉs) \ ∂*s)` is `Hⁿ⁻¹`-null for a set of locally finite perimeter in `Ω`.
* `TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary`: `∂*s =ᵐ[μHE[n - 1]] Ω ∩ ∂ᵉs`, together
  with finite-perimeter specializations
  `TauCeti.reducedBoundary_ae_eq_inter_essentialBoundary_of_perimeter_ne_top` and
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

/-- Rescaled relative isoperimetric bound on closed balls: in dimension `n ≥ 2`, the `(1 - 1 / n)`
power of the smaller closed-ball volume proportion of `s` and `sᶜ` is controlled by
`P(s; ball x r) / r ^ (n - 1)`. -/
private theorem min_div_closedBall_rpow_le_mul_perimeter_div (hn : 2 ≤ finrank ℝ E) {r : ℝ}
    (hr : 0 < r) (hs : NullMeasurableSet s (μ.restrict (ball x r))) :
    (min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)) ^
        (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      (ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) /
          μ (ball (0 : E) 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹)) *
        (perimeter μ ⟨ball x r, isOpen_ball⟩ s / ENNReal.ofReal r ^ (finrank ℝ E - 1)) := by
  set n := finrank ℝ E with hn_eq
  set q : ℝ := 1 - (n : ℝ)⁻¹
  have hq : 0 < q := sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (zero_lt_two.trans_le hn)
  have hmin : min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) ^ q ≤
      ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball 0 1) ^ (n : ℝ)⁻¹) *
        perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
    rw [measure_congr (EventuallyEqSet.inter .rfl (μ.addHaar_closedBall_ae_eq_ball x r)),
      measure_congr (EventuallyEqSet.diff (μ.addHaar_closedBall_ae_eq_ball x r) .rfl)]
    exact min_measure_inter_measure_sdiff_rpow_le_perimeter hn hs
      (Ω := ⟨ball x r, isOpen_ball⟩) subset_rfl
  have hexp : (n : ℝ) * q = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (one_le_two.trans hn), Nat.cast_one, mul_sub, mul_one,
      mul_inv_cancel₀ (by positivity)]
  have hrpow : ENNReal.ofReal (r ^ n) ^ q = ENNReal.ofReal r ^ (n - 1) := by
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos hr n), ← Real.rpow_natCast r n,
      ← Real.rpow_mul hr.le, hexp, Real.rpow_natCast, ENNReal.ofReal_pow hr.le]
  have hden : μ (closedBall x r) ^ q =
      ENNReal.ofReal r ^ (n - 1) * μ (ball (0 : E) 1) ^ q := by
    rw [Measure.addHaar_closedBall μ x hr.le, ← hn_eq, ENNReal.mul_rpow_of_nonneg _ _ hq.le, hrpow]
  have hωqt : μ (ball (0 : E) 1) ^ q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hq.le measure_ball_lt_top.ne
  rw [ENNReal.div_rpow_of_nonneg _ _ hq.le, hden]
  refine (ENNReal.div_le_div_right hmin _).trans_eq ?_
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (.inr hωqt) (.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  ring

/-- In dimension `n ≥ 2`, if `s` is null-measurable on `Ω`, `x ∈ Ω`, and
`P(s; ball x r) / r ^ (n - 1) → 0` as `r → 0⁺`, then `x ∉ ∂ᵉs`. -/
private theorem notMem_essentialBoundary_of_tendsto_perimeter_ball_div
    (hn : 2 ≤ finrank ℝ E) (hs : NullMeasurableSet s (μ.restrict Ω)) (hx : x ∈ Ω)
    (hP : Tendsto (fun r => perimeter μ ⟨ball x r, isOpen_ball⟩ s /
        ENNReal.ofReal r ^ (finrank ℝ E - 1)) (𝓝[>] 0) (𝓝 0)) :
    x ∉ essentialBoundary μ s := by
  set n := finrank ℝ E
  set q : ℝ := 1 - (n : ℝ)⁻¹
  have hq : 0 < q := sub_pos.2 (inv_lt_one_of_one_lt₀ (by exact_mod_cast hn))
  set K := ENNReal.ofReal (2 ^ (n + 1) / μ.real (ball 0 1) ^ (n : ℝ)⁻¹) /
    μ (ball (0 : E) 1) ^ q
  have hKt : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_pos (measure_ball_pos μ 0 one_pos) measure_ball_lt_top.ne).ne'
  set f : ℝ → ℝ≥0∞ := fun r =>
    min (μ (s ∩ closedBall x r)) (μ (closedBall x r \ s)) / μ (closedBall x r)
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds hx)
  have hKP : Tendsto (fun r => K * (perimeter μ ⟨ball x r, isOpen_ball⟩ s /
      ENNReal.ofReal r ^ (n - 1))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hP (.inr hKt)
  have hfq : Tendsto (fun r => f r ^ q) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hKP
      (.of_forall fun _ => zero_le) (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr =>
        min_div_closedBall_rpow_le_mul_perimeter_div hn hr.1
          (hs.mono (Measure.restrict_mono ((ball_subset_ball hr.2.le).trans hεΩ) le_rfl)))
  refine notMem_essentialBoundary_of_tendsto_min_div ?_
  have hf := ((ENNReal.continuous_rpow_const (y := q⁻¹)).tendsto 0).comp hfq
  rw [ENNReal.zero_rpow_of_pos (inv_pos.2 hq)] at hf
  exact hf.congr fun r => by
    dsimp only [Function.comp_apply]
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hq.ne', ENNReal.rpow_one]

/-- Federer's null-difference estimate in dimension `n ≥ 2`: outside `∂*s`, `|Dχ_s|` has zero
`(n - 1)`-dimensional density `μH[n - 1]`-almost everywhere on `Ω`, forcing points outside `∂*s` to
lie outside `∂ᵉs` as well. -/
private theorem hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_of_two_le
    (hn : 2 ≤ finrank ℝ E)
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μH[((finrank ℝ E - 1 : ℕ) : ℝ)]
      (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 := by
  set d : ℕ := finrank ℝ E - 1
  set lam := variationMeasure μ Ω (s.indicator 1)
  set A : Set Ω := ((↑) : Ω → E) ⁻¹' (essentialBoundary μ s \ reducedBoundary μ Ω s)
  have himg : ((↑) : Ω → E) '' A =
      ((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s := by
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨⟨y.2, hy.1⟩, hy.2⟩,
      fun ⟨⟨hxΩ, hxeb⟩, hxrb⟩ => ⟨⟨x, hxΩ⟩, ⟨hxeb, hxrb⟩, rfl⟩⟩
  rw [← himg, isometry_subtype_coe.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg d)),
    measure_eq_zero_iff_ae_notMem]
  have hlamA : lam A = 0 :=
    measure_mono_null (fun _ hy => hy.2) (ae_iff.1 ae_mem_reducedBoundary)
  have hs : NullMeasurableSet s (μ.restrict Ω) :=
    (aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable
  have h20 : (2 : ℝ≥0∞) ^ d ≠ 0 := by simp
  have h2t : (2 : ℝ≥0∞) ^ d ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  filter_upwards [lam.ae_tendsto_measure_closedBall_div_of_measure_eq_zero
    (Nat.cast_nonneg d) hlamA] with y hy hyA
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
      ((eventually_perimeter_ball_le_variationMeasure_closedBall hu hfin y.2).mono fun r hr => by
        rw [Subtype.preimage_closedBall] at hr
        exact ENNReal.div_le_div_right hr _)
  exact notMem_essentialBoundary_of_tendsto_perimeter_ball_div hn hs y.2 hP0 hyA.1

/-- **The perimeter measure is concentrated on the essential boundary.** Against an additive Haar
measure on a finite-dimensional real inner product space, `|Dχ_s|`-almost every point of `Ω` lies in
`∂ᵉs`. -/
theorem ae_mem_essentialBoundary :
    ∀ᵐ y : Ω ∂variationMeasure μ Ω (s.indicator 1), (y : E) ∈ essentialBoundary μ s :=
  ae_mem_reducedBoundary.mono fun _ hy => reducedBoundary_subset_essentialBoundary hy

/-- **Federer's structure theorem, null-difference form (raw Hausdorff measure).** For a set `s` of
locally finite perimeter in an open set `Ω` against an additive Haar measure `μ`, the part of the
essential boundary in `Ω` outside the reduced boundary is `μH[n - 1]`-null (`n = dim E`). -/
theorem hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μH[((finrank ℝ E - 1 : ℕ) : ℝ)]
      (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 := by
  rcases le_or_gt (finrank ℝ E) 1 with hn | hn
  · rw [← reducedBoundary_eq_inter_essentialBoundary_of_finrank_le_one hn hu hfin, sdiff_self,
      measure_empty]
  · exact hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary_of_two_le hn hu hfin

/-- **Federer's structure theorem, null-difference form.** For a set `s` of locally finite perimeter
in an open set `Ω` against an additive Haar measure `μ`, the part of the essential boundary in `Ω`
outside the reduced boundary is `μHE[n - 1]`-null (`n = dim E`). -/
theorem euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    μHE[finrank ℝ E - 1] (((Ω : Set E) ∩ essentialBoundary μ s) \ reducedBoundary μ Ω s) = 0 :=
  Measure.euclideanHausdorffMeasure_eq_zero_iff.2
    (hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary hu hfin)

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
    hausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary hu hfin⟩

/-- **Federer's structure theorem.** For a set `s` of locally finite perimeter in an open set `Ω`
against an additive Haar measure `μ`, the reduced boundary `∂*s` agrees `μHE[n - 1]`-almost
everywhere with `Ω ∩ ∂ᵉs` (`n = dim E`). -/
theorem reducedBoundary_ae_eq_inter_essentialBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    reducedBoundary μ Ω s =ᵐ[μHE[finrank ℝ E - 1]] (Ω : Set E) ∩ essentialBoundary μ s :=
  ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 (subset_inter reducedBoundary_subset
      reducedBoundary_subset_essentialBoundary), measure_empty],
    euclideanHausdorffMeasure_inter_essentialBoundary_sdiff_reducedBoundary hu hfin⟩

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
