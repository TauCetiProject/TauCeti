/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile
public import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# The Wasserstein distance of two real laws at exponent one

On the real line the transport problem for the ground distance is solved explicitly: for two
probability laws `μ` and `ν` on `ℝ`,

`W₁ (μ, ν) = ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ = ‖μ.quantile - ν.quantile‖_{L¹ (0, 1)}`,

the area between the two cumulative distribution functions, equivalently the `L¹` distance of the
two quantile functions on the unit interval. The monotone coupling
`MeasureTheory.Measure.quantileCoupling` attains it, so the monotone rearrangement of two real
laws is an optimal transport plan for the ground distance.

Both identities are identities in `[0, ∞]` and need no moment hypothesis: their two sides are
infinite together, so laws with divergent first moments are covered as they stand.

One measure-theoretic identity, proved in `TauCeti.MeasureTheory.Integral.LayerCake`, drives both,
`TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff`: the `L¹` distance of two real
functions is the integral, over the levels `s`, of the measure of the set where exactly one of them
is at most `s`. On the two coordinates of a transport plan it rewrites the transport objective as
an integral of plan masses, each at least the gap between the two cumulative distribution functions
at that level, since a set on which exactly one coordinate is small carries at least the difference
of the two marginal masses. On the two quantile functions it rewrites the objective of the monotone
plan as the integral of exactly those gaps, by the Galois property of the quantile. Lower bound and
attained value therefore meet.

Exponents `p > 1` are not covered: the argument uses that the ground cost is the distance itself,
and the one-dimensional formula for the costs `|x - y| ^ p` is a rearrangement statement with an
unrelated proof.

## Main statements

* `TauCeti.wassersteinEDist_one_eq_lintegral_enorm_cdf_sub` — the Wasserstein distance at
  exponent one is the area between the two cumulative distribution functions;
* `TauCeti.wassersteinEDist_one_eq_eLpNorm_quantile_sub` — it is also the `L¹ (0, 1)` distance of
  the two quantile functions;
* `MeasureTheory.Measure.isOptimalCoupling_quantileCoupling` — the monotone coupling is an optimal
  plan for the ground distance.

## References

* S. S. Vallender, *Calculation of the Wasserstein distance between probability distributions on
  the line*, Theory of Probability and its Applications 18 (1974), 784--786.
* C. Villani, *Topics in Optimal Transportation*, GSM 58, AMS 2003, §2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal symmDiff

namespace TauCeti

section RealLaws

/-- On a transport plan of two real laws, the set of pairs whose two coordinates are separated by
the level `s` has mass at least the gap between the two cumulative distribution functions at
`s`. -/
theorem enorm_cdf_sub_le_measure_symmDiff {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) (s : ℝ) :
    ‖cdf μ s - cdf ν s‖ₑ ≤ π ({z : ℝ × ℝ | z.1 ≤ s} ∆ {z : ℝ × ℝ | z.2 ≤ s}) := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hfst : {z : ℝ × ℝ | z.1 ≤ s} = Iic s ×ˢ univ := by ext z; simp
  have hsnd : {z : ℝ × ℝ | z.2 ≤ s} = univ ×ˢ Iic s := by ext z; simp
  have hμ : cdf μ s = (π {z : ℝ × ℝ | z.1 ≤ s}).toReal := by
    rw [cdf_eq_real, measureReal_def, hfst, hπ.measure_prod_univ measurableSet_Iic]
  have hν : cdf ν s = (π {z : ℝ × ℝ | z.2 ≤ s}).toReal := by
    rw [cdf_eq_real, measureReal_def, hsnd, hπ.measure_univ_prod measurableSet_Iic]
  have hbound : |cdf μ s - cdf ν s|
      ≤ (π ({z : ℝ × ℝ | z.1 ≤ s} ∆ {z : ℝ × ℝ | z.2 ≤ s})).toReal := by
    rw [hμ, hν]
    exact MeasureTheory.abs_toReal_sub_le_toReal_symmDiff (measure_ne_top π _)
      (measure_ne_top π _)
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal (measure_ne_top π _)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The `L¹ (0, 1)` distance of the two quantile functions is the area between the two cumulative
distribution functions. -/
theorem lintegral_enorm_quantile_sub_eq_lintegral_enorm_cdf_sub (μ ν : Measure ℝ) :
    ∫⁻ t, ‖μ.quantile t - ν.quantile t‖ₑ ∂volume.restrict (Ioo (0 : ℝ) 1)
      = ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ := by
  rw [lintegral_enorm_sub_eq_lintegral_measure_symmDiff _
    (Measure.measurable_quantile μ).aemeasurable (Measure.measurable_quantile ν).aemeasurable]
  refine lintegral_congr fun s ↦ ?_
  have huIoc : Set.uIoc (cdf μ s) (cdf ν s)
      = Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) := by rw [Set.uIoc]
  have hset : ({t | μ.quantile t ≤ s} ∆ {t | ν.quantile t ≤ s}) ∩ Ioo (0 : ℝ) 1
      = Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) ∩ Ioo (0 : ℝ) 1 := by
    ext t
    simp only [mem_inter_iff, Set.mem_symmDiff, Set.mem_ofPred_eq, ← huIoc, Set.mem_uIoc, mem_Ioo,
      and_congr_left_iff]
    rintro ⟨ht0, ht1⟩
    rw [Measure.quantile_le_iff μ ht0 ht1, Measure.quantile_le_iff ν ht0 ht1]
    simp only [not_le, and_comm, or_comm]
  have hmeas : MeasurableSet ({t | μ.quantile t ≤ s} ∆ {t | ν.quantile t ≤ s}) :=
    (measurableSet_le (Measure.measurable_quantile μ) measurable_const).symmDiff
      (measurableSet_le (Measure.measurable_quantile ν) measurable_const)
  rw [Measure.restrict_apply hmeas, hset]
  refine le_antisymm ?_ ?_
  · calc volume (Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) ∩ Ioo (0 : ℝ) 1)
        ≤ volume (Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s))) :=
          measure_mono inter_subset_left
      _ = ‖cdf μ s - cdf ν s‖ₑ := by
          rw [Real.volume_Ioc, max_sub_min_eq_abs, abs_sub_comm, Real.enorm_eq_ofReal_abs]
  · calc ‖cdf μ s - cdf ν s‖ₑ
        = volume (Ioo (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s))) := by
          rw [Real.volume_Ioo, max_sub_min_eq_abs, abs_sub_comm, Real.enorm_eq_ofReal_abs]
      _ ≤ volume (Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) ∩ Ioo (0 : ℝ) 1) := by
          refine measure_mono fun t ht ↦ ⟨Ioo_subset_Ioc_self ht, ?_⟩
          exact ⟨lt_of_le_of_lt (le_min (cdf_nonneg μ s) (cdf_nonneg ν s)) ht.1,
            lt_of_lt_of_le ht.2 (max_le (cdf_le_one μ s) (cdf_le_one ν s))⟩

/-- **The one-dimensional Kantorovich formula.** The Wasserstein distance at exponent one of two
probability laws on `ℝ` is the area between their cumulative distribution functions. -/
theorem wassersteinEDist_one_eq_lintegral_enorm_cdf_sub (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist 1 μ ν = ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ := by
  refine le_antisymm ?_ ?_
  · refine (wassersteinEDist_le_eLpNorm_quantile_sub 1 μ ν).trans_eq ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_enorm_quantile_sub_eq_lintegral_enorm_cdf_sub μ ν
  · rw [wassersteinEDist_one_eq_transportCost]
    refine le_transportCost fun π hπ ↦ ?_
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    calc ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ
        ≤ ∫⁻ s, π ({z : ℝ × ℝ | z.1 ≤ s} ∆ {z : ℝ × ℝ | z.2 ≤ s}) :=
          lintegral_mono fun s ↦ enorm_cdf_sub_le_measure_symmDiff hπ s
      _ = ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π :=
          (lintegral_enorm_sub_eq_lintegral_measure_symmDiff π measurable_fst.aemeasurable
            measurable_snd.aemeasurable).symm
      _ = ∫⁻ z, edist z.1 z.2 ∂π := by simp_rw [edist_eq_enorm_sub]

/-- **The one-dimensional quantile formula.** The Wasserstein distance at exponent one of two
probability laws on `ℝ` is the `L¹ (0, 1)` distance of their quantile functions. -/
theorem wassersteinEDist_one_eq_eLpNorm_quantile_sub (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    wassersteinEDist 1 μ ν
      = eLpNorm (fun t ↦ μ.quantile t - ν.quantile t) 1 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [wassersteinEDist_one_eq_lintegral_enorm_cdf_sub, eLpNorm_one_eq_lintegral_enorm,
    lintegral_enorm_quantile_sub_eq_lintegral_enorm_cdf_sub]

end RealLaws

end TauCeti

namespace MeasureTheory.Measure

/-- **The monotone rearrangement is optimal.** The monotone coupling of two real laws minimizes
the transport objective of the ground distance. -/
theorem isOptimalCoupling_quantileCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    TauCeti.IsOptimalCoupling (fun z : ℝ × ℝ ↦ edist z.1 z.2) (μ.quantileCoupling ν) μ ν where
  toIsCoupling := μ.isCoupling_quantileCoupling ν
  lintegral_eq := by
    rw [← TauCeti.wassersteinEDist_one_eq_transportCost,
      TauCeti.wassersteinEDist_one_eq_eLpNorm_quantile_sub,
      ← TauCeti.eLpNorm_edist_quantileCoupling 1 μ ν, eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_congr fun z ↦ by simp

end MeasureTheory.Measure
