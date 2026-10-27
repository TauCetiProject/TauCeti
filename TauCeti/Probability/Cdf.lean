/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Cumulative distribution functions

This file records basic properties of cumulative distribution functions. In particular, the cdf
of an atomless real probability measure is continuous, and convolution averages translated cdfs.

A probability measure `μ` on `ℕ` becomes a real law by pushing it forward along the cast
`ℕ → ℝ`. The resulting cumulative distribution function is determined by the cumulative masses of
`μ` itself: it vanishes below the origin, where the pushforward has no mass at all, and at a
nonnegative point `x` it is the mass `μ` gives to the initial segment below the natural floor of
`x`. Every discrete law on `ℕ` therefore reads its real cdf off its own cumulative masses.

## Main results

* `MeasureTheory.Measure.cdf_conv` computes the cdf of a convolution;
* `MeasureTheory.Measure.continuous_cdf_of_noAtoms` proves continuity for atomless real laws;
* `MeasureTheory.Measure.cdf_eq_zero_of_measure_Iio_eq_zero` shows that an atomless law with no
  mass below a point has cdf zero there;
* `TauCeti.Probability.one_sub_cdf_zero_eq_one` and
  `TauCeti.Probability.one_sub_cdf_zero_eq_one_of_absolutelyContinuous` show that survival starts
  at one for an atomless or absolutely continuous law carried by the nonnegative half-line;
* `MeasureTheory.Measure.measure_Ioc_pos_iff_cdf_lt` characterizes positive interval mass by a
  strict increase of the cdf;
* `MeasureTheory.Measure.support_eq_univ_of_strictMono_cdf` shows that a strictly increasing cdf
  has full topological support;
* `MeasureTheory.Measure.strictMonoOn_cdf_of_subset_support` proves strict increase on any
  interval contained in the support;
* `MeasureTheory.Measure.cdf_lt_one_of_strictMonoOn_Ici` gives a strict upper bound for cdfs
  that increase strictly on a right half-line;
* `MeasureTheory.Measure.cdf_sublevel_measure` evaluates the measure of a CDF sublevel set for
  an atomless real law;
* `MeasureTheory.Measure.measureReal_Iio_neg` relates the lower tail of a symmetric real law to
  its cdf;
* `MeasureTheory.Measure.cdf_map_abs_of_nonneg` and `MeasureTheory.Measure.cdf_map_abs_of_neg`
  evaluate the cdf of the image of a real law under absolute value, and
  `MeasureTheory.Measure.cdf_map_abs_of_isNegInvariant` specializes it to symmetric laws;
* `MeasureTheory.Measure.cdf_map_const_mul_sqrt` evaluates the cdf of the image of a real law
  under a positive multiple of the square root;
* `MeasureTheory.Measure.leftLim_cdf` identifies the left limit of the cdf at a point with the
  mass of the open ray to its left;
* `Set.OrdConnected.mem_of_measureReal_Iio_le_of_le_cdf` shows that a cumulative-crossing point
  lies in every interval carrying the full mass of the measure;
* `MeasureTheory.Measure.cdf_map_natCast` evaluates the cdf at a nonnegative point;
* `MeasureTheory.Measure.cdf_map_natCast_of_neg` evaluates it below the origin;
* `MeasureTheory.Measure.cdf_map_intCast` evaluates an integer-valued law's cdf using the
  integer floor, including at negative points;
* `MeasureTheory.Measure.exists_nat_le_measureReal_Iic` shows that every level below one is
  reached by a finite cumulative mass of a natural-valued law.

## Adapted from

`continuous_cdf_of_noAtoms` and `cdf_sublevel_measure` are adapted from Cameron Freer's
independent implementation in `Graphon/MeasureIso.lean` at commit
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>,
under the same names; the graphon-specific packaging was removed. The original work is
copyright Cameron Freer and licensed under Apache 2.0.

These two results are the input to the probability integral transform
`MeasureTheory.Measure.cdf_map_eq_volume_restrict` in `TauCeti.Probability.Quantile`, which is
adapted from the same source, and they realize the measure-preserving equivalence of an
atomless standard-Borel space with the unit interval proved as Theorem A.7 in S. Janson,
*Graphons, cut norm and distance, couplings and rearrangements*, Arkiv för Matematik 52 (2014).
-/

public section

open Filter Function MeasureTheory ProbabilityTheory Set Topology

namespace MeasureTheory.Measure

/-- The cdf of a convolution is the average of the translated cdfs of its second factor. -/
theorem cdf_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : ℝ) : cdf (μ ∗ ν) x = ∫ y, cdf ν (x - y) ∂μ := by
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  rw [integral_conv (f := (Iic x).indicator (1 : ℝ → ℝ))
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [indicator_apply, Pi.one_apply, mem_Iic, le_sub_iff_add_le, add_comm y z]

/-- Below the level `1` some point has cumulative mass at least the level, because the cumulative
distribution function tends to `1` at `+∞`. -/
theorem nonempty_setOf_le_cdf (μ : Measure ℝ) {t : ℝ} (ht : t < 1) :
    {x : ℝ | t ≤ cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists.imp fun _ h ↦ h.le

/-- For a symmetric real law, the mass below `-x` is the mass above `x`, which is
`1 - cdf μ x`. -/
theorem measureReal_Iio_neg (μ : Measure ℝ) [IsProbabilityMeasure μ] [μ.IsNegInvariant]
    (x : ℝ) : μ.real (Iio (-x)) = 1 - cdf μ x := by
  rw [← Set.neg_Ioi, measureReal_def, Measure.measure_neg, ← measureReal_def, ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]

/-- The cdf of the image of `μ` under absolute value at a nonnegative point `x` is the mass of
`[-x, x]`, that is, the cdf of `μ` at `x` minus its left limit at `-x`. -/
theorem cdf_map_abs_of_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (|·|)) x = cdf μ x - μ.real (Iio (-x)) := by
  have hpre : (|·|) ⁻¹' Iic x = Iic x \ Iio (-x) := by
    ext y
    simp [abs_le, and_comm]
  rw [cdf_eq_real, map_measureReal_apply continuous_abs.measurable measurableSet_Iic, hpre,
    measureReal_sdiff (Iio_subset_Iic_self.trans (Iic_subset_Iic.2 (by linarith)))
      measurableSet_Iio, cdf_eq_real]

/-- The image of `μ` under absolute value puts no mass on the negative half-line. -/
theorem cdf_map_abs_of_neg (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ} (hx : x < 0) :
    cdf (μ.map (|·|)) x = 0 := by
  have hpre : (|·|) ⁻¹' Iic x = ∅ :=
    eq_empty_of_forall_notMem fun y hy => not_le.2 hx ((abs_nonneg y).trans hy)
  rw [cdf_eq_real, map_measureReal_apply continuous_abs.measurable measurableSet_Iic, hpre,
    measureReal_empty]

/-- The cdf of the image of a symmetric law under absolute value at `x ≥ 0` is
`2 * cdf μ x - 1`. -/
theorem cdf_map_abs_of_isNegInvariant (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [μ.IsNegInvariant] {x : ℝ} (hx : 0 ≤ x) : cdf (μ.map (|·|)) x = 2 * cdf μ x - 1 := by
  rw [μ.cdf_map_abs_of_nonneg hx, μ.measureReal_Iio_neg x]
  ring

/-- At positive scale `s`, the image of `μ` under `y ↦ s * √y` puts no mass on the negative
half-line, and at `x ≥ 0` its cdf is the cdf of `μ` at `(x / s) ^ 2`. -/
theorem cdf_map_const_mul_sqrt (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (x : ℝ) :
    cdf (μ.map fun y ↦ s * √y) x = if x < 0 then 0 else cdf μ ((x / s) ^ 2) := by
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  by_cases hx : x < 0
  · have hpre : (fun y ↦ s * √y) ⁻¹' Iic x = ∅ :=
      eq_empty_of_forall_notMem fun y hy ↦
        not_le.2 hx ((mul_nonneg hs.le (Real.sqrt_nonneg y)).trans hy)
    rw [hpre, measureReal_empty, ite_eq_left hx]
  · have hpre : (fun y ↦ s * √y) ⁻¹' Iic x = Iic ((x / s) ^ 2) := by
      ext y
      simp only [mem_preimage, mem_Iic, ← le_div_iff₀' hs, Real.sqrt_le_iff,
        div_nonneg (le_of_not_gt hx) hs.le, true_and]
    rw [hpre, ← cdf_eq_real, ite_eq_right hx]

/-- The cdf of an integer-valued law cast to the reals is its cumulative mass through the integer
floor of the argument. Unlike natural floor, integer floor also accounts for negative values. -/
theorem cdf_map_intCast (μ : Measure ℤ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (μ.map (Int.cast : ℤ → ℝ)) x = μ.real (Iic ⌊x⌋) := by
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, Int.preimage_Iic]

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

/-- At a nonnegative point, the cdf of a natural-valued law cast to the reals is the cumulative
mass of the initial segment below the natural floor of that point. -/
theorem cdf_map_natCast {x : ℝ} (hx : 0 ≤ x) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = μ.real (Iic ⌊x⌋₊) := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = Iic ⌊x⌋₊ := by
    ext k
    simp only [mem_preimage, mem_Iic]
    exact (Nat.le_floor_iff hx).symm
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]

/-- Below the origin, the cdf of a natural-valued law cast to the reals vanishes: the law is
carried by the natural numbers. -/
theorem cdf_map_natCast_of_neg {x : ℝ} (hx : x < 0) :
    cdf (μ.map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Iic x = ∅ := by
    ext k
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hx (Nat.cast_nonneg k)
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre,
    measureReal_empty]

/-- Every level below one is reached by a finite cumulative mass of a natural-valued probability
law. This existence proof supplies the witness required by `Nat.find`. -/
theorem exists_nat_le_measureReal_Iic {u : ℝ} (hu : u < 1) : ∃ k : ℕ, u ≤ μ.real (Iic k) := by
  obtain ⟨x, hx⟩ := nonempty_setOf_le_cdf (μ.map (Nat.cast : ℕ → ℝ)) hu
  refine ⟨⌈x⌉₊, ?_⟩
  have h := hx.trans (monotone_cdf (μ.map (Nat.cast : ℕ → ℝ)) (Nat.le_ceil x))
  simpa only [cdf_map_natCast μ (Nat.cast_nonneg _), Nat.floor_natCast] using h

/-- **CDF continuity from null singletons.** The cumulative distribution function of a
probability measure on `ℝ` is continuous when every singleton has measure zero. -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hleft : ∀ x, leftLim (cdf ν) x = cdf ν x := by
    intro x
    have hsing : (cdf ν).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hsing
    have hle : leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
    have hz : cdf ν x - leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp hsing
    exact le_antisymm hle (by linarith)
  rw [continuous_iff_continuousAt]
  intro x
  rw [(cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim, hleft x,
    ((cdf ν).right_continuous x).rightLim_eq]

/-- The left limit of the cumulative distribution function of a real probability law at a point is
the mass of the open ray to the left of that point. -/
theorem leftLim_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    leftLim (cdf ν) x = ν.real (Iio x) := by
  have h := (cdf ν).measure_Iio (tendsto_cdf_atBot ν) x
  rw [measure_cdf, sub_zero] at h
  have hnonneg : 0 ≤ leftLim (cdf ν) x :=
    (cdf_nonneg ν (x - 1)).trans ((cdf ν).mono.le_leftLim (by linarith))
  rw [measureReal_def, h, ENNReal.toReal_ofReal hnonneg]

/-- The mass of the open ray to the left of a point is at most a level exactly when the cumulative
distribution function stays at most that level at every point strictly to the left. -/
theorem measureReal_Iio_le_iff_forall_cdf_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {x t : ℝ} : ν.real (Iio x) ≤ t ↔ ∀ y < x, cdf ν y ≤ t := by
  rw [← leftLim_cdf]
  exact ⟨fun h y hy ↦ ((cdf ν).mono.le_leftLim hy).trans h, fun h ↦
    le_of_tendsto ((cdf ν).mono.tendsto_leftLim x) (eventually_nhdsWithin_of_forall h)⟩

/-- The mass of a bounded interval `Ioc a b` is the increment of the cumulative distribution
function between its endpoints. -/
theorem measureReal_Ioc_eq_cdf_sub (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ}
    (hab : a ≤ b) : ν.real (Ioc a b) = cdf ν b - cdf ν a := by
  rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic, cdf_eq_real,
    cdf_eq_real]

/-- A probability measure with no mass below `c` has cdf zero at every point strictly below `c`. -/
theorem cdf_eq_zero_of_lt_of_measure_Iio_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {c x : ℝ}
    (hc : ν (Iio c) = 0) (hx : x < c) : cdf ν x = 0 := by
  rw [cdf_eq_real]
  exact measureReal_mono_null (Iic_subset_Iio.mpr hx) (by simp [Measure.real, hc])

/-- An atomless law that gives no mass to the open half-line below `c` has cdf zero at `c`. -/
theorem cdf_eq_zero_of_measure_Iio_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] {c : ℝ} (hc : ν (Iio c) = 0) : cdf ν c = 0 := by
  have h : ν (Iic c) = 0 := (measure_congr Iio_ae_eq_Iic).symm.trans hc
  rw [cdf_eq_real, measureReal_def, h, ENNReal.toReal_zero]

/-- A half-open interval has positive mass exactly when the cdf strictly increases across its
endpoints. -/
theorem measure_Ioc_pos_iff_cdf_lt (ν : Measure ℝ) [IsProbabilityMeasure ν] {a b : ℝ} :
    0 < ν (Ioc a b) ↔ cdf ν a < cdf ν b := by
  calc
    0 < ν (Ioc a b) ↔ 0 < (cdf ν).measure (Ioc a b) := by rw [measure_cdf]
    _ ↔ cdf ν a < cdf ν b := by
      rw [StieltjesFunction.measure_Ioc, ENNReal.ofReal_pos, sub_pos]

/-- A real probability law with a strictly increasing cdf has full topological support. -/
theorem support_eq_univ_of_strictMono_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : StrictMono (cdf ν)) : ν.support = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [mem_support_iff_forall]
  intro U hU
  obtain ⟨a, b, hx, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  have hIoc : 0 < ν (Ioc a x) := (measure_Ioc_pos_iff_cdf_lt ν).mpr (hν hx.1)
  exact hIoc.trans_le (measure_mono fun y hy ↦ hab ⟨hy.1, hy.2.trans_lt hx.2⟩)

/-- The cdf increases strictly on every order-connected set contained in the support. -/
theorem strictMonoOn_cdf_of_subset_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {s : Set ℝ} (hs : s.OrdConnected) (hν : s ⊆ ν.support) : StrictMonoOn (cdf ν) s := by
  intro a ha b hb hab
  rw [← measure_Ioc_pos_iff_cdf_lt]
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  exact ((mem_support_iff_forall _).mp (hν (hs.out ha hb ⟨hac.le, hcb.le⟩)) (Ioo a b)
    (Ioo_mem_nhds hac hcb)).trans_le (measure_mono Ioo_subset_Ioc_self)

/-- A cdf that increases strictly on a right half-line is below one at every finite cutoff. -/
theorem cdf_lt_one_of_strictMonoOn_Ici (ν : Measure ℝ) {c : ℝ}
    (hν : StrictMonoOn (cdf ν) (Ici c)) (x : ℝ) : cdf ν x < 1 := by
  have hlt := hν (a := max x c) (b := max x c + 1) (le_max_right _ _)
    ((le_max_right x c).trans (lt_add_one _).le) (lt_add_one _)
  exact ((monotone_cdf ν (le_max_left x c)).trans_lt hlt).trans_le (cdf_le_one ν _)

/-- The measure of the sublevel set `{x | cdf ν x ≤ y}` is `ENNReal.ofReal y` when
`y < 1`. -/
theorem cdf_sublevel_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (y : ℝ) (hy1 : y < 1) :
    ν {x | cdf ν x ≤ y} = ENNReal.ofReal y := by
  set S : Set ℝ := {x | cdf ν x ≤ y}
  have hScl : IsClosed S := isClosed_Iic.preimage (continuous_cdf_of_noAtoms ν)
  have hevt : ∀ᶠ x in atTop, y < cdf ν x :=
    (tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevt
  have hSbdd : BddAbove S := by
    refine ⟨M, fun x hx => ?_⟩
    by_contra hxM
    exact absurd (hM x (le_of_lt (not_le.mp hxM))) (not_lt.2 hx)
  by_cases hSne : S.Nonempty
  · set q := sSup S
    have hq_mem : q ∈ S := hScl.csSup_mem hSne hSbdd
    have hSeq : S = Iic q := by
      ext x
      constructor
      · intro hx; exact le_csSup hSbdd hx
      · intro hx
        exact le_trans ((cdf ν).mono hx) hq_mem
    have hcdfq : cdf ν q = y := by
      refine le_antisymm hq_mem ?_
      have htend : Tendsto (cdf ν) (𝓝[>] q) (𝓝 (cdf ν q)) :=
        ((continuous_cdf_of_noAtoms ν).tendsto q).mono_left nhdsWithin_le_nhds
      have hevt2 : ∀ᶠ x in 𝓝[>] q, y ≤ cdf ν x := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
        have : x ∉ S := fun hxS => absurd (le_csSup hSbdd hxS) (not_le.2 hx)
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto htend hevt2
    rw [hSeq, ← ofReal_cdf ν q, hcdfq]
  · rw [not_nonempty_iff_eq_empty] at hSne
    have hyle : y ≤ 0 := by
      have hfor : ∀ᶠ x in atBot, y ≤ cdf ν x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have : x ∉ S := by rw [hSne]; simp
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto (tendsto_cdf_atBot ν) hfor
    have hνS : ν S = 0 := by rw [hSne]; exact measure_empty
    rw [ENNReal.ofReal_eq_zero.mpr hyle]
    exact hνS

end MeasureTheory.Measure

namespace Set.OrdConnected

/-- A point `q` at which the level `t` lies between the left limit and the value of the cumulative
distribution function lies in every interval of full mass: otherwise the interval lies entirely
on one side of `q`, and the mass on that side is `0` or `1`. -/
theorem mem_of_measureReal_Iio_le_of_le_cdf {μ : Measure ℝ} {s : Set ℝ} {t : ℝ}
    [IsProbabilityMeasure μ] (hs : s.OrdConnected) (hμs : ∀ᵐ x ∂μ, x ∈ s) {q : ℝ}
    (hIio : μ.real (Iio q) ≤ t) (hIic : t ≤ cdf μ q) (h0 : 0 < t) (h1 : t < 1) : q ∈ s := by
  by_contra hq
  have hside : (∀ x ∈ s, x < q) ∨ ∀ x ∈ s, q < x := by
    by_contra! h
    obtain ⟨⟨a, ha, hqa⟩, b, hb, hbq⟩ := h
    exact hq (hs.out hb ha ⟨hbq, hqa⟩)
  rcases hside with hlt | hgt
  · have hfull : μ (Iio q) = μ univ :=
      (ae_mem_iff_measure_eq measurableSet_Iio.nullMeasurableSet).1 (hμs.mono hlt)
    rw [measureReal_def, hfull, measure_univ, ENNReal.toReal_one] at hIio
    exact hIio.not_gt h1
  · have hnull : μ (Iic q) = 0 :=
      measure_eq_zero_iff_ae_notMem.2 (hμs.mono fun x hx hxq ↦ (hgt x hx).not_ge hxq)
    rw [cdf_eq_real, measureReal_def, hnull, ENNReal.toReal_zero] at hIic
    exact hIic.not_gt h0

end Set.OrdConnected

namespace TauCeti.Probability

variable {μ : Measure ℝ}

/-- **Survival starts at one.** An atomless probability law carried by the nonnegative half-line
has survival probability one at zero. -/
theorem one_sub_cdf_zero_eq_one [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (h0 : μ (Iio 0) = 0) :
    1 - cdf μ 0 = 1 := by
  rw [Measure.cdf_eq_zero_of_measure_Iio_eq_zero μ h0, sub_zero]

/-- **Survival starts at one for an absolutely continuous law.** A probability law absolutely
continuous with respect to Lebesgue measure and carried by the nonnegative half-line has survival
probability one at zero. -/
theorem one_sub_cdf_zero_eq_one_of_absolutelyContinuous [IsProbabilityMeasure μ]
    (hac : μ ≪ (volume : Measure ℝ)) (h0 : μ (Iio 0) = 0) : 1 - cdf μ 0 = 1 := by
  have : NullSingletonClass μ := ⟨fun t ↦ hac (measure_singleton t)⟩
  exact one_sub_cdf_zero_eq_one h0

end TauCeti.Probability
