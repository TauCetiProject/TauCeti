/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.Probability.Process.EmpiricalMeasure
import TauCeti.Analysis.SpecificLimits.Cesaro.Basic
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Asymptotic equidistribution of sequences

Defines asymptotic equidistribution (`TauCeti.AsympEquidistributed`), total equidistribution
(`TauCeti.TotallyAsympEquidistributed`), and two-sided `ℤ`-indexed counterparts
(`TauCeti.AsympEquidistributedInt`, `TauCeti.TotallyAsympEquidistributedInt`), with Cesàro and
portmanteau characterizations, residue-class criteria, pushforwards, and congruence properties.

## References

* T. Tao, *Higher Order Fourier Analysis*, GSM 142, AMS, 2012, §1.1.1.
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A sequence `x : ℕ → X` is asymptotically equidistributed for `μ` if its empirical measures
converge weakly to `μ`. -/
def AsympEquidistributed (x : ℕ → X) (μ : ProbabilityMeasure X) : Prop :=
  Tendsto (TauCeti.Probability.empiricalMeasure x) atTop (𝓝 μ)

/-- Unfolding characterization of `AsympEquidistributed`. -/
theorem asympEquidistributed_def {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔
      Tendsto (TauCeti.Probability.empiricalMeasure x) atTop (𝓝 μ) := Iff.rfl

/-- Asymptotic equidistribution iff Cesàro averages converge for every `𝕜`-valued `X →ᵇ 𝕜`. -/
theorem asympEquidistributed_iff_integral_rclike_tendsto (𝕜 : Type*) [RCLike 𝕜]
    {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ ∀ f : X →ᵇ 𝕜, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : 𝕜)⁻¹ *
      ∑ i ∈ range (n + 1), f (x i)) atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]
  exact forall_congr' fun f ↦ by simp_rw [TauCeti.Probability.integral_empiricalMeasure_rclike
    (𝕜 := 𝕜) f.continuous.stronglyMeasurable]

/-- Asymptotic equidistribution iff Cesàro averages converge for every real `X →ᵇ ℝ`. -/
theorem asympEquidistributed_iff_integral_tendsto {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ ∀ f : X →ᵇ ℝ, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i ∈ range (n + 1), f (x i)) atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) :=
  asympEquidistributed_iff_integral_rclike_tendsto ℝ

/-- A constant sequence at `p` is asymptotically equidistributed for `diracProba p`. -/
theorem asympEquidistributed_const (p : X) :
    AsympEquidistributed (fun _ : ℕ ↦ p) (diracProba p) := by
  refine tendsto_const_nhds.congr fun n ↦ (ProbabilityMeasure.toMeasure_injective ?_).symm
  rw [TauCeti.Probability.empiricalMeasure_toMeasure, sum_const, card_range, ← smul_assoc,
    nsmul_eq_mul, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      (ENNReal.natCast_ne_top _), one_smul]; rfl

/-- When `ProbabilityMeasure X` is Hausdorff, an equidistributed sequence has a unique limit. -/
theorem AsympEquidistributed.unique [T2Space (ProbabilityMeasure X)] {x : ℕ → X}
    {μ ν : ProbabilityMeasure X} (hμ : AsympEquidistributed x μ) (hν : AsympEquidistributed x ν) :
    μ = ν := tendsto_nhds_unique hμ hν

/-- A constant sequence at `p` is equidistributed for `μ` iff `μ = diracProba p`. -/
@[simp] theorem asympEquidistributed_const_iff [T2Space (ProbabilityMeasure X)] (p : X)
    (μ : ProbabilityMeasure X) : AsympEquidistributed (fun _ : ℕ ↦ p) μ ↔ μ = diracProba p :=
  ⟨fun h ↦ h.unique (asympEquidistributed_const p), fun h ↦ h ▸ asympEquidistributed_const p⟩

/-- Pushing an equidistributed sequence forward along a continuous measurable map. -/
theorem AsympEquidistributed.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributed x μ) {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    AsympEquidistributed (f ∘ x) (μ.map f) :=
  ((ProbabilityMeasure.continuous_map_of_measurable hf hm).tendsto μ |>.comp hx).congr
    fun n ↦ TauCeti.Probability.map_empiricalMeasure hm x n

/-- Two sequences that agree eventually are equidistributed for the same measures. -/
theorem asympEquidistributed_congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hxy : x =ᶠ[atTop] y) : AsympEquidistributed x μ ↔ AsympEquidistributed y μ := by
  simp only [asympEquidistributed_iff_integral_tendsto]
  exact forall_congr' fun f ↦ by simpa only [smul_eq_mul] using
    tendsto_cesaro_congr_of_eventuallyEq (hxy.mono fun _ h ↦ congrArg f h)

/-- A sequence agreeing eventually with an equidistributed sequence shares its limit measure. -/
theorem AsympEquidistributed.congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributed x μ) (hxy : x =ᶠ[atTop] y) : AsympEquidistributed y μ :=
  (asympEquidistributed_congr_of_eventuallyEq hxy).mp hx

/-- Shifting the index of a sequence by a fixed offset `m` preserves equidistribution. -/
@[simp] theorem asympEquidistributed_comp_add_iff {x : ℕ → X} {μ : ProbabilityMeasure X} (m : ℕ) :
    AsympEquidistributed (fun n ↦ x (n + m)) μ ↔ AsympEquidistributed x μ := by
  simp only [asympEquidistributed_iff_integral_tendsto]
  exact forall_congr' fun f ↦ by
    simpa only [smul_eq_mul] using tendsto_cesaro_comp_add_iff (f := fun i ↦ f (x i)) m

/-- Equidistribution for `μr r` along every residue class `r : Fin q` (`q > 0`) implies
equidistribution for the uniform mixture `ν` of the `μr`. -/
theorem asympEquidistributed_of_forall_mod_average {x : ℕ → X} {q : ℕ} (hq : 0 < q)
    {μr : Fin q → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hν : (ν : Measure X) = (q : ℝ≥0∞)⁻¹ • ∑ r : Fin q, (μr r : Measure X))
    (h : ∀ r : Fin q, AsympEquidistributed (fun n ↦ x (q * n + r)) (μr r)) :
    AsympEquidistributed x ν := by
  rw [asympEquidistributed_iff_integral_tendsto]; intro f
  let L : ℕ → ℝ := fun r ↦ if hr : r < q then ∫ y, f y ∂(μr ⟨r, hr⟩ : Measure X) else 0
  have havg : ∫ y, f y ∂(ν : Measure X) = (q : ℝ)⁻¹ • ∑ r ∈ range q, L r := by
    rw [hν, integral_smul_measure, integral_finsetSum_measure (fun r _ ↦ f.integrable _),
      ENNReal.toReal_inv, ENNReal.toReal_natCast, ← Fin.sum_univ_eq_sum_range L]
    exact congrArg _ (sum_congr rfl fun r _ ↦ by simp [L, r.isLt])
  rw [havg]; simpa only [smul_eq_mul] using
    tendsto_cesaro_of_forall_mod hq (f := fun i ↦ f (x i)) (L := L) fun r hr ↦ by
      rw [(by simp [L, hr] : L r = ∫ y, f y ∂(μr ⟨r, hr⟩ : Measure X))]
      simpa only [smul_eq_mul] using (asympEquidistributed_iff_integral_tendsto.mp (h ⟨r, hr⟩)) f

/-- Equidistribution for `μ` along every residue class modulo `q > 0` implies equidistribution. -/
theorem asympEquidistributed_of_forall_mod {x : ℕ → X} {μ : ProbabilityMeasure X} {q : ℕ}
    (hq : 0 < q) (h : ∀ r < q, AsympEquidistributed (fun n ↦ x (q * n + r)) μ) :
    AsympEquidistributed x μ := asympEquidistributed_of_forall_mod_average hq (μr := fun _ ↦ μ)
  (by ext s _; simp [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hq.ne')
    (ENNReal.natCast_ne_top q)]) fun r ↦ h r.val r.isLt

/-- For a measurable set with `μ`-null frontier, the visit frequency converges to `μ.real E`. -/
theorem AsympEquidistributed.tendsto_frequency [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    {E : Set X} [DecidablePred (· ∈ E)] (hE : MeasurableSet E)
    (hfront : (μ : Measure X) (frontier E) = 0) : Tendsto (fun n : ℕ ↦
      (((range (n + 1)).filter (fun i ↦ x i ∈ E)).card : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 ((μ : Measure X).real E)) :=
  ((ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) E)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hx hfront)).congr
    (TauCeti.Probability.empiricalMeasure_real_eq_frequency hE)

/-- An equidistributed sequence visits every positive-`μ`-measure open set with positive lower
frequency. -/
theorem AsympEquidistributed.eventually_frequency_ge [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    {U : Set X} [DecidablePred (· ∈ U)] (hU : IsOpen U) (hpos : 0 < (μ : Measure X) U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c ≤ (((range (n + 1)).filter (fun i ↦ x i ∈ U)).card : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  have hU_pos : 0 < ((μ : Measure X) U).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  refine ⟨((μ : Measure X) U).toReal / 2, half_pos hU_pos, ?_⟩
  filter_upwards [Filter.eventually_lt_of_lt_liminf
    ((((ENNReal.ofReal_lt_ofReal_iff hU_pos).mpr (half_lt_self hU_pos)).trans_eq
      (ENNReal.ofReal_toReal (measure_ne_top _ _))).trans_le
      (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hx hU))] with n hn
  rw [← TauCeti.Probability.empiricalMeasure_real_eq_frequency hU.measurableSet n]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hn.le

/-- An equidistributed sequence for an open-positive probability measure has dense range. -/
theorem AsympEquidistributed.denseRange [HasOuterApproxClosed X] {x : ℕ → X}
    {μ : ProbabilityMeasure X} [Measure.IsOpenPosMeasure (μ : Measure X)]
    (hx : AsympEquidistributed x μ) : DenseRange x := by
  rw [DenseRange, dense_iff_inter_open]; intro U hU hne; classical
  obtain ⟨c, hc, hev⟩ := hx.eventually_frequency_ge hU (hU.measure_pos (μ : Measure X) hne)
  obtain ⟨n, hn⟩ := hev.exists; obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
    by_contra h0; rw [Nat.eq_zero_of_not_pos h0, Nat.cast_zero, zero_div] at hn; linarith)
  exact ⟨x i, (mem_filter.mp hi).2, mem_range_self i⟩

/-- A sequence `x : ℕ → X` is totally equidistributed for `μ` if `n ↦ x (q * n + r)` is
equidistributed for `μ` for all `q > 0` and `r : ℕ`. -/
def TotallyAsympEquidistributed (x : ℕ → X) (μ : ProbabilityMeasure X) : Prop :=
  ∀ q r : ℕ, 0 < q → AsympEquidistributed (fun n ↦ x (q * n + r)) μ

/-- Unfolding characterization of `TotallyAsympEquidistributed`. -/
theorem totallyAsympEquidistributed_def {x : ℕ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributed x μ ↔
      ∀ q r : ℕ, 0 < q → AsympEquidistributed (fun n ↦ x (q * n + r)) μ := Iff.rfl

/-- Total equidistribution implies equidistribution (`q = 1, r = 0`). -/
theorem TotallyAsympEquidistributed.asympEquidistributed {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) : AsympEquidistributed x μ := by
  simpa using hx 1 0 Nat.one_pos

/-- Total equidistribution is preserved along any positive-step arithmetic progression. -/
theorem TotallyAsympEquidistributed.comp_affine {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) {q : ℕ} (hq : 0 < q) (r : ℕ) :
    TotallyAsympEquidistributed (fun n ↦ x (q * n + r)) μ := fun q' r' hq' ↦ by
  simpa [mul_add, ← mul_assoc, add_assoc] using hx (q * q') (q * r' + r) (Nat.mul_pos hq hq')

/-- Pushing a totally equidistributed sequence forward along a continuous measurable map. -/
theorem TotallyAsympEquidistributed.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    TotallyAsympEquidistributed (f ∘ x) (μ.map f) := fun q r hq ↦ (hx q r hq).map hf hm

/-- A constant sequence at `p` is totally equidistributed for `diracProba p`. -/
theorem totallyAsympEquidistributed_const (p : X) :
    TotallyAsympEquidistributed (fun _ : ℕ ↦ p) (diracProba p) :=
  fun _ _ _ ↦ asympEquidistributed_const p

/-- Two sequences that agree eventually are totally equidistributed for the same measures. -/
theorem totallyAsympEquidistributed_congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hxy : x =ᶠ[atTop] y) : TotallyAsympEquidistributed x μ ↔ TotallyAsympEquidistributed y μ :=
  forall₃_congr fun q r hq ↦ asympEquidistributed_congr_of_eventuallyEq <| hxy.comp_tendsto <|
    (tendsto_add_atTop_nat r).comp <| by
      simpa only [nsmul_eq_mul, Nat.cast_id, id_eq] using
        (tendsto_id.nsmul_atTop hq : Tendsto (fun n : ℕ ↦ q • n) atTop atTop)

/-- A sequence agreeing eventually with a totally equidistributed sequence shares its limit. -/
theorem TotallyAsympEquidistributed.congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) (hxy : x =ᶠ[atTop] y) :
    TotallyAsympEquidistributed y μ := (totallyAsympEquidistributed_congr_of_eventuallyEq hxy).mp hx

/-- A sequence `x : ℤ → X` is two-sided equidistributed for `μ` when both `n ↦ x (n + 1)` and
`n ↦ x (-(n + 1))` are equidistributed for `μ`. -/
def AsympEquidistributedInt (x : ℤ → X) (μ : ProbabilityMeasure X) : Prop :=
  AsympEquidistributed (fun n : ℕ ↦ x (n + 1)) μ ∧
    AsympEquidistributed (fun n : ℕ ↦ x (-(n + 1 : ℤ))) μ

/-- Unfolding characterization of `AsympEquidistributedInt`. -/
theorem asympEquidistributedInt_def {x : ℤ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributedInt x μ ↔ AsympEquidistributed (fun n : ℕ ↦ x (n + 1)) μ ∧
      AsympEquidistributed (fun n : ℕ ↦ x (-(n + 1 : ℤ))) μ := Iff.rfl

/-- The positive half of a doubly infinite equidistributed sequence is equidistributed. -/
theorem AsympEquidistributedInt.pos_half {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) : AsympEquidistributed (fun n : ℕ ↦ x (n + 1)) μ := hx.1

/-- The negative half of a doubly infinite equidistributed sequence is equidistributed. -/
theorem AsympEquidistributedInt.neg_half {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) :
    AsympEquidistributed (fun n : ℕ ↦ x (-(n + 1 : ℤ))) μ := hx.2

/-- Restricting a doubly infinite equidistributed sequence to `ℕ` gives an equidistributed seq. -/
theorem AsympEquidistributedInt.natCast {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) : AsympEquidistributed (fun n : ℕ ↦ x n) μ := by
  simpa using (asympEquidistributed_comp_add_iff (x := fun n : ℕ ↦ x n) 1).mp hx.1

/-- Reversing the sign of the index preserves two-sided equidistribution. -/
@[simp] theorem asympEquidistributedInt_neg_iff {x : ℤ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributedInt (fun n : ℤ ↦ x (-n)) μ ↔ AsympEquidistributedInt x μ := by
  simp only [asympEquidistributedInt_def, neg_neg, and_comm]

/-- Shifting the index of `x : ℤ → X` by `r : ℤ` preserves two-sided equidistribution. -/
@[simp] theorem asympEquidistributedInt_comp_add_iff {x : ℤ → X} {μ : ProbabilityMeasure X}
    (r : ℤ) : AsympEquidistributedInt (fun n : ℤ ↦ x (n + r)) μ ↔ AsympEquidistributedInt x μ := by
  have hnat (m : ℕ) (z : ℤ → X) :
      AsympEquidistributedInt (fun n : ℤ ↦ z (n + m)) μ ↔ AsympEquidistributedInt z μ :=
    and_congr (by
      rw [(funext fun n ↦ by push_cast; ring_nf :
        (fun n : ℕ ↦ z ((n : ℤ) + 1 + m)) = fun n : ℕ ↦ z (((n + m : ℕ) : ℤ) + 1))]
      exact asympEquidistributed_comp_add_iff (x := fun n : ℕ ↦ z ((n : ℤ) + 1)) m)
      ((asympEquidistributed_comp_add_iff (x := fun n : ℕ ↦ z (-((n : ℤ) + 1) + m)) m).symm.trans
        (by rw [(funext fun n ↦ by push_cast; ring_nf :
          (fun n : ℕ ↦ z (-(((n + m : ℕ) : ℤ) + 1) + m)) = fun n : ℕ ↦ z (-((n : ℤ) + 1)))]))
  rcases le_total 0 r with hr | hr
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr; exact hnat m x
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hr)
    rw [(by linarith : r = -(m : ℤ)), ← asympEquidistributedInt_neg_iff
        (x := fun n ↦ x (n + -(m : ℤ))), ← asympEquidistributedInt_neg_iff (x := x)]
    simpa only [neg_add_rev, neg_neg, add_comm] using hnat m (fun n ↦ x (-n))

/-- Pushing a two-sided equidistributed sequence forward along a continuous measurable map. -/
theorem AsympEquidistributedInt.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    AsympEquidistributedInt (f ∘ x) (μ.map f) := ⟨hx.1.map hf hm, hx.2.map hf hm⟩

/-- Two sequences `ℤ → X` agreeing near `+∞` and `-∞` share two-sided equidistribution. -/
theorem asympEquidistributedInt_congr_of_eventuallyEq {x y : ℤ → X} {μ : ProbabilityMeasure X}
    (hxy_top : x =ᶠ[atTop] y) (hxy_bot : x =ᶠ[atBot] y) :
    AsympEquidistributedInt x μ ↔ AsympEquidistributedInt y μ :=
  have hpos : Tendsto (fun n : ℕ ↦ (n : ℤ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℤ) tendsto_natCast_atTop_atTop
  and_congr (asympEquidistributed_congr_of_eventuallyEq (hxy_top.comp_tendsto hpos))
    (asympEquidistributed_congr_of_eventuallyEq
      (hxy_bot.comp_tendsto (tendsto_neg_atTop_atBot.comp hpos)))

/-- A sequence agreeing near `±∞` with a two-sided equidistributed sequence shares its limit. -/
theorem AsympEquidistributedInt.congr_of_eventuallyEq {x y : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) (hxy_top : x =ᶠ[atTop] y) (hxy_bot : x =ᶠ[atBot] y) :
    AsympEquidistributedInt y μ :=
  (asympEquidistributedInt_congr_of_eventuallyEq hxy_top hxy_bot).mp hx

/-- Changing `x` at any single index `k : ℤ` does not affect two-sided equidistribution. -/
@[simp] theorem asympEquidistributedInt_update {x : ℤ → X} {μ : ProbabilityMeasure X} (k : ℤ)
    (y : X) : AsympEquidistributedInt (Function.update x k y) μ ↔ AsympEquidistributedInt x μ :=
  asympEquidistributedInt_congr_of_eventuallyEq
    ((Function.update_eventuallyEq_cofinite x k y).filter_mono atTop_le_cofinite)
    ((Function.update_eventuallyEq_cofinite x k y).filter_mono atBot_le_cofinite)

/-- A sequence `x : ℤ → X` is totally two-sided equidistributed for `μ` if every progression
`n ↦ x (q * n + r)` (`q > 0`, `r : ℤ`) is `AsympEquidistributedInt` for `μ`. -/
def TotallyAsympEquidistributedInt (x : ℤ → X) (μ : ProbabilityMeasure X) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ r : ℤ, AsympEquidistributedInt (fun n ↦ x (q * n + r)) μ

/-- Unfolding characterization of `TotallyAsympEquidistributedInt`. -/
theorem totallyAsympEquidistributedInt_def {x : ℤ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributedInt x μ ↔
      ∀ q : ℕ, 0 < q → ∀ r : ℤ, AsympEquidistributedInt (fun n ↦ x (q * n + r)) μ := Iff.rfl

/-- Total two-sided equidistribution implies plain two-sided equidistribution. -/
theorem TotallyAsympEquidistributedInt.asympEquidistributedInt {x : ℤ → X}
    {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ) :
    AsympEquidistributedInt x μ := by simpa using hx 1 Nat.one_pos 0

/-- Restricting a totally two-sided equidistributed sequence to `ℕ` preserves total equidist. -/
theorem TotallyAsympEquidistributedInt.totallyAsympEquidistributed_natCast {x : ℤ → X}
    {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ x n) μ := fun q r hq ↦ by
  simpa only [Int.natCast_add, Int.natCast_mul] using (hx q hq r).natCast

/-- Reversing the sign of the index preserves total two-sided equidistribution. -/
@[simp] theorem totallyAsympEquidistributedInt_neg_iff {x : ℤ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ x (-n)) μ ↔ TotallyAsympEquidistributedInt x μ := by
  refine forall₂_congr fun q _ ↦ (Equiv.neg ℤ).forall_congr fun r ↦ ?_; simp only [Equiv.neg_apply]
  have heq : (fun n : ℤ ↦ x (-((q : ℤ) * n + r))) =
      fun n : ℤ ↦ (fun m : ℤ ↦ x ((q : ℤ) * m + (-r))) (-n) := by ext n; ring_nf
  rw [heq, asympEquidistributedInt_neg_iff (x := fun m : ℤ ↦ x ((q : ℤ) * m + (-r)))]

/-- Shifting the index by `r₀ : ℤ` preserves total two-sided equidistribution. -/
@[simp] theorem totallyAsympEquidistributedInt_comp_add_iff {x : ℤ → X} {μ : ProbabilityMeasure X}
    (r₀ : ℤ) : TotallyAsympEquidistributedInt (fun n : ℤ ↦ x (n + r₀)) μ ↔
      TotallyAsympEquidistributedInt x μ :=
  forall₂_congr fun _ _ ↦ (Equiv.addRight r₀).forall_congr fun _ ↦ by
    simp only [Equiv.coe_addRight, add_assoc]

/-- Total two-sided equidistribution is preserved along any positive-step progression. -/
theorem TotallyAsympEquidistributedInt.comp_affine {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributedInt x μ) {q : ℕ} (hq : 0 < q) (r : ℤ) :
    TotallyAsympEquidistributedInt (fun n ↦ x (q * n + r)) μ := fun q' hq' r' ↦ by
  rw [(funext fun n ↦ by push_cast; ring_nf :
    (fun n : ℤ ↦ x ((q : ℤ) * ((q' : ℤ) * n + r') + r)) =
      fun n : ℤ ↦ x (((q * q' : ℕ) : ℤ) * n + ((q : ℤ) * r' + r)))]
  exact hx (q * q') (Nat.mul_pos hq hq') ((q : ℤ) * r' + r)

/-- Pushing a totally two-sided equidistributed sequence forward along a continuous measurable map.
-/
theorem TotallyAsympEquidistributedInt.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributedInt x μ) {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    TotallyAsympEquidistributedInt (f ∘ x) (μ.map f) := fun q hq r ↦ (hx q hq r).map hf hm

/-- Two sequences `ℤ → X` agreeing near `±∞` share total two-sided equidistribution. -/
theorem totallyAsympEquidistributedInt_congr_of_eventuallyEq {x y : ℤ → X}
    {μ : ProbabilityMeasure X} (hxy_top : x =ᶠ[atTop] y) (hxy_bot : x =ᶠ[atBot] y) :
    TotallyAsympEquidistributedInt x μ ↔ TotallyAsympEquidistributedInt y μ :=
  forall₃_congr fun q hq r ↦ asympEquidistributedInt_congr_of_eventuallyEq
    (hxy_top.comp_tendsto <| by simpa only [nsmul_eq_mul, id_eq] using
      tendsto_atTop_add_const_right atTop r (tendsto_id.nsmul_atTop hq))
    (hxy_bot.comp_tendsto <| by simpa only [nsmul_eq_mul, id_eq] using
      tendsto_atBot_add_const_right atBot r (tendsto_id.nsmul_atBot hq))

/-- A sequence agreeing near `±∞` with a totally two-sided equidistributed sequence shares its
limit. -/
theorem TotallyAsympEquidistributedInt.congr_of_eventuallyEq {x y : ℤ → X}
    {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ)
    (hxy_top : x =ᶠ[atTop] y) (hxy_bot : x =ᶠ[atBot] y) : TotallyAsympEquidistributedInt y μ :=
  (totallyAsympEquidistributedInt_congr_of_eventuallyEq hxy_top hxy_bot).mp hx

/-- Changing `x` at any single index `k : ℤ` does not affect total two-sided equidistribution. -/
@[simp] theorem totallyAsympEquidistributedInt_update {x : ℤ → X} {μ : ProbabilityMeasure X} (k : ℤ)
    (y : X) : TotallyAsympEquidistributedInt (Function.update x k y) μ ↔
      TotallyAsympEquidistributedInt x μ :=
  totallyAsympEquidistributedInt_congr_of_eventuallyEq
    ((Function.update_eventuallyEq_cofinite x k y).filter_mono atTop_le_cofinite)
    ((Function.update_eventuallyEq_cofinite x k y).filter_mono atBot_le_cofinite)

end TauCeti
