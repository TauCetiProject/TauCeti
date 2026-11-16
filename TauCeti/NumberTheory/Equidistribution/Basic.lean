/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.Probability.Process.EmpiricalMeasure
import TauCeti.Analysis.SpecificLimits.Cesaro
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Asymptotic equidistribution of sequences

A sequence `x : ℕ → X` in a topological measurable space with measurable opens is *asymptotically
equidistributed* with respect to a probability measure `μ` (`TauCeti.AsympEquidistributed x μ`) if
its successor-indexed empirical probability measures converge weakly to `μ`. Equivalently, the
Cesàro averages of `f ∘ x` converge to `∫ f dμ` for every real or complex bounded continuous
function `f`.

Equidistribution is invariant under index shifts and finite modifications, pushes forward along
continuous measurable maps, and follows from equidistribution on every residue class modulo a
positive integer. On spaces satisfying `HasOuterApproxClosed`, the portmanteau theorem yields
convergence of visit frequencies for null-boundary sets, positive asymptotic lower density of
visits to open sets of positive measure, and density of the range when `μ` charges every nonempty
open set.

This file also introduces total equidistribution (`TauCeti.TotallyAsympEquidistributed`), requiring
equidistribution along every positive-step arithmetic progression, together with the two-sided
integer-indexed variants `TauCeti.AsympEquidistributedInt` and
`TauCeti.TotallyAsympEquidistributedInt`.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1.
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal

namespace TauCeti

section AsympEquidistributed

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A sequence `x : ℕ → X` is asymptotically equidistributed for a probability measure `μ` if its
empirical probability measures converge weakly to `μ`. -/
def AsympEquidistributed (x : ℕ → X) (μ : ProbabilityMeasure X) : Prop :=
  Tendsto (TauCeti.Probability.empiricalMeasure x) atTop (𝓝 μ)

/-- Unfolding characterization of `AsympEquidistributed`. -/
theorem asympEquidistributed_def {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ Tendsto (TauCeti.Probability.empiricalMeasure x) atTop (𝓝 μ) :=
  Iff.rfl

/-- Asymptotic equidistribution is equivalent to convergence of Cesàro averages for every
`𝕜`-valued bounded continuous test function (`𝕜 = ℝ` or `ℂ`). -/
theorem asympEquidistributed_iff_integral_rclike_tendsto (𝕜 : Type*) [RCLike 𝕜]
    {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ ∀ f : X →ᵇ 𝕜,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : 𝕜)⁻¹ * ∑ i ∈ range (n + 1), f (x i))
        atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]
  refine forall_congr' fun f ↦ ?_
  have havg (n : ℕ) :
      ∫ y, f y ∂(TauCeti.Probability.empiricalMeasure x n : Measure X) =
        ((n + 1 : ℕ) : 𝕜)⁻¹ * ∑ i ∈ range (n + 1), f (x i) := by
    have hf : StronglyMeasurable (f : X → 𝕜) := by
      have heq : (f : X → 𝕜) = fun y ↦ (RCLike.re (f y) : 𝕜) + (RCLike.im (f y) : 𝕜) * RCLike.I :=
        funext fun y ↦ (RCLike.re_add_im (f y)).symm
      rw [heq]
      exact (RCLike.continuous_ofReal.comp_stronglyMeasurable
        (RCLike.continuous_re.comp f.continuous).stronglyMeasurable).add
        ((RCLike.continuous_ofReal.comp_stronglyMeasurable
          (RCLike.continuous_im.comp f.continuous).stronglyMeasurable).mul_const _)
    rw [TauCeti.Probability.integral_empiricalMeasure hf, RCLike.real_smul_eq_coe_mul]
    simp
  simp_rw [havg]

/-- Asymptotic equidistribution is equivalent to convergence of Cesàro averages for every real
bounded continuous test function. -/
theorem asympEquidistributed_iff_integral_tendsto {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ ∀ f : X →ᵇ ℝ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range (n + 1), f (x i))
        atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) :=
  asympEquidistributed_iff_integral_rclike_tendsto ℝ

/-- A constant sequence at `p` is asymptotically equidistributed for the Dirac measure at `p`. -/
theorem asympEquidistributed_const (p : X) :
    AsympEquidistributed (fun _ : ℕ ↦ p) (diracProba p) := by
  have hemp (n : ℕ) : TauCeti.Probability.empiricalMeasure (fun _ : ℕ ↦ p) n = diracProba p := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [TauCeti.Probability.empiricalMeasure_toMeasure, sum_const, card_range, ← smul_assoc,
      nsmul_eq_mul, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
        (ENNReal.natCast_ne_top _), one_smul]
    rfl
  rw [asympEquidistributed_def]
  exact tendsto_const_nhds.congr fun n ↦ (hemp n).symm

/-- When the weak topology on probability measures is Hausdorff (for instance under
`HasOuterApproxClosed X` and `BorelSpace X`), a sequence is equidistributed for at most one
probability measure. -/
theorem AsympEquidistributed.unique [T2Space (ProbabilityMeasure X)]
    {x : ℕ → X} {μ ν : ProbabilityMeasure X}
    (hμ : AsympEquidistributed x μ) (hν : AsympEquidistributed x ν) :
    μ = ν :=
  tendsto_nhds_unique hμ hν

/-- A constant sequence at `p` is equidistributed for `μ` if and only if `μ = diracProba p`. -/
@[simp]
theorem asympEquidistributed_const_iff [T2Space (ProbabilityMeasure X)]
    (p : X) (μ : ProbabilityMeasure X) :
    AsympEquidistributed (fun _ : ℕ ↦ p) μ ↔ μ = diracProba p :=
  ⟨fun h ↦ h.unique (asympEquidistributed_const p), fun h ↦ h ▸ asympEquidistributed_const p⟩

/-- Pushing an equidistributed sequence forward along a continuous measurable map yields a sequence
equidistributed for the pushforward probability measure. -/
theorem AsympEquidistributed.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributed x μ) {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    AsympEquidistributed (f ∘ x) (μ.map f) := by
  rw [asympEquidistributed_def] at hx ⊢
  have hcont := (ProbabilityMeasure.continuous_map_of_measurable hf hm).tendsto μ
  refine (hcont.comp hx).congr fun n ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  simp [ProbabilityMeasure.toMeasure_map, Measure.map_apply hm hs,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (hm hs), ← Set.indicator_comp_right]

/-- Two sequences that agree eventually are equidistributed for the same measures. -/
theorem asympEquidistributed_congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hxy : x =ᶠ[atTop] y) :
    AsympEquidistributed x μ ↔ AsympEquidistributed y μ := by
  rw [asympEquidistributed_iff_integral_tendsto, asympEquidistributed_iff_integral_tendsto]
  refine forall_congr' fun f ↦ ?_
  simpa only [smul_eq_mul] using
    tendsto_cesaro_congr_of_eventuallyEq (f := fun i ↦ f (x i)) (g := fun i ↦ f (y i))
      (hxy.mono fun _ h ↦ congrArg f h)

/-- A sequence agreeing eventually with an equidistributed sequence is equidistributed for the same
measure. -/
theorem AsympEquidistributed.congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributed x μ) (hxy : x =ᶠ[atTop] y) :
    AsympEquidistributed y μ :=
  (asympEquidistributed_congr_of_eventuallyEq hxy).mp hx

/-- Shifting the index of a sequence by a fixed offset `m` does not change equidistribution. -/
@[simp]
theorem asympEquidistributed_comp_add_iff {x : ℕ → X} {μ : ProbabilityMeasure X} (m : ℕ) :
    AsympEquidistributed (fun n ↦ x (n + m)) μ ↔ AsympEquidistributed x μ := by
  rw [asympEquidistributed_iff_integral_tendsto, asympEquidistributed_iff_integral_tendsto]
  refine forall_congr' fun f ↦ ?_
  simpa only [smul_eq_mul] using
    tendsto_cesaro_comp_add_iff (f := fun i ↦ f (x i)) ⟨‖f‖, fun i ↦ f.norm_coe_le_norm (x i)⟩ m

/-- If a sequence is equidistributed for `μ` along every residue class modulo `q > 0`, then it is
equidistributed for `μ`. -/
theorem asympEquidistributed_of_forall_mod {x : ℕ → X} {μ : ProbabilityMeasure X}
    {q : ℕ} (hq : 0 < q) (h : ∀ r < q, AsympEquidistributed (fun n ↦ x (q * n + r)) μ) :
    AsympEquidistributed x μ := by
  rw [asympEquidistributed_iff_integral_tendsto]
  intro f
  have hmod := tendsto_cesaro_of_forall_mod hq (f := fun i ↦ f (x i))
    ⟨‖f‖, fun i ↦ f.norm_coe_le_norm (x i)⟩ (L := fun _ ↦ ∫ y, f y ∂(μ : Measure X))
    fun r hr ↦ by
      simpa only [smul_eq_mul] using (asympEquidistributed_iff_integral_tendsto.mp (h r hr)) f
  have hmean : (q : ℝ)⁻¹ • ∑ _r ∈ range q, ∫ y, f y ∂(μ : Measure X) =
      ∫ y, f y ∂(μ : Measure X) := by
    simp only [sum_const, card_range, nsmul_eq_mul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq.ne'), one_mul]
  rw [hmean] at hmod
  simpa only [smul_eq_mul] using hmod

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The empirical frequency of a measurable set equals the real-valued mass assigned to it by the
empirical probability measure. -/
private theorem empiricalMeasure_real_eq_frequency {x : ℕ → X} {E : Set X}
    [DecidablePred (· ∈ E)] (hE : MeasurableSet E) (n : ℕ) :
    ((TauCeti.Probability.empiricalMeasure x n : Measure X) E).toReal =
      (((range (n + 1)).filter (fun i ↦ x i ∈ E)).card : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  rw [TauCeti.Probability.empiricalMeasure_apply_toReal hE, div_eq_inv_mul]
  congr 1
  simp [Set.indicator_apply]

/-- For a measurable set whose frontier is `μ`-null, the asymptotic visit frequency of an
equidistributed sequence equals the `μ`-measure of the set. -/
theorem AsympEquidistributed.tendsto_frequency [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    {E : Set X} [DecidablePred (· ∈ E)] (hE : MeasurableSet E)
    (hfront : (μ : Measure X) (frontier E) = 0) :
    Tendsto (fun n : ℕ ↦
      (((range (n + 1)).filter (fun i ↦ x i ∈ E)).card : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 ((μ : Measure X).real E)) := by
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hx hfront
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) E)).comp hlim
  exact hreal.congr fun n ↦ empiricalMeasure_real_eq_frequency hE n

/-- An equidistributed sequence visits every open set of positive `μ`-measure with asymptotic
frequency bounded below by a positive constant. -/
theorem AsympEquidistributed.eventually_frequency_ge [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    {U : Set X} [DecidablePred (· ∈ U)] (hU : IsOpen U) (hpos : 0 < (μ : Measure X) U) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c ≤ (((range (n + 1)).filter (fun i ↦ x i ∈ U)).card : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  have hU_ne_top : (μ : Measure X) U ≠ ∞ := measure_ne_top _ _
  have hU_real_pos : 0 < ((μ : Measure X) U).toReal := ENNReal.toReal_pos hpos.ne' hU_ne_top
  refine ⟨((μ : Measure X) U).toReal / 2, half_pos hU_real_pos, ?_⟩
  have hlt : ENNReal.ofReal (((μ : Measure X) U).toReal / 2) < (μ : Measure X) U := by
    calc ENNReal.ofReal (((μ : Measure X) U).toReal / 2)
        < ENNReal.ofReal ((μ : Measure X) U).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hU_real_pos).mpr (half_lt_self hU_real_pos)
      _ = (μ : Measure X) U := ENNReal.ofReal_toReal hU_ne_top
  have hliminf : (μ : Measure X) U ≤
      atTop.liminf (fun n ↦ (TauCeti.Probability.empiricalMeasure x n : Measure X) U) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hx hU
  have hev := Filter.eventually_lt_of_lt_liminf (hlt.trans_le hliminf)
  filter_upwards [hev] with n hn
  rw [← empiricalMeasure_real_eq_frequency hU.measurableSet n]
  have hfin : (TauCeti.Probability.empiricalMeasure x n : Measure X) U ≠ ∞ := measure_ne_top _ _
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hn.le

/-- If `x` is equidistributed for a probability measure that charges every nonempty open set, then
the range of `x` is dense. -/
theorem AsympEquidistributed.denseRange [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} [Measure.IsOpenPosMeasure (μ : Measure X)]
    (hx : AsympEquidistributed x μ) :
    DenseRange x := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hne
  classical
  have hpos : 0 < (μ : Measure X) U := hU.measure_pos (μ : Measure X) hne
  obtain ⟨c, hc, hev⟩ := hx.eventually_frequency_ge hU hpos
  obtain ⟨n, hn⟩ := hev.exists
  have hcard_pos : 0 < ((range (n + 1)).filter (fun i ↦ x i ∈ U)).card := by
    by_contra hzero
    have h0 : ((range (n + 1)).filter (fun i ↦ x i ∈ U)).card = 0 := by omega
    rw [h0, Nat.cast_zero, zero_div] at hn
    linarith
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard_pos
  exact ⟨x i, (mem_filter.mp hi).2, mem_range_self i⟩

end AsympEquidistributed

section TotallyAsympEquidistributed

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A sequence `x : ℕ → X` is totally asymptotically equidistributed for `μ` if it is
asymptotically equidistributed along every positive-step arithmetic progression `n ↦ x (q * n + r)`.
-/
def TotallyAsympEquidistributed (x : ℕ → X) (μ : ProbabilityMeasure X) : Prop :=
  ∀ q r : ℕ, 0 < q → AsympEquidistributed (fun n ↦ x (q * n + r)) μ

/-- Unfolding characterization of `TotallyAsympEquidistributed`. -/
theorem totallyAsympEquidistributed_def {x : ℕ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributed x μ ↔
      ∀ q r : ℕ, 0 < q → AsympEquidistributed (fun n ↦ x (q * n + r)) μ :=
  Iff.rfl

/-- Total equidistribution implies equidistribution (take `q = 1, r = 0`). -/
theorem TotallyAsympEquidistributed.asympEquidistributed {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) :
    AsympEquidistributed x μ := by
  simpa using hx 1 0 Nat.one_pos

/-- Total equidistribution is preserved by passing to a positive-step arithmetic progression. -/
theorem TotallyAsympEquidistributed.comp_affine {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) {q : ℕ} (hq : 0 < q) (r : ℕ) :
    TotallyAsympEquidistributed (fun n ↦ x (q * n + r)) μ := by
  intro q' r' hq'
  have h := hx (q * q') (q * r' + r) (Nat.mul_pos hq hq')
  have heq : (fun n ↦ x (q * (q' * n + r') + r)) = fun n ↦ x (q * q' * n + (q * r' + r)) := by
    funext n
    ring_nf
  rwa [heq]

/-- Pushing a totally equidistributed sequence forward along a continuous measurable map yields a
totally equidistributed sequence for the pushforward measure. -/
theorem TotallyAsympEquidistributed.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    TotallyAsympEquidistributed (f ∘ x) (μ.map f) :=
  fun q r hq ↦ (hx q r hq).map hf hm

/-- A constant sequence at `p` is totally equidistributed for `diracProba p`. -/
theorem totallyAsympEquidistributed_const (p : X) :
    TotallyAsympEquidistributed (fun _ : ℕ ↦ p) (diracProba p) :=
  fun _ _ _ ↦ asympEquidistributed_const p

/-- Two sequences that agree eventually are totally equidistributed for the same measures. -/
theorem totallyAsympEquidistributed_congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hxy : x =ᶠ[atTop] y) :
    TotallyAsympEquidistributed x μ ↔ TotallyAsympEquidistributed y μ := by
  refine forall₃_congr fun q r hq ↦ asympEquidistributed_congr_of_eventuallyEq ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp hxy
  refine eventually_atTop.mpr ⟨N, fun n hn ↦ hN _ ?_⟩
  have : n ≤ q * n := Nat.le_mul_of_pos_left n hq
  omega

/-- A sequence agreeing eventually with a totally equidistributed sequence is totally
equidistributed for the same measure. -/
theorem TotallyAsympEquidistributed.congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) (hxy : x =ᶠ[atTop] y) :
    TotallyAsympEquidistributed y μ :=
  (totallyAsympEquidistributed_congr_of_eventuallyEq hxy).mp hx

end TotallyAsympEquidistributed

section AsympEquidistributedInt

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A doubly infinite sequence `x : ℤ → X` is asymptotically equidistributed for `μ` when both its
positive half `n ↦ x (n + 1)` and its negative half `n ↦ x (-(n + 1))` are asymptotically
equidistributed for `μ`. -/
def AsympEquidistributedInt (x : ℤ → X) (μ : ProbabilityMeasure X) : Prop :=
  AsympEquidistributed (fun n : ℕ ↦ x (n + 1)) μ ∧
    AsympEquidistributed (fun n : ℕ ↦ x (-(n + 1 : ℤ))) μ

/-- Unfolding characterization of `AsympEquidistributedInt`. -/
theorem asympEquidistributedInt_def {x : ℤ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributedInt x μ ↔
      AsympEquidistributed (fun n : ℕ ↦ x (n + 1)) μ ∧
        AsympEquidistributed (fun n : ℕ ↦ x (-(n + 1 : ℤ))) μ :=
  Iff.rfl

/-- The positive half of a doubly infinite equidistributed sequence is equidistributed. -/
theorem AsympEquidistributedInt.pos_half {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) :
    AsympEquidistributed (fun n : ℕ ↦ x (n + 1)) μ :=
  hx.1

/-- The negative half of a doubly infinite equidistributed sequence is equidistributed. -/
theorem AsympEquidistributedInt.neg_half {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) :
    AsympEquidistributed (fun n : ℕ ↦ x (-(n + 1 : ℤ))) μ :=
  hx.2

/-- Restricting a doubly infinite equidistributed sequence to `ℕ` gives an equidistributed
sequence. -/
theorem AsympEquidistributedInt.natCast {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) :
    AsympEquidistributed (fun n : ℕ ↦ x n) μ := by
  have h := hx.1
  have heq : (fun n : ℕ ↦ x ((n + 1 : ℕ) : ℤ)) = fun n : ℕ ↦ x (n + 1) := by
    funext n
    simp
  exact (asympEquidistributed_comp_add_iff (x := fun n : ℕ ↦ x n) 1).mp (heq.symm ▸ h)

/-- Reversing the sign of the index preserves two-sided equidistribution. -/
@[simp]
theorem asympEquidistributedInt_neg_iff {x : ℤ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributedInt (fun n : ℤ ↦ x (-n)) μ ↔ AsympEquidistributedInt x μ := by
  simp only [asympEquidistributedInt_def, neg_neg, and_comm]

/-- Changing the value of `x` at `0` does not affect two-sided equidistribution. -/
@[simp]
theorem asympEquidistributedInt_update_zero {x : ℤ → X} {μ : ProbabilityMeasure X} (y : X) :
    AsympEquidistributedInt (Function.update x 0 y) μ ↔ AsympEquidistributedInt x μ := by
  have hpos : (fun n : ℕ ↦ Function.update x 0 y (n + 1)) = fun n : ℕ ↦ x (n + 1) := by
    funext n
    exact Function.update_of_ne (by omega) _ _
  have hneg : (fun n : ℕ ↦ Function.update x 0 y (-(n + 1 : ℤ))) =
      fun n : ℕ ↦ x (-(n + 1 : ℤ)) := by
    funext n
    exact Function.update_of_ne (by omega) _ _
  rw [asympEquidistributedInt_def, asympEquidistributedInt_def, hpos, hneg]

/-- A doubly infinite sequence `x : ℤ → X` is totally asymptotically equidistributed for `μ` when
every progression `n ↦ x (q * n + r)` with `q > 0` and `r : ℤ` is `AsympEquidistributedInt` for
`μ`. -/
def TotallyAsympEquidistributedInt (x : ℤ → X) (μ : ProbabilityMeasure X) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ r : ℤ, AsympEquidistributedInt (fun n ↦ x (q * n + r)) μ

/-- Unfolding characterization of `TotallyAsympEquidistributedInt`. -/
theorem totallyAsympEquidistributedInt_def {x : ℤ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributedInt x μ ↔
      ∀ q : ℕ, 0 < q → ∀ r : ℤ, AsympEquidistributedInt (fun n ↦ x (q * n + r)) μ :=
  Iff.rfl

/-- Total two-sided equidistribution implies plain two-sided equidistribution. -/
theorem TotallyAsympEquidistributedInt.asympEquidistributedInt
    {x : ℤ → X} {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ) :
    AsympEquidistributedInt x μ := by
  simpa using hx 1 Nat.one_pos 0

/-- Restricting a totally equidistributed doubly infinite sequence to `ℕ` yields a totally
equidistributed sequence on `ℕ`. -/
theorem TotallyAsympEquidistributedInt.totallyAsympEquidistributed_natCast
    {x : ℤ → X} {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ x n) μ := by
  intro q r hq
  have h := (hx q hq r).natCast
  simpa only [Int.natCast_add, Int.natCast_mul] using h

/-- Total two-sided equidistribution is preserved by passing to any positive-step arithmetic
progression. -/
theorem TotallyAsympEquidistributedInt.comp_affine
    {x : ℤ → X} {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ)
    {q : ℕ} (hq : 0 < q) (r : ℤ) :
    TotallyAsympEquidistributedInt (fun n ↦ x (q * n + r)) μ := by
  intro q' hq' r'
  have h := hx (q * q') (Nat.mul_pos hq hq') ((q : ℤ) * r' + r)
  have heq : (fun n : ℤ ↦ x ((q : ℤ) * ((q' : ℤ) * n + r') + r)) =
      fun n : ℤ ↦ x (((q * q' : ℕ) : ℤ) * n + ((q : ℤ) * r' + r)) := by
    funext n
    push_cast
    ring_nf
  rwa [heq]

end AsympEquidistributedInt

end TauCeti
