/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.Probability.Process.EmpiricalMeasure
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.SpecificLimits.Cesaro

/-!
# Asymptotic equidistribution of sequences

A sequence `x : ℕ → X` in a topological measurable space is asymptotically equidistributed with
respect to a probability measure `μ` (`TauCeti.AsympEquidistributed x μ`) when its empirical
probability measures `TauCeti.Probability.empiricalMeasure x n` converge weakly to `μ`.
Equivalently, the Cesàro averages `(n + 1)⁻¹ ∑_{i ≤ n} f (x i)` converge to `∫ f dμ` for every
bounded continuous real- or complex-valued test function `f`.

A sequence is totally equidistributed (`TauCeti.TotallyAsympEquidistributed x μ`) when every
infinite arithmetic progression `n ↦ x (q * n + r)` (`q ≥ 1`) is equidistributed for `μ`. For
doubly infinite sequences `x : ℤ → X`, equidistribution (`TauCeti.AsympEquidistributedInt x μ`)
requires both the positive half `n ↦ x (n + 1)` and the negative half `n ↦ x (-(n + 1))` to be
equidistributed for `μ`, omitting `x 0`, and total equidistribution tests all progressions
`n ↦ x (q * n + r)` with `q ≥ 1` and `r : ℤ`.

## Main definitions

* `TauCeti.AsympEquidistributed`: weak convergence of empirical measures of `x : ℕ → X` to `μ`.
* `TauCeti.TotallyAsympEquidistributed`: equidistribution of `x : ℕ → X` along every positive-step
  arithmetic progression.
* `TauCeti.AsympEquidistributedInt`: equidistribution of both halves of `x : ℤ → X`.
* `TauCeti.TotallyAsympEquidistributedInt`: total equidistribution of `x : ℤ → X`.

## Main results

* `TauCeti.asympEquidistributed_iff_integral_rclike_tendsto` and
  `TauCeti.asympEquidistributed_iff_integral_tendsto`: characterization by bounded continuous test
  functions.
* `TauCeti.asympEquidistributed_comp_add_iff` and
  `TauCeti.AsympEquidistributed.congr_of_eventuallyEq`: invariance under finite index shifts and
  eventual equality.
* `TauCeti.asympEquidistributed_of_mod_classes_average` and
  `TauCeti.AsympEquidistributed.of_mod_classes`: interleaving equidistributed residue classes
  modulo `q > 0`.
* `TauCeti.AsympEquidistributed.unique` and `TauCeti.asympEquidistributed_const_iff`: uniqueness
  of limiting measures and constant sequences.
* `TauCeti.AsympEquidistributed.tendsto_frequency`,
  `TauCeti.AsympEquidistributed.eventually_lt_frequency_of_isOpen`, and
  `TauCeti.AsympEquidistributed.denseRange`: Portmanteau frequency limits, positive lower density
  for open sets, and dense range.
-/

public section

noncomputable section

open BoundedContinuousFunction Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

section NatSeq

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A sequence `x : ℕ → X` is asymptotically equidistributed with respect to `μ` if its empirical
probability measures converge weakly to `μ`. -/
def AsympEquidistributed (x : ℕ → X) (μ : ProbabilityMeasure X) : Prop :=
  Tendsto (TauCeti.Probability.empiricalMeasure x) atTop (𝓝 μ)

/-- Definitional restatement of `AsympEquidistributed`. -/
theorem asympEquidistributed_def {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ Tendsto (TauCeti.Probability.empiricalMeasure x) atTop (𝓝 μ) :=
  Iff.rfl

/-- Asymptotic equidistribution is equivalent to convergence of Cesàro averages for every bounded
continuous `𝕜`-valued function (`𝕜` either `ℝ` or `ℂ`). -/
theorem asympEquidistributed_iff_integral_rclike_tendsto (𝕜 : Type*) [RCLike 𝕜]
    {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ ∀ f : X →ᵇ 𝕜,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : 𝕜)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i))
        atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) := by
  rw [asympEquidistributed_def, ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]
  refine forall_congr' fun f ↦ ?_
  have havg (n : ℕ) :
      ∫ y, f y ∂(TauCeti.Probability.empiricalMeasure x n : Measure X) =
        ((n + 1 : ℕ) : 𝕜)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i) := by
    rw [TauCeti.Probability.integral_empiricalMeasure f.continuous.stronglyMeasurable,
      RCLike.real_smul_eq_coe_mul]
    push_cast
    rfl
  simp_rw [havg]

/-- Asymptotic equidistribution is equivalent to convergence of Cesàro averages for every bounded
continuous real-valued function. -/
theorem asympEquidistributed_iff_integral_tendsto {x : ℕ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributed x μ ↔ ∀ f : X →ᵇ ℝ,
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i))
        atTop (𝓝 (∫ y, f y ∂(μ : Measure X))) :=
  asympEquidistributed_iff_integral_rclike_tendsto ℝ

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- Shifting a sequence by `m` changes any partial sum of a bounded function by at most
`2 * m * ‖f‖`. -/
private theorem norm_sum_range_add_sub_le (f : X →ᵇ ℝ) (x : ℕ → X) (m n : ℕ) :
    ‖∑ i ∈ Finset.range (n + 1), f (x (i + m)) - ∑ i ∈ Finset.range (n + 1), f (x i)‖ ≤
      2 * (m : ℝ) * ‖f‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : ∑ i ∈ Finset.range (n + 1), f (x (i + (m + 1))) -
        ∑ i ∈ Finset.range (n + 1), f (x (i + m)) = f (x (n + 1 + m)) - f (x m) := by
      have h1 : ∑ i ∈ Finset.range (n + 1), f (x (i + (m + 1))) + f (x m) =
          ∑ i ∈ Finset.range (n + 2), f (x (i + m)) := by
        rw [Finset.sum_range_succ' (fun i ↦ f (x (i + m))) (n + 1), zero_add]
        simp [Nat.add_assoc, Nat.add_comm 1 m]
      have h2 : ∑ i ∈ Finset.range (n + 2), f (x (i + m)) =
          ∑ i ∈ Finset.range (n + 1), f (x (i + m)) + f (x (n + 1 + m)) :=
        Finset.sum_range_succ (fun i ↦ f (x (i + m))) (n + 1)
      linarith
    have hsplit : ∑ i ∈ Finset.range (n + 1), f (x (i + (m + 1))) -
        ∑ i ∈ Finset.range (n + 1), f (x i) =
      (∑ i ∈ Finset.range (n + 1), f (x (i + (m + 1))) -
          ∑ i ∈ Finset.range (n + 1), f (x (i + m))) +
        (∑ i ∈ Finset.range (n + 1), f (x (i + m)) - ∑ i ∈ Finset.range (n + 1), f (x i)) := by
      ring
    calc ‖∑ i ∈ Finset.range (n + 1), f (x (i + (m + 1))) -
            ∑ i ∈ Finset.range (n + 1), f (x i)‖
        ≤ ‖f (x (n + 1 + m)) - f (x m)‖ + 2 * (m : ℝ) * ‖f‖ := by
          rw [hsplit, hstep]
          exact (norm_add_le _ _).trans (by gcongr)
      _ ≤ (‖f (x (n + 1 + m))‖ + ‖f (x m)‖) + 2 * (m : ℝ) * ‖f‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (‖f‖ + ‖f‖) + 2 * (m : ℝ) * ‖f‖ := by
          gcongr <;> exact f.norm_coe_le_norm _
      _ = 2 * ((m + 1 : ℕ) : ℝ) * ‖f‖ := by push_cast; ring

/-- Shifting the index of a sequence by any natural number `m` does not affect asymptotic
equidistribution. -/
theorem asympEquidistributed_comp_add_iff (x : ℕ → X) (m : ℕ) (μ : ProbabilityMeasure X) :
    AsympEquidistributed (fun n ↦ x (n + m)) μ ↔ AsympEquidistributed x μ := by
  rw [asympEquidistributed_iff_integral_tendsto, asympEquidistributed_iff_integral_tendsto]
  refine forall_congr' fun f ↦ ?_
  have hdiff : Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x (i + m)) -
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), f (x i)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * (2 * (m : ℝ) * ‖f‖))
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).mul_const
        (2 * (m : ℝ) * ‖f‖)
    refine squeeze_zero_norm (fun n ↦ ?_) hbound
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_sum_range_add_sub_le f x m n) (by positivity)
  constructor
  · intro h
    simpa using h.sub hdiff
  · intro h
    simpa using h.add hdiff

/-- Sequences that agree eventually are equidistributed for the same probability measures. -/
theorem AsympEquidistributed.congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributed x μ) (hxy : x =ᶠ[atTop] y) : AsympEquidistributed y μ := by
  obtain ⟨m, hm⟩ := eventually_atTop.1 hxy
  rw [← asympEquidistributed_comp_add_iff y m]
  have heq : (fun n ↦ y (n + m)) = fun n ↦ x (n + m) :=
    funext fun n ↦ (hm (n + m) (Nat.le_add_left m n)).symm
  rw [heq, asympEquidistributed_comp_add_iff]
  exact hx

/-- Eventually equal sequences are equidistributed for the same probability measures. -/
theorem asympEquidistributed_congr_of_eventuallyEq {x y : ℕ → X} {μ : ProbabilityMeasure X}
    (hxy : x =ᶠ[atTop] y) : AsympEquidistributed x μ ↔ AsympEquidistributed y μ :=
  ⟨fun hx ↦ hx.congr_of_eventuallyEq hxy, fun hy ↦ hy.congr_of_eventuallyEq hxy.symm⟩

/-- If every residue class `m ↦ x (q * m + r)` modulo `q` is equidistributed for a probability
measure `μ r`, then `x` is equidistributed for the uniform mixture `q⁻¹ • ∑ r, μ r`. -/
theorem asympEquidistributed_of_mod_classes_average {x : ℕ → X} {q : ℕ}
    {μ : Fin q → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hν : (ν : Measure X) = (q : ℝ≥0∞)⁻¹ • ∑ r : Fin q, (μ r : Measure X))
    (hx : ∀ r : Fin q, AsympEquidistributed (fun m ↦ x (q * m + r)) (μ r)) :
    AsympEquidistributed x ν := by
  have hq : 0 < q := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    subst h0
    have h1 : (ν : Measure X) Set.univ = 1 := measure_univ
    rw [hν] at h1
    simp at h1
  rw [asympEquidistributed_iff_integral_tendsto]
  intro f
  have hν_int : ∫ y, f y ∂(ν : Measure X) =
      (q : ℝ)⁻¹ • ∑ r : Fin q, ∫ y, f y ∂(μ r : Measure X) := by
    rw [hν, integral_smul_measure, integral_finsetSum_measure
      (fun r _ ↦ BoundedContinuousFunction.integrable (μ r : Measure X) f),
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [hν_int]
  simpa only [smul_eq_mul] using tendsto_cesaro_of_mod_classes (g := fun i ↦ f (x i)) hq fun r ↦ by
    simpa only [smul_eq_mul] using (asympEquidistributed_iff_integral_tendsto.1 (hx r)) f

/-- If every residue class `m ↦ x (q * m + r)` modulo `q > 0` is equidistributed for the same
probability measure `μ`, then `x` is equidistributed for `μ`. -/
theorem AsympEquidistributed.of_mod_classes {x : ℕ → X} {q : ℕ} (hq : 0 < q)
    {μ : ProbabilityMeasure X}
    (hx : ∀ r : Fin q, AsympEquidistributed (fun m ↦ x (q * m + r)) μ) :
    AsympEquidistributed x μ := by
  refine asympEquidistributed_of_mod_classes_average (μ := fun _ ↦ μ) ?_ hx
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
    smul_smul, ENNReal.inv_mul_cancel (by simp [hq.ne']) (by simp), one_smul]

/-- When `ProbabilityMeasure X` is Hausdorff (for example under `HasOuterApproxClosed X` and
`BorelSpace X`), a sequence is equidistributed for at most one probability measure. -/
theorem AsympEquidistributed.unique [T2Space (ProbabilityMeasure X)]
    {x : ℕ → X} {μ ν : ProbabilityMeasure X}
    (hμ : AsympEquidistributed x μ) (hν : AsympEquidistributed x ν) : μ = ν :=
  tendsto_nhds_unique hμ hν

/-- A constant sequence at `p` is asymptotically equidistributed for `diracProba p`. -/
theorem asympEquidistributed_const (p : X) : AsympEquidistributed (fun _ ↦ p) (diracProba p) := by
  have hemp : TauCeti.Probability.empiricalMeasure (fun _ ↦ p) = fun _ ↦ diracProba p := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    simp only [TauCeti.Probability.empiricalMeasure_toMeasure, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul]
    rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_smul]
    rfl
  rw [asympEquidistributed_def, hemp]
  exact tendsto_const_nhds

/-- When `ProbabilityMeasure X` is Hausdorff, a constant sequence at `p` is equidistributed for `μ`
if and only if `μ = diracProba p`. -/
theorem asympEquidistributed_const_iff [T2Space (ProbabilityMeasure X)]
    (p : X) (μ : ProbabilityMeasure X) :
    AsympEquidistributed (fun _ ↦ p) μ ↔ μ = diracProba p :=
  ⟨fun h ↦ h.unique (asympEquidistributed_const p), fun h ↦ h ▸ asympEquidistributed_const p⟩

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Express the real-valued empirical measure of a measurable set as its relative frequency. -/
private theorem empiricalMeasure_apply_toReal_eq_card_div {x : ℕ → X} {E : Set X}
    [DecidablePred (· ∈ E)] (hE : MeasurableSet E) (n : ℕ) :
    ((TauCeti.Probability.empiricalMeasure x n : Measure X) E).toReal =
      (((Finset.range (n + 1)).filter fun i ↦ x i ∈ E).card : ℝ) / (n + 1 : ℕ) := by
  rw [TauCeti.Probability.empiricalMeasure_apply_toReal hE, div_eq_inv_mul]
  congr 1
  simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole]

/-- **Portmanteau frequency theorem.** If `x` is equidistributed for `μ` and `E` has `μ`-null
frontier (`μ (frontier E) = 0`), then the empirical frequencies of `E` converge to `(μ E).toReal`.
No measurability assumption on `E` is needed. -/
theorem AsympEquidistributed.tendsto_frequency [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    {E : Set X} [DecidablePred (· ∈ E)] (hbdry : (μ : Measure X) (frontier E) = 0) :
    Tendsto (fun n : ℕ ↦
        (((Finset.range (n + 1)).filter fun i ↦ x i ∈ E).card : ℝ) / (n + 1 : ℕ))
      atTop (𝓝 ((μ : Measure X) E).toReal) := by
  classical
  have hcl_le : (μ : Measure X) (closure E) ≤ (μ : Measure X) (interior E) := by
    have hsub : closure E ⊆ interior E ∪ frontier E := fun y hy ↦ by
      by_cases h : y ∈ interior E
      · exact Or.inl h
      · exact Or.inr ⟨hy, h⟩
    calc (μ : Measure X) (closure E)
        ≤ (μ : Measure X) (interior E ∪ frontier E) := measure_mono hsub
      _ ≤ (μ : Measure X) (interior E) + (μ : Measure X) (frontier E) := measure_union_le _ _
      _ = (μ : Measure X) (interior E) := by rw [hbdry, add_zero]
  have hint_eq : (μ : Measure X) (interior E) = (μ : Measure X) E :=
    le_antisymm (measure_mono interior_subset) ((measure_mono subset_closure).trans hcl_le)
  have hcl_eq : (μ : Measure X) (closure E) = (μ : Measure X) E :=
    le_antisymm (hcl_le.trans (measure_mono interior_subset)) (measure_mono subset_closure)
  have hmeas_tend (S : Set X) [DecidablePred (· ∈ S)] (hS : MeasurableSet S)
      (hSbdry : (μ : Measure X) (frontier S) = 0) :
      Tendsto (fun n : ℕ ↦
          (((Finset.range (n + 1)).filter fun i ↦ x i ∈ S).card : ℝ) / (n + 1 : ℕ))
        atTop (𝓝 ((μ : Measure X) S).toReal) := by
    have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hx (E := S)
      (by rw [← ENNReal.coe_inj, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hSbdry,
        ENNReal.coe_zero])
    have h' : Tendsto (fun n ↦ ((TauCeti.Probability.empiricalMeasure x n : Measure X) S).toReal)
        atTop (𝓝 ((μ : Measure X) S).toReal) := by
      simpa only [Function.comp_def, ProbabilityMeasure.coeFn_def, ENNReal.toReal] using
        (NNReal.continuous_coe.tendsto _).comp h
    simpa only [empiricalMeasure_apply_toReal_eq_card_div hS] using h'
  have hlo := hmeas_tend (interior E) isOpen_interior.measurableSet
    (measure_mono_null frontier_interior_subset hbdry)
  have hhi := hmeas_tend (closure E) isClosed_closure.measurableSet
    (measure_mono_null frontier_closure_subset hbdry)
  rw [hint_eq] at hlo
  rw [hcl_eq] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n ↦ ?_) (fun n ↦ ?_)
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast Finset.card_le_card fun i hi ↦
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1, interior_subset (Finset.mem_filter.1 hi).2⟩
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast Finset.card_le_card fun i hi ↦
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1, subset_closure (Finset.mem_filter.1 hi).2⟩

/-- If `x` is equidistributed for `μ` and `U` is open, then every threshold `c < (μ U).toReal`
is eventually exceeded by the empirical frequencies of `U`. -/
theorem AsympEquidistributed.eventually_lt_frequency_of_isOpen [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    {U : Set X} [DecidablePred (· ∈ U)] (hU : IsOpen U) {c : ℝ}
    (hc : c < ((μ : Measure X) U).toReal) :
    ∀ᶠ n : ℕ in atTop,
      c < (((Finset.range (n + 1)).filter fun i ↦ x i ∈ U).card : ℝ) / (n + 1 : ℕ) := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact Eventually.of_forall fun n ↦ hc0.trans_le (by positivity)
  · have hlt : ENNReal.ofReal c < (μ : Measure X) U :=
      (ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).2 hc
    have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hx hU
    have hev := Filter.eventually_lt_of_lt_liminf (hlt.trans_le hlim)
      ⟨0, Eventually.of_forall fun _ ↦ zero_le⟩
    filter_upwards [hev] with n hn
    rw [← empiricalMeasure_apply_toReal_eq_card_div hU.measurableSet]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hc0 (measure_ne_top _ _)).1 hn

/-- If `x` is equidistributed for a probability measure `μ` that gives positive mass to every
nonempty open set, then the range of `x` is dense in `X`. -/
theorem AsympEquidistributed.denseRange [HasOuterApproxClosed X]
    {x : ℕ → X} {μ : ProbabilityMeasure X} (hx : AsympEquidistributed x μ)
    (hμ : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < (μ : Measure X) U) :
    DenseRange x := by
  classical
  refine dense_iff_inter_open.2 fun U hU hUne ↦ ?_
  have hpos : 0 < ((μ : Measure X) U).toReal :=
    ENNReal.toReal_pos (hμ U hU hUne).ne' (measure_ne_top _ _)
  obtain ⟨n, hn⟩ := (hx.eventually_lt_frequency_of_isOpen hU hpos).exists
  have hcard : 0 < ((Finset.range (n + 1)).filter fun i ↦ x i ∈ U).card := by
    by_contra h0
    simp only [not_lt, Nat.le_zero] at h0
    simp [h0] at hn
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hcard
  exact ⟨x i, (Finset.mem_filter.1 hi).2, ⟨i, rfl⟩⟩

end NatSeq

section TotalAndInt

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A sequence `x : ℕ → X` is totally asymptotically equidistributed with respect to `μ` if every
positive-step arithmetic progression `n ↦ x (q * n + r)` (`0 < q`) is equidistributed for `μ`. -/
def TotallyAsympEquidistributed (x : ℕ → X) (μ : ProbabilityMeasure X) : Prop :=
  ∀ q r : ℕ, 0 < q → AsympEquidistributed (fun n ↦ x (q * n + r)) μ

/-- Definitional restatement of `TotallyAsympEquidistributed`. -/
theorem totallyAsympEquidistributed_def {x : ℕ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributed x μ ↔
      ∀ q r : ℕ, 0 < q → AsympEquidistributed (fun n ↦ x (q * n + r)) μ :=
  Iff.rfl

/-- Total equidistribution implies ordinary equidistribution (take `q = 1`, `r = 0`). -/
theorem TotallyAsympEquidistributed.asympEquidistributed {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) : AsympEquidistributed x μ := by
  simpa using hx 1 0 Nat.one_pos

/-- Total equidistribution is preserved upon passing to any positive-step arithmetic progression. -/
theorem TotallyAsympEquidistributed.comp_affine {x : ℕ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributed x μ) {q : ℕ} (hq : 0 < q) (r : ℕ) :
    TotallyAsympEquidistributed (fun n ↦ x (q * n + r)) μ := by
  intro q' r' hq'
  have heq : (fun n ↦ x (q * (q' * n + r') + r)) = fun n ↦ x ((q * q') * n + (q * r' + r)) :=
    funext fun n ↦ by ring_nf
  rw [heq]
  exact hx (q * q') (q * r' + r) (Nat.mul_pos hq hq')

/-- A constant sequence is totally equidistributed for its Dirac probability measure. -/
theorem totallyAsympEquidistributed_const (p : X) :
    TotallyAsympEquidistributed (fun _ ↦ p) (diracProba p) :=
  fun _ _ _ ↦ asympEquidistributed_const p

/-- A doubly infinite sequence `x : ℤ → X` is asymptotically equidistributed with respect to `μ`
when both halves `n ↦ x (n + 1)` and `n ↦ x (-(n + 1))` (`n : ℕ`) are equidistributed for `μ`. -/
def AsympEquidistributedInt (x : ℤ → X) (μ : ProbabilityMeasure X) : Prop :=
  AsympEquidistributed (fun n : ℕ ↦ x ((n : ℤ) + 1)) μ ∧
    AsympEquidistributed (fun n : ℕ ↦ x (-((n : ℤ) + 1))) μ

/-- Definitional restatement of `AsympEquidistributedInt`. -/
theorem asympEquidistributedInt_def {x : ℤ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributedInt x μ ↔
      AsympEquidistributed (fun n : ℕ ↦ x ((n : ℤ) + 1)) μ ∧
        AsympEquidistributed (fun n : ℕ ↦ x (-((n : ℤ) + 1))) μ :=
  Iff.rfl

/-- Bilateral equidistribution on `ℤ` is equivalent to equidistribution of both `n ↦ x n` and
`n ↦ x (-n)` on `ℕ`. -/
theorem asympEquidistributedInt_iff_natCast {x : ℤ → X} {μ : ProbabilityMeasure X} :
    AsympEquidistributedInt x μ ↔
      AsympEquidistributed (fun n : ℕ ↦ x n) μ ∧
        AsympEquidistributed (fun n : ℕ ↦ x (-(n : ℤ))) μ := by
  rw [asympEquidistributedInt_def,
    ← asympEquidistributed_comp_add_iff (fun n : ℕ ↦ x n) 1,
    ← asympEquidistributed_comp_add_iff (fun n : ℕ ↦ x (-(n : ℤ))) 1]
  simp

/-- Restriction of a bilaterally equidistributed sequence on `ℤ` to `ℕ` is equidistributed. -/
theorem AsympEquidistributedInt.natCast {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) : AsympEquidistributed (fun n : ℕ ↦ x n) μ :=
  (asympEquidistributedInt_iff_natCast.1 hx).1

/-- Restriction of a bilaterally equidistributed sequence on `ℤ` to nonpositive integers is
equidistributed. -/
theorem AsympEquidistributedInt.neg_natCast {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : AsympEquidistributedInt x μ) : AsympEquidistributed (fun n : ℕ ↦ x (-(n : ℤ))) μ :=
  (asympEquidistributedInt_iff_natCast.1 hx).2

/-- Modifying the value of a sequence `x : ℤ → X` at `0` does not change bilateral
equidistribution. -/
@[simp]
theorem asympEquidistributedInt_update_zero (x : ℤ → X) (y : X) (μ : ProbabilityMeasure X) :
    AsympEquidistributedInt (Function.update x 0 y) μ ↔ AsympEquidistributedInt x μ := by
  have h1 : (fun n : ℕ ↦ Function.update x 0 y ((n : ℤ) + 1)) = fun n : ℕ ↦ x ((n : ℤ) + 1) :=
    funext fun n ↦ Function.update_of_ne (by omega) _ _
  have h2 : (fun n : ℕ ↦ Function.update x 0 y (-((n : ℤ) + 1))) =
      fun n : ℕ ↦ x (-((n : ℤ) + 1)) :=
    funext fun n ↦ Function.update_of_ne (by omega) _ _
  rw [asympEquidistributedInt_def, asympEquidistributedInt_def, h1, h2]

/-- A doubly infinite sequence `x : ℤ → X` is totally asymptotically equidistributed with respect
to `μ` if `n ↦ x (q * n + r)` is bilaterally equidistributed for every `q ≥ 1` and `r : ℤ`. -/
def TotallyAsympEquidistributedInt (x : ℤ → X) (μ : ProbabilityMeasure X) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ r : ℤ, AsympEquidistributedInt (fun n ↦ x (q * n + r)) μ

/-- Definitional restatement of `TotallyAsympEquidistributedInt`. -/
theorem totallyAsympEquidistributedInt_def {x : ℤ → X} {μ : ProbabilityMeasure X} :
    TotallyAsympEquidistributedInt x μ ↔
      ∀ q : ℕ, 0 < q → ∀ r : ℤ, AsympEquidistributedInt (fun n ↦ x (q * n + r)) μ :=
  Iff.rfl

/-- Total equidistribution on `ℤ` implies ordinary bilateral equidistribution on `ℤ`. -/
theorem TotallyAsympEquidistributedInt.asympEquidistributedInt {x : ℤ → X}
    {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ) :
    AsympEquidistributedInt x μ := by
  simpa using hx 1 Nat.one_pos 0

/-- Total equidistribution on `ℤ` implies total equidistribution of its restriction to `ℕ`. -/
theorem TotallyAsympEquidistributedInt.totallyAsympEquidistributed_natCast {x : ℤ → X}
    {μ : ProbabilityMeasure X} (hx : TotallyAsympEquidistributedInt x μ) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ x n) μ := by
  intro q r hq
  simpa using (hx q hq r).natCast

/-- Total equidistribution on `ℤ` is preserved upon passing to any positive-step arithmetic
progression. -/
theorem TotallyAsympEquidistributedInt.comp_affine {x : ℤ → X} {μ : ProbabilityMeasure X}
    (hx : TotallyAsympEquidistributedInt x μ) {q : ℕ} (hq : 0 < q) (r : ℤ) :
    TotallyAsympEquidistributedInt (fun n ↦ x (q * n + r)) μ := by
  intro q' hq' r'
  have heq : (fun n : ℤ ↦ x (q * (q' * n + r') + r)) =
      fun n : ℤ ↦ x (((q * q' : ℕ) : ℤ) * n + (q * r' + r)) :=
    funext fun n ↦ by push_cast; ring_nf
  rw [heq]
  exact hx (q * q') (Nat.mul_pos hq hq') (q * r' + r)

end TotalAndInt

end TauCeti
