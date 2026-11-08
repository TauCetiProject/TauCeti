/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.EmpiricalMeasure.Basic
public import TauCeti.Analysis.Normed.BoundedContinuousFunction.FiniteAverage

/-!
# Removing one point from an empirical measure

Deleting one point from a finite population of size `n + 2` changes the average of a
bounded continuous test function by at most `2 * ‖f‖ / (n + 2)`. The deleted point is
arbitrary, and repeated values are counted with multiplicity. In particular, the bound
applies to the removal of one eigenvalue from an empirical spectral measure.

Bounded-continuous-test convergence in probability transfers to the retained population,
including for triangular arrays on different probability spaces.
-/

public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

namespace TauCeti.Probability

/-- Removing any one value changes a bounded continuous test integral by at most
`2 * ‖f‖ / (n + 2)`. -/
theorem abs_integral_empiricalMeasureOfFintype_sub_succAbove_le
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (n : ℕ) (x : Fin (n + 2) → α) (i : Fin (n + 2)) (f : α →ᵇ ℝ) :
    |(∫ y, f y ∂(empiricalMeasureOfFintype x : Measure α)) -
      (∫ y, f y ∂(empiricalMeasureOfFintype (x ∘ i.succAbove) : Measure α))| ≤
      2 * ‖f‖ / (n + 2 : ℝ) := by
  rw [integral_empiricalMeasureOfFintype f.continuous.stronglyMeasurable,
    integral_empiricalMeasureOfFintype f.continuous.stronglyMeasurable]
  simp only [Fintype.card_fin, smul_eq_mul, Function.comp_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, mul_comm,
    Function.comp_def] using
    BoundedContinuousFunction.abs_average_insert_sub n (x i) (x ∘ i.succAbove) f

/-- A bounded-continuous-test limit in probability survives deleting any one observation,
including a sample-dependent choice and varying underlying measure spaces. -/
theorem tendsto_integral_empiricalMeasureOfFintype_succAbove_probability
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n))
    (x : (n : ℕ) → Ω n → Fin (n + 2) → α)
    (i : (n : ℕ) → Ω n → Fin (n + 2)) (f : α →ᵇ ℝ) (L : ℝ)
    (hfull : ∀ ε > 0, Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ y, f y ∂(empiricalMeasureOfFintype (x n ω) : Measure α)) - L|})
      atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ y, f y ∂(empiricalMeasureOfFintype (x n ω ∘ (i n ω).succAbove) :
        Measure α)) - L|}) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ ↦ 2 * ‖f‖ / (n + 2 : ℝ)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have h := tendsto_inv_atTop_zero.comp hden
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using h.const_mul (2 * ‖f‖)
  have hevent : ∀ᶠ n : ℕ in atTop, 2 * ‖f‖ / (n + 2 : ℝ) < ε / 2 :=
    hd.eventually (Iio_mem_nhds (by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hfull (ε / 2) (by positivity))
  · filter_upwards with n
    exact bot_le
  · filter_upwards [hevent] with n hn
    apply measure_mono
    intro ω hω
    have hdiff := abs_integral_empiricalMeasureOfFintype_sub_succAbove_le
      n (x n ω) (i n ω) f
    have hbound := abs_sub_le
      (∫ y, f y ∂(empiricalMeasureOfFintype (x n ω ∘ (i n ω).succAbove) : Measure α))
      (∫ y, f y ∂(empiricalMeasureOfFintype (x n ω) : Measure α)) L
    rw [abs_sub_comm
      (∫ y, f y ∂(empiricalMeasureOfFintype (x n ω ∘ (i n ω).succAbove) : Measure α))
      (∫ y, f y ∂(empiricalMeasureOfFintype (x n ω) : Measure α))] at hbound
    change ε / 2 ≤ |(∫ y, f y ∂(empiricalMeasureOfFintype (x n ω) : Measure α)) - L|
    change ε ≤ |(∫ y, f y ∂(empiricalMeasureOfFintype
      (x n ω ∘ (i n ω).succAbove) : Measure α)) - L| at hω
    linarith

end TauCeti.Probability
