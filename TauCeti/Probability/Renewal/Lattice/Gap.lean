/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Lattice.Basic
public import TauCeti.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Positive lattice gaps in integer units

For an interarrival law with span `a`, division by `a` gives a natural-valued law.
The floor map makes this conversion total without changing any almost-sure values.
We compute its singleton masses and prove that multiplication by `a` recovers the
original measure.

When `μ {0} < 1`, conditioning away from zero first gives the natural-valued law of
positive gaps in units of `a`. Its atoms are precisely the positive lattice atoms
of the original law, with normalization factor `1 / (1 - μ {0})`.
The formulas also cover the degenerate law at zero, whose conditioning is the zero measure.
Consequently the gcd of its support is one exactly when `a` is the greatest span.
This supplies the gcd-one condition needed in lattice renewal aperiodicity arguments,
without excluding zero increments or requiring a finite mean.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*,
  vol. II, second edition, Wiley, 1971, Chapter XI.
-/

public section

open Set ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0} {a : ℝ≥0}

/-- In integer lattice units, the mass at `n` is the original mass at `n * a`. -/
@[simp]
theorem IsLatticeSpan.map_floor_div_apply_singleton (ha : μ.IsLatticeSpan a) (n : ℕ) :
    (μ.map (fun x ↦ ⌊x / a⌋₊)) {n} = μ {(n : ℝ≥0) * a} := by
  rw [map_apply (by fun_prop : Measurable (fun x : ℝ≥0 ↦ ⌊x / a⌋₊))
    (measurableSet_singleton n)]
  apply measure_congr
  filter_upwards [ha.ae_mem_range] with x ⟨k, hk⟩
  rw [← hk]
  simp [mul_div_cancel_right₀ _ ha.pos.ne', mul_left_inj' ha.pos.ne']

/-- Converting a lattice law to integer units and multiplying back recovers that law. -/
@[simp]
theorem IsLatticeSpan.map_mul_map_floor_div (ha : μ.IsLatticeSpan a) :
    (μ.map (fun x ↦ ⌊x / a⌋₊)).map (fun n : ℕ ↦ (n : ℝ≥0) * a) = μ := by
  rw [map_map (measurable_of_countable _)
    (by fun_prop : Measurable (fun x : ℝ≥0 ↦ ⌊x / a⌋₊))]
  conv_rhs => rw [← map_id (μ := μ)]
  apply map_congr
  filter_upwards [ha.ae_mem_range] with x ⟨n, hn⟩
  rw [← hn]
  simp [mul_div_cancel_right₀ _ ha.pos.ne']

/-- Removing zero increments and converting to integer units removes the zero atom and
divides every positive lattice atom by the probability of a nonzero increment. -/
@[simp]
theorem IsLatticeSpan.map_floor_div_cond_compl_zero_apply_singleton [IsProbabilityMeasure μ]
    (ha : μ.IsLatticeSpan a) (n : ℕ) :
    (μ[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)) {n} =
      if n = 0 then 0 else (1 - μ {0})⁻¹ * μ {(n : ℝ≥0) * a} := by
  rw [(ha.cond _).map_floor_div_apply_singleton]
  split_ifs with hn
  · simp [hn]
  · exact cond_compl_singleton_apply_singleton
      (mul_ne_zero (Nat.cast_ne_zero.2 hn) ha.pos.ne')

/-- The support of the positive integer gap law is exactly the positive lattice atoms.
This also holds for the degenerate law at zero, whose conditioned measure is zero. -/
theorem IsLatticeSpan.map_floor_div_cond_compl_zero_singleton_pos_iff [IsProbabilityMeasure μ]
    (ha : μ.IsLatticeSpan a) (n : ℕ) :
    0 < (μ[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)) {n} ↔
      0 < n ∧ 0 < μ {(n : ℝ≥0) * a} := by
  rw [ha.map_floor_div_cond_compl_zero_apply_singleton]
  by_cases hn : n = 0
  · simp [hn]
  · have hq : (1 - μ {0})⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    simp [hn, pos_iff_ne_zero, hq]

/-- A lattice span is greatest exactly when the support of the conditioned positive gap law,
expressed in integer units, has gcd one. This is the gcd-one condition needed in lattice
renewal aperiodicity arguments, and permits both zero increments and infinite mean. -/
theorem IsLatticeSpan.isGreatest_iff_setGcd_map_floor_div_cond_eq_one [IsProbabilityMeasure μ]
    (ha : μ.IsLatticeSpan a) :
    IsGreatest {b | μ.IsLatticeSpan b} a ↔
      Nat.setGcd {n : ℕ | 0 < (μ[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)) {n}} = 1 := by
  rw [isGreatest_setOf_isLatticeSpan_iff, and_iff_right ha]
  simp_rw [ha.map_floor_div_cond_compl_zero_singleton_pos_iff]

end MeasureTheory.Measure
