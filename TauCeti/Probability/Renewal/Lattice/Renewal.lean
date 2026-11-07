/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.Probability.Renewal.Lattice.Basic
public import TauCeti.Probability.Renewal.Measure
public import TauCeti.MeasureTheory.Group.Convolution.MeasureSupport

/-!
# Lattice renewal measures and their increments

Convolution and convolution powers preserve concentration on the nonnegative multiples of a
fixed positive span. Consequently the renewal measure of a lattice law is concentrated on the
same lattice. The span need not be maximal, and no moment assumption is needed.

For span `a`, the interval `(n * a, (n + 1) * a]` contains only one possible renewal location.
Its renewal mass is the atom at `(n + 1) * a`, and the renewal function increases by exactly
that mass. This identifies the interval increments in the lattice renewal theorem with the
single-location masses represented by the renewal countdown chain.

The additive identity is stated in extended nonnegative reals, without a finiteness assumption.
The real subtraction identity requires local finiteness of the renewal measure. It therefore
applies to every probability interarrival law with mass at zero less than one. Increments at
zero are allowed: the atom at zero is not removed from the renewal function, but cancels from
each difference of its values.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI, the lattice renewal equation.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Pointwise

namespace MeasureTheory.Measure

variable {μ ν : Measure ℝ≥0} {a : ℝ≥0}

/-- Convolving two measures with the same lattice span preserves that span. -/
theorem IsLatticeSpan.conv [SFinite ν] (hμ : μ.IsLatticeSpan a) (hν : ν.IsLatticeSpan a) :
    (μ ∗ ν).IsLatticeSpan a := by
  refine ⟨hμ.pos, ae_mem_conv_of_ae_mem (countable_range _).measurableSet ?_
    hμ.ae_mem_range hν.ae_mem_range⟩
  rintro z ⟨x, ⟨m, rfl⟩, y, ⟨n, rfl⟩, rfl⟩
  exact ⟨m + n, by simp [Nat.cast_add, add_mul]⟩

/-- Every convolution power of a lattice measure has the same span, including the zeroth
power, the point mass at zero. -/
theorem IsLatticeSpan.convolutionPower [SFinite μ] (hμ : μ.IsLatticeSpan a) (n : ℕ) :
    (μ.convolutionPower n).IsLatticeSpan a := by
  induction n with
  | zero =>
    rw [convolutionPower_zero]
    refine ⟨hμ.pos, ?_⟩
    exact (ae_dirac_iff (countable_range _).measurableSet).2 ⟨0, by simp⟩
  | succ n ih =>
    rw [convolutionPower_succ]
    exact ih.conv hμ

/-- The renewal measure of a lattice measure is concentrated on the same lattice. This does
not require probability normalization or local finiteness. -/
theorem IsLatticeSpan.renewalMeasure [SFinite μ] (hμ : μ.IsLatticeSpan a) :
    μ.renewalMeasure.IsLatticeSpan a := by
  refine ⟨hμ.pos, ?_⟩
  rw [renewalMeasure_def, ae_sum_iff]
  exact fun n ↦ (hμ.convolutionPower n).ae_mem_range

/-- Between successive lattice times, the renewal function is constant. -/
theorem IsLatticeSpan.renewalFunction_eq_of_mem_Ico [SFinite μ] (hμ : μ.IsLatticeSpan a)
    {t : ℝ≥0} {n : ℕ} (ht : t ∈ Ico ((n : ℝ≥0) * a) ((n + 1 : ℕ) * a)) :
    μ.renewalFunction t = μ.renewalFunction ((n : ℝ≥0) * a) := by
  simp only [renewalFunction_def]
  exact (hμ.conv hμ.renewalMeasure).measure_Iic_eq_of_mem_Ico ht

/-- The renewal function increases from `n * a` to `(n + 1) * a` by the renewal mass of the
latter location. This additive form remains valid for infinite renewal masses. -/
theorem IsLatticeSpan.renewalFunction_succ_mul [SFinite μ] (hμ : μ.IsLatticeSpan a) (n : ℕ) :
    μ.renewalFunction ((n + 1 : ℕ) * a) =
      μ.renewalFunction ((n : ℝ≥0) * a) + μ.renewalMeasure {((n + 1 : ℕ) : ℝ≥0) * a} := by
  have hle : (n : ℝ≥0) * a ≤ ((n + 1 : ℕ) : ℝ≥0) * a := by
    gcongr
    exact_mod_cast n.le_succ
  have hpos : 0 < ((n + 1 : ℕ) : ℝ≥0) * a := mul_pos (by positivity) hμ.pos
  have hatom : μ.renewalMeasure {((n + 1 : ℕ) : ℝ≥0) * a} =
      (μ ∗ μ.renewalMeasure) {((n + 1 : ℕ) : ℝ≥0) * a} := by
    conv_lhs => rw [renewalMeasure_eq_dirac_add_conv, _root_.add_apply]
    rw [dirac_apply, indicator_of_notMem (by simpa using hpos.ne'), zero_add]
  rw [renewalFunction_def, ← Iic_union_Ioc_eq_Iic hle,
    measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
    (hμ.conv hμ.renewalMeasure).measure_Ioc_mul_eq_singleton, hatom, renewalFunction_def]

/-- For a locally finite lattice renewal measure, a real renewal-function increment equals
its singleton mass. Genuine zero-increment arrivals are included in both renewal-function
values and cancel in their difference. -/
theorem IsLatticeSpan.toReal_renewalFunction_sub_mul [SFinite μ]
    [IsLocallyFiniteMeasure μ.renewalMeasure] (hμ : μ.IsLatticeSpan a) (n : ℕ) :
    (μ.renewalFunction ((n + 1 : ℕ) * a)).toReal -
        (μ.renewalFunction ((n : ℝ≥0) * a)).toReal =
      μ.renewalMeasure.real {((n + 1 : ℕ) : ℝ≥0) * a} := by
  have hfin : μ.renewalFunction ((n : ℝ≥0) * a) ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (measure_Iic_lt_top (μ := μ.renewalMeasure) (a := (n : ℝ≥0) * a)).ne ?_
    rw [renewalMeasure_Iic]
    exact le_add_self
  rw [hμ.renewalFunction_succ_mul, ENNReal.toReal_add hfin measure_singleton_lt_top.ne,
    measureReal_def]
  ring

end MeasureTheory.Measure
