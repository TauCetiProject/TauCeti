/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Integral.IntegrableOn
import TauCeti.Algebra.Order.Field.Basic

/-!
# The Kantorovich inequality

For data in an interval `[m, M]` with `0 < m`, the product of the mean and the mean of the
reciprocals is at most `(M + m) ^ 2 / (4 * M * m)`. This file proves the inequality for a
probability measure and for finite weights, and shows that the bound is attained.

## Main results

* `TauCeti.integral_mul_integral_inv_le`: the Kantorovich inequality for a probability measure:
  if `m ≤ f ≤ M` almost everywhere with `0 < m`, then
  `(∫ f) * (∫ f⁻¹) ≤ (M + m) ^ 2 / (4 * M * m)`.
* `TauCeti.sum_mul_mul_sum_div_le`: the finite weighted form, for nonnegative weights summing
  to `1`, in a linearly ordered field.
* `TauCeti.integral_mul_integral_inv_half_dirac_add_dirac`: the bound is attained by the law
  giving mass `1 / 2` to each of `m` and `M`.

The integral and finite forms combine two ordered-field lemmas from
`TauCeti.Algebra.Order.Field.Basic`: integrating or summing `t + m * M / t ≤ m + M`
(`TauCeti.add_mul_div_le_add`) gives `A + m * M * B ≤ m + M` for the two means `A` and `B`, and
`TauCeti.mul_le_sq_div_of_add_mul_le` turns this into the bound on `A * B`.

## References

* P. S. Bullen, *Handbook of Means and Their Inequalities*, Ch. III, Thm 5(a), p. 235.

The proofs were written for Tau Ceti with AI assistance (Claude).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The Kantorovich inequality for a probability measure: if `m ≤ f ≤ M` almost everywhere with
`0 < m`, then `(∫ f) * (∫ f⁻¹) ≤ (M + m) ^ 2 / (4 * M * m)`. -/
theorem integral_mul_integral_inv_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {m M : ℝ} (hm : 0 < m)
    (hfb : ∀ᵐ a ∂μ, f a ∈ Icc m M) :
    (∫ a, f a ∂μ) * (∫ a, (f a)⁻¹ ∂μ) ≤ (M + m) ^ 2 / (4 * M * m) := by
  obtain ⟨a, hma, haM⟩ := hfb.exists
  have hM : 0 < M := hm.trans_le (hma.trans haM)
  by_cases hfi : Integrable f μ
  swap
  · rw [integral_undef hfi, zero_mul]
    positivity
  have hfi' : Integrable (fun a ↦ (f a)⁻¹) μ := by
    refine Integrable.of_bound hfi.aemeasurable.inv.aestronglyMeasurable m⁻¹ ?_
    filter_upwards [hfb] with a ha
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hm.trans_le ha.1)]
    exact inv_anti₀ hm ha.1
  -- Integrate `f + m * M * f⁻¹ ≤ m + M`.
  have hsum : ∫ a, f a ∂μ + m * M * ∫ a, (f a)⁻¹ ∂μ ≤ m + M := by
    rw [← integral_const_mul, ← integral_add hfi (hfi'.const_mul _)]
    refine (integral_mono_ae (hfi.add (hfi'.const_mul _)) (integrable_const (m + M)) ?_).trans
      (by simp)
    filter_upwards [hfb] with a ha
    simpa [div_eq_mul_inv] using add_mul_div_le_add (hm.trans_le ha.1) ha.1 ha.2
  have h1 : 0 ≤ ∫ a, f a ∂μ := integral_nonneg_of_ae <| by
    filter_upwards [hfb] with a ha using hm.le.trans ha.1
  have h2 : 0 ≤ ∫ a, (f a)⁻¹ ∂μ := integral_nonneg_of_ae <| by
    filter_upwards [hfb] with a ha using inv_nonneg.2 (hm.le.trans ha.1)
  rw [mul_assoc]
  exact mul_le_sq_div_of_add_mul_le (mul_pos hM hm) (by positivity) (by linarith)

/-- The finite weighted Kantorovich inequality: for nonnegative weights `w` summing to `1` on
`s` and `m ≤ x i ≤ M` on `s` with `0 < m`,
`(∑ i ∈ s, w i * x i) * (∑ i ∈ s, w i / x i) ≤ (M + m) ^ 2 / (4 * M * m)`. -/
theorem sum_mul_mul_sum_div_le {K ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : Finset ι} {w x : ι → K} {m M : K} (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    (hm : 0 < m) (hx : ∀ i ∈ s, x i ∈ Icc m M) :
    (∑ i ∈ s, w i * x i) * (∑ i ∈ s, w i / x i) ≤ (M + m) ^ 2 / (4 * M * m) := by
  obtain ⟨i, hi⟩ : s.Nonempty := Finset.nonempty_of_sum_ne_zero (hw1 ▸ one_ne_zero)
  have hM : 0 < M := hm.trans_le ((hx i hi).1.trans (hx i hi).2)
  -- Sum `w i * (x i + m * M / x i) ≤ w i * (m + M)`.
  have hsum : ∑ i ∈ s, w i * x i + m * M * ∑ i ∈ s, w i / x i ≤ m + M := by
    calc ∑ i ∈ s, w i * x i + m * M * ∑ i ∈ s, w i / x i
        = ∑ i ∈ s, w i * (x i + m * M / x i) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ ∑ i ∈ s, w i * (m + M) := Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
          (add_mul_div_le_add (hm.trans_le (hx i hi).1) (hx i hi).1 (hx i hi).2) (hw i hi)
      _ = m + M := by rw [← Finset.sum_mul, hw1, one_mul]
  have h1 : 0 ≤ ∑ i ∈ s, w i * x i := Finset.sum_nonneg fun i hi ↦
    mul_nonneg (hw i hi) (hm.le.trans (hx i hi).1)
  have h2 : 0 ≤ ∑ i ∈ s, w i / x i := Finset.sum_nonneg fun i hi ↦
    div_nonneg (hw i hi) (hm.le.trans (hx i hi).1)
  rw [mul_assoc]
  exact mul_le_sq_div_of_add_mul_le (mul_pos hM hm) (by positivity) (by linarith)

/-- The Kantorovich bound is attained: for nonzero `m` and `M`, the law giving mass `1 / 2` to
each of `m` and `M` has `(∫ x) * (∫ x⁻¹) = (M + m) ^ 2 / (4 * M * m)`. -/
theorem integral_mul_integral_inv_half_dirac_add_dirac {m M : ℝ} (hm : m ≠ 0) (hM : M ≠ 0) :
    (∫ x, x ∂((2⁻¹ : ℝ≥0∞) • (Measure.dirac m + Measure.dirac M))) *
        (∫ x, x⁻¹ ∂((2⁻¹ : ℝ≥0∞) • (Measure.dirac m + Measure.dirac M))) =
      (M + m) ^ 2 / (4 * M * m) := by
  simp only [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    smul_eq_mul]
  field_simp
  ring

end TauCeti
