/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Measures of intervals

Mathlib's `MeasureTheory.tendsto_measure_Ioc_atBot` lets the left endpoint of `(x, a]` go to
`-∞`. This file adds the analogous limits for `(x, a)` and `[x, a]`, and the right-continuity of
`x ↦ μ (-∞, x]` and `x ↦ μ (-∞, x)` at `a` from the right, where both tend to `μ (-∞, a]`.
Reflection exchanges the two open tails.

On `ℝ`, a uniform bound `C` on the mass of the unit windows `[a, a + 1]` bounds the mass of
longer windows linearly in their length, and so makes the measure locally finite.

## Main results

* `MeasureTheory.tendsto_measure_Ioo_atBot`, `MeasureTheory.tendsto_measure_Icc_atBot`:
  `μ (x, a) → μ (-∞, a)` and `μ [x, a] → μ (-∞, a]` as `x → -∞`.
* `MeasureTheory.tendsto_measure_Iio_nhdsGT`, `MeasureTheory.tendsto_measure_Iic_nhdsGT`:
  `μ (-∞, x) → μ (-∞, a]` and `μ (-∞, x] → μ (-∞, a]` as `x → a⁺`, provided some `μ (-∞, r)`,
  respectively `μ (-∞, r]`, with `r > a` is finite.
* `MeasureTheory.Measure.tendsto_measureReal_Icc_neg_mul_atTop`: the real mass of symmetric
  intervals with endpoints `±δx` tends to the total mass of a finite real measure when `δ > 0`.
* `MeasureTheory.Measure.map_neg_real_Ioi`: the right tail of a reflected measure is its left tail.
* `MeasureTheory.Measure.measure_Icc_add_natCast_le`,
  `MeasureTheory.Measure.isLocallyFiniteMeasure_of_measure_Icc_add_one_le`: a measure on `ℝ`
  whose unit windows `[a, a + 1]` have mass at most `C` gives `[a, a + n]` mass at most
  `(n + 1) * C`, and is locally finite.
-/

public section

open Set Filter
open scoped Topology ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section Preorder

variable [Preorder α] [(atBot : Filter α).IsCountablyGenerated]

/-- The measure of `(x, a)` tends to the measure of `(-∞, a)` as `x → -∞`. -/
theorem tendsto_measure_Ioo_atBot [NoMinOrder α] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioo x a)) atBot (𝓝 (μ (Iio a))) := by
  rw [← iUnion_Ioo_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioo antitone_const)

/-- The measure of `[x, a]` tends to the measure of `(-∞, a]` as `x → -∞`. -/
theorem tendsto_measure_Icc_atBot (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Icc x a)) atBot (𝓝 (μ (Iic a))) := by
  rw [← iUnion_Icc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Icc antitone_const)

end Preorder

section DenselyOrdered

variable [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [FirstCountableTopology α] [OpensMeasurableSpace α] {a : α}

/-- If some `μ (-∞, r)` with `r > a` is finite, then the measure of `(-∞, x)` tends to the
measure of `(-∞, a]` as `x → a⁺`. -/
theorem tendsto_measure_Iio_nhdsGT (hf : ∃ r > a, μ (Iio r) ≠ ∞) :
    Tendsto (fun x => μ (Iio x)) (𝓝[>] a) (𝓝 (μ (Iic a))) := by
  have h : ⋂ r > a, Iio r = Iic a := by
    ext x
    simp only [mem_iInter, mem_Iio, mem_Iic]
    exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense fun r hr => (h r hr).le,
      fun h r hr => h.trans_lt hr⟩
  rw [← h]
  exact tendsto_measure_biInter_gt (fun _ _ => measurableSet_Iio.nullMeasurableSet)
    (fun _ _ _ hij => Iio_subset_Iio hij) hf

/-- If some `μ (-∞, r]` with `r > a` is finite, then `x ↦ μ (-∞, x]` is right-continuous
at `a`. -/
theorem tendsto_measure_Iic_nhdsGT (hf : ∃ r > a, μ (Iic r) ≠ ∞) :
    Tendsto (fun x => μ (Iic x)) (𝓝[>] a) (𝓝 (μ (Iic a))) := by
  have h : ⋂ r > a, Iic r = Iic a := by
    ext x
    simp only [mem_iInter, mem_Iic]
    exact ⟨le_of_forall_gt_imp_ge_of_dense, fun h r hr => h.trans hr.le⟩
  rw [← h]
  exact tendsto_measure_biInter_gt (fun _ _ => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ _ hij => Iic_subset_Iic.2 hij) hf

end DenselyOrdered

/-- Reflection turns the real mass of an open right tail into that of the opposite left tail. -/
@[simp]
theorem Measure.map_neg_real_Ioi (μ : Measure ℝ) (x : ℝ) :
    (μ.map (fun y ↦ -y)).real (Ioi x) = μ.real (Iio (-x)) := by
  rw [map_measureReal_apply measurable_neg measurableSet_Ioi]
  congr 1
  ext y
  simp

/-- Symmetric intervals growing at any positive rate exhaust a finite measure on the real line.
Their real masses therefore tend to the total real mass. -/
theorem Measure.tendsto_measureReal_Icc_neg_mul_atTop (μ : Measure ℝ) [IsFiniteMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ ↦ μ.real (Icc (-(δ * x)) (δ * x))) atTop (𝓝 (μ.real univ)) := by
  have hcover : (⋃ x : ℝ, Icc (-x) x) = univ := by
    rw [iUnion_eq_univ_iff]
    intro x
    exact ⟨|x|, neg_abs_le x, le_abs_self x⟩
  have hm := tendsto_measure_iUnion_atTop
    (μ := μ) (fun x y (hxy : x ≤ y) ↦ Icc_subset_Icc (neg_le_neg hxy) hxy)
  rw [hcover] at hm
  exact ((ENNReal.tendsto_toReal (measure_ne_top μ univ)).comp hm).comp
    (tendsto_id.const_mul_atTop hδ)

namespace Measure

/-- A measure on `ℝ` whose unit windows `[a, a + 1]` have mass at most `C` gives every window
`[a, a + n]` of natural length `n` mass at most `(n + 1) * C`. -/
theorem measure_Icc_add_natCast_le {η : Measure ℝ} {C : ℝ≥0∞}
    (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C) (a : ℝ) (n : ℕ) :
    η (Icc a (a + n)) ≤ (n + 1) * C := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_add, one_mul]
    exact (measure_mono (Icc_subset_Icc_right (by linarith))).trans (hC a)
  | succ n ih =>
    calc η (Icc a (a + (n + 1 : ℕ)))
        ≤ η (Icc a (a + n) ∪ Icc (a + n) (a + n + 1)) := by
          refine measure_mono ?_
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
            Icc_subset_Icc_union_Icc (a := a) (b := a + n) (c := a + n + 1)
      _ ≤ (n + 1) * C + C := (measure_union_le _ _).trans (add_le_add ih (hC _))
      _ = ((n + 1 : ℕ) + 1) * C := by push_cast; ring

/-- A measure on `ℝ` with uniformly bounded mass on unit windows is locally finite. -/
theorem isLocallyFiniteMeasure_of_measure_Icc_add_one_le {η : Measure ℝ} {C : ℝ≥0}
    (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C) : IsLocallyFiniteMeasure η :=
  ⟨fun x ↦ ⟨Icc (x - 2⁻¹) (x - 2⁻¹ + 1), Icc_mem_nhds (by linarith) (by linarith),
    (hC _).trans_lt ENNReal.coe_lt_top⟩⟩

end Measure

end MeasureTheory
