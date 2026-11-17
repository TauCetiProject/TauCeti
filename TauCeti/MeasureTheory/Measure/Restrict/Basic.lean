/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Almost-everywhere vanishing outside the topological support

If the topological support `tsupport f` of a function `f : α → β` is contained in a set `s`, then
`f` vanishes everywhere on the open set `(tsupport f)ᶜ`, which contains `sᶜ` and is measurable in
any `OpensMeasurableSpace`. Consequently `f =ᵐ[μ.restrict sᶜ] 0` without any measurability
assumption on `s` or `f`.

The file also records the total mass of a rescaled restriction, and that normalized restrictions to
sets of positive mass, scaled by the smallest mass over their number, sum to at most the measure.

## Main results

* `MeasureTheory.Measure.smul_restrict_univ`: `(s • μ.restrict A) univ = s * μ A`.
* `MeasureTheory.Measure.smul_sum_inv_smul_restrict_le`: the normalized restrictions of a measure
  to finitely many sets, scaled by the smallest mass over their number, sum to at most the
  measure.
* `MeasureTheory.ae_restrict_compl_eq_zero_of_tsupport_subset`: if `tsupport f ⊆ s`, then
  `f =ᵐ[μ.restrict sᶜ] 0`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A function whose topological support lies in `s` vanishes almost everywhere on `sᶜ`. -/
theorem ae_restrict_compl_eq_zero_of_tsupport_subset {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [Zero β] {μ : Measure α} {s : Set α}
    {f : α → β} (hf : tsupport f ⊆ s) : f =ᵐ[μ.restrict sᶜ] 0 :=
  ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 hf) <|
    ae_restrict_of_forall_mem (isClosed_tsupport f).isOpen_compl.measurableSet fun _ hx ↦
      image_eq_zero_of_notMem_tsupport hx

namespace Measure

/-- The total mass of the restriction to `A` of a measure, rescaled by `s`. -/
theorem smul_restrict_univ {α : Type*} [MeasurableSpace α] (s : ℝ≥0∞) (μ : Measure α)
    (A : Set α) : (s • μ.restrict A) univ = s * μ A := by
  simp only [_root_.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]


/-- Scaling the normalized restrictions `(π (W i))⁻¹ • π.restrict (W i)` of a measure `π` by
`π (W j) / n`, where `W j` has minimal mass, and summing over `i : Fin n` stays below `π`. -/
theorem smul_sum_inv_smul_restrict_le {α : Type*} [MeasurableSpace α] {π : Measure α}
    {n : ℕ} {W : Fin n → Set α} {j : Fin n} (hj : ∀ i, π (W j) ≤ π (W i)) :
    (π (W j) / n) • Measure.sum (fun i ↦ (π (W i))⁻¹ • π.restrict (W i)) ≤ π := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact j.elim0
  refine Measure.le_iff.2 fun s hs ↦ ?_
  have hterm : ∀ i, π (W j) / n * ((π (W i))⁻¹ • π.restrict (W i)) s ≤ (n : ℝ≥0∞)⁻¹ * π s :=
    fun i ↦ by
    have hti : π (W j) / n * (π (W i))⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := by
      calc π (W j) / n * (π (W i))⁻¹ ≤ π (W i) / n * (π (W i))⁻¹ :=
            mul_le_mul_left (ENNReal.div_le_div_right (hj i) _) _
        _ ≤ (n : ℝ≥0∞)⁻¹ := by
            rw [div_eq_mul_inv, mul_right_comm]
            exact mul_le_of_le_one_left' (ENNReal.mul_inv_le_one _)
    calc π (W j) / n * ((π (W i))⁻¹ • π.restrict (W i)) s
        = π (W j) / n * (π (W i))⁻¹ * π (s ∩ W i) := by
          simp [Measure.restrict_apply hs, mul_assoc]
      _ ≤ (n : ℝ≥0∞)⁻¹ * π s := by gcongr; exact Set.inter_subset_left
  calc ((π (W j) / n) • Measure.sum (fun i ↦ (π (W i))⁻¹ • π.restrict (W i))) s
      = ∑ i, π (W j) / n * ((π (W i))⁻¹ • π.restrict (W i)) s := by
        simp [Finset.mul_sum]
    _ ≤ ∑ _i : Fin n, (n : ℝ≥0∞)⁻¹ * π s := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = π s := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn) (ENNReal.natCast_ne_top n), one_mul]

end Measure

end MeasureTheory
