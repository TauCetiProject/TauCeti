/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg
import TauCeti.MeasureTheory.Measure.Hausdorff
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Measurability of the fiber measures of a map

The coarea formula integrates the Hausdorff measures `y ↦ μH[t] (A ∩ f ⁻¹' {y})` of the fibers of
a map `f`. This file shows that this integrand is measurable, so that the formula is an identity
between genuine integrals, and so that it can be summed over a countable partition of `A`.

Fiber measures on compact and σ-compact sets are Borel measurable by
`IsCompact.measurable_hausdorffMeasure_inter_preimage` and
`IsSigmaCompact.measurable_hausdorffMeasure_inter_preimage` in
`TauCeti.MeasureTheory.Measure.Hausdorff`. This file extends them to measurable sets.

If `f` is Lipschitz on `A` with values in a finite-dimensional real normed space with additive
Haar measure `μ`, and `A` is σ-compact up to a `μH[m + t]`-null set, where `m` is the dimension
of the target, then `y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable: the fibers
of the null part are null for almost every `y` by Eilenberg's inequality. In particular this
holds for every Lebesgue measurable subset `A` of a finite-dimensional real inner product space
of dimension `n` and the normalized Hausdorff measures `μHE[k]` with `n ≤ m + k`, which include
the coarea dimension `k = n - m`.

## Main declarations

* `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`: fiber measures of a Lipschitz
  map are almost everywhere measurable on a set that is σ-compact up to a null set.
* `LipschitzOnWith.aemeasurable_euclideanHausdorffMeasure_inter_preimage`: the normalized fiber
  measures `μHE[k]` of a Lipschitz map on a Lebesgue measurable subset of a finite-dimensional
  real inner product space are almost everywhere measurable.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.1 (measurability of the fiber measures in the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module
open scoped ENNReal NNReal

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

section Lipschitz

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure] {K : ℝ≥0} {t : ℝ}

/-- **Fiber measures of a Lipschitz map are almost everywhere measurable.** Let `f` be Lipschitz
on `A`, with values in an `m`-dimensional real normed space with additive Haar measure `μ`, and
let `t ≥ 0`. If `A` contains a σ-compact set `S` with `μH[m + t] (A \ S) = 0`, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. -/
theorem LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage {f : X → Y} {A S : Set X}
    (hf : LipschitzOnWith K f A) (ht : 0 ≤ t) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ := by
  refine (hS.measurable_hausdorffMeasure_inter_preimage (hf.continuousOn.mono hSA)
    t).aemeasurable.congr ?_
  -- By Eilenberg's inequality, almost every fiber of the null part `A \ S` is null.
  filter_upwards [(hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ ht hAS]
    with y hy
  refine le_antisymm (measure_mono (inter_subset_inter_left _ hSA)) ?_
  calc μH[t] (A ∩ f ⁻¹' {y}) ≤ μH[t] (S ∩ f ⁻¹' {y}) + μH[t] ((A \ S) ∩ f ⁻¹' {y}) := by
        refine (measure_mono ?_).trans (measure_union_le _ _)
        rw [← union_inter_distrib_right, union_sdiff_self]
        exact inter_subset_inter_left _ subset_union_right
    _ = μH[t] (S ∩ f ⁻¹' {y}) := by rw [hy, add_zero]

/-- **Normalized fiber measures of a Lipschitz map on a Lebesgue measurable set are almost
everywhere measurable.** Let `f` be Lipschitz on a Lebesgue measurable subset `A` of an
`n`-dimensional real inner product space, with values in an `m`-dimensional real normed space
with additive Haar measure `μ`. If `n ≤ m + k`, then `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` is
`μ`-almost everywhere measurable. This applies to the coarea dimension `k = n - m`, for which
`n ≤ m + k` is `le_add_tsub`. -/
theorem LipschitzOnWith.aemeasurable_euclideanHausdorffMeasure_inter_preimage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : E → Y} {A : Set E} (hf : LipschitzOnWith K f A)
    (hA : NullMeasurableSet A) {k : ℕ} (hk : finrank ℝ E ≤ finrank ℝ Y + k) :
    AEMeasurable (fun y ↦ μHE[k] (A ∩ f ⁻¹' {y})) μ := by
  obtain ⟨S, hSA, hS, hSA'⟩ := hA.exists_isSigmaCompact_subset_ae_eq
  -- The null part `A \ S` is null for the `n`-dimensional, hence the `(m + k)`-dimensional,
  -- Hausdorff measure.
  have hnull : μH[finrank ℝ Y + (k : ℝ)] (A \ S) = 0 := by
    have h := (ae_eq_set.1 hSA').2
    rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      euclideanHausdorffMeasure_eq_zero_iff] at h
    exact nonpos_iff_eq_zero.1 ((hausdorffMeasure_mono (by exact_mod_cast hk) _).trans h.le)
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply]
  exact (hf.aemeasurable_hausdorffMeasure_inter_preimage μ k.cast_nonneg hSA hS
    hnull).const_smul _

end Lipschitz
