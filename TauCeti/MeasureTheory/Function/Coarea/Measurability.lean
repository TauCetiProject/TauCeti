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

If `f` is Lipschitz (or, in a second-countable domain, locally Lipschitz) on `A` with values in a
finite-dimensional real normed space with additive Haar measure `μ`, and `A` is σ-compact up to a
`μH[m + t]`-null set, where `m` is the dimension of the target, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable: the fibers of the null part are
null for almost every `y` by Eilenberg's inequality. In particular this holds for any map locally
Lipschitz on a Lebesgue measurable subset `A` of a finite-dimensional real inner product space of
dimension `n` and the normalized Hausdorff measures `μHE[k]` with `n ≤ m + k`, which include the
coarea dimension `k = n - m`.

## Main declarations

* `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`,
  `LocallyLipschitzOn.aemeasurable_hausdorffMeasure_inter_preimage`: fiber measures of a Lipschitz
  (or, on a second-countable domain, locally Lipschitz) map are almost everywhere measurable on a
  set that is σ-compact up to a null set.
* `LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage`: the normalized fiber
  measures `μHE[k]` of a map locally Lipschitz on a Lebesgue measurable subset of an
  `n`-dimensional real inner product space into an `m`-dimensional real normed space are almost
  everywhere measurable when `n ≤ m + k`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4.1 (measurability of the fiber measures in the coarea formula).
-/

public section

open MeasureTheory Measure Set Filter Module
open scoped ENNReal NNReal

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

section FiberMeasurability

variable [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) {K : ℝ≥0} {t : ℝ}

/-- If `f` is continuous on a σ-compact subset `S ⊆ A` and almost every fiber of `A \ S` is
`μH[t]`-null, then `y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. -/
private theorem aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero {f : X → Y}
    {A S : Set X} (hSA : S ⊆ A) (hS : IsSigmaCompact S) (hf : ContinuousOn f S)
    (hnull : ∀ᵐ y ∂μ, μH[t] ((A \ S) ∩ f ⁻¹' {y}) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ := by
  refine (hS.measurable_hausdorffMeasure_inter_preimage hf t).aemeasurable.congr ?_
  filter_upwards [hnull] with y hy
  exact measure_eq_measure_of_null_sdiff (inter_subset_inter_left _ hSA)
    (by rwa [← inter_sdiff_distrib_right])

variable [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [μ.IsAddHaarMeasure]

/-- **Fiber measures of a Lipschitz map are almost everywhere measurable.** Let `f` be Lipschitz
on `A`, with values in an `m`-dimensional real normed space with additive Haar measure `μ`, and
let `t ≥ 0`. If `A` contains a σ-compact set `S` with `μH[m + t] (A \ S) = 0`, then
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable. -/
theorem LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage {f : X → Y} {A S : Set X}
    (hf : LipschitzOnWith K f A) (ht : 0 ≤ t) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ :=
  aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero μ hSA hS (hf.continuousOn.mono hSA)
    ((hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ ht hAS)

/-- **Fiber measures of a locally Lipschitz map on a second-countable domain are almost everywhere
measurable.** Let `f` be locally Lipschitz on `A`, with values in an `m`-dimensional real normed
space with additive Haar measure `μ`, and let `t ≥ 0`. If `A` contains a σ-compact set `S` with
`μH[m + t] (A \ S) = 0`, then `y ↦ μH[t] (A ∩ f ⁻¹' {y})` is `μ`-almost everywhere measurable.
Unlike `LipschitzOnWith.aemeasurable_hausdorffMeasure_inter_preimage`, this assumes
`[SecondCountableTopology X]` to cover `A \ S` by countably many Lipschitz pieces. -/
theorem LocallyLipschitzOn.aemeasurable_hausdorffMeasure_inter_preimage
    [SecondCountableTopology X] {f : X → Y} {A S : Set X}
    (hf : LocallyLipschitzOn A f) (ht : 0 ≤ t) (hSA : S ⊆ A) (hS : IsSigmaCompact S)
    (hAS : μH[finrank ℝ Y + t] (A \ S) = 0) :
    AEMeasurable (fun y ↦ μH[t] (A ∩ f ⁻¹' {y})) μ :=
  aemeasurable_hausdorffMeasure_inter_preimage_of_ae_eq_zero μ hSA hS (hf.continuousOn.mono hSA)
    ((hf.mono sdiff_subset).ae_hausdorffMeasure_inter_preimage_eq_zero μ ht hAS)

/-- **Normalized fiber measures of a locally Lipschitz map on a Lebesgue measurable set are almost
everywhere measurable.** Let `f` be locally Lipschitz on a Lebesgue measurable subset `A` of an
`n`-dimensional real inner product space, with values in an `m`-dimensional real normed space
with additive Haar measure `μ`. If `n ≤ m + k`, then `y ↦ μHE[k] (A ∩ f ⁻¹' {y})` is
`μ`-almost everywhere measurable. Neither openness of `A` nor a global Lipschitz bound is needed.
This applies to the coarea dimension `k = n - m`, for which `n ≤ m + k` is `le_add_tsub`. -/
theorem LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : E → Y} {A : Set E} (hf : LocallyLipschitzOn A f)
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
  simp only [euclideanHausdorffMeasure_def, _root_.smul_apply]
  exact (hf.aemeasurable_hausdorffMeasure_inter_preimage μ k.cast_nonneg hSA hS
    hnull).const_smul _

end FiberMeasurability
