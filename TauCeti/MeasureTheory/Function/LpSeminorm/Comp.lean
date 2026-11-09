/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Precomposition by a map with dominated pushforward

Let `f : α → β` be almost everywhere measurable for `μ`. If `μ.map f ≤ C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν` for every `p`
(`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). The codomain only needs a continuous
extended norm. For a normed vector space codomain, `C < ⊤`, and `1 ≤ p`, this estimate gives
boundedness of precomposition from `Lᵖ(ν)` to `Lᵖ(μ)`, with norm at most `C ^ (1/p)`.

For `p = ∞` no bound on the pushforward is needed: precomposition with a quasi-measure-preserving
map, such as the projection `Prod.fst` from a product of σ-finite measures, preserves `L^∞`
(`MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`).

For counting measures, precomposition by a map that is injective on the support does not increase
`eLpNorm`. This is the `ℓᵖ` estimate for shifted and reindexed sequences
(`MeasureTheory.eLpNorm_count_le_of_injOn`), and each term of a sequence is at most its `ℓᵖ` norm
(`MeasureTheory.le_eLpNorm_count`).

## Main declarations

* `MeasureTheory.eLpNorm_comp_le_of_map_le_smul`: the `eLpNorm` bound for precomposition.
* `MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`: precomposition with a
  quasi-measure-preserving map preserves `L^∞`.
* `MeasureTheory.eLpNorm_count_le_of_injOn`: the `ℓᵖ` norm of `f` is at most that of `g` when
  `f ≤ g ∘ e` with `e` injective on the support of `f`.
* `MeasureTheory.le_eLpNorm_count`: each term of a sequence is at most its `ℓᵖ` norm.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace ε]
  [ContinuousENorm ε] {μ : Measure α} {ν : Measure β} {f : α → β} {g : β → ε}

/-- **`eLpNorm` bound for precomposition.** If `f` pushes `μ` forward to at most `C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν`. No measurability assumption on `g` is
needed: its `eLpNorm` is infinite when it is not almost everywhere strongly measurable. -/
theorem eLpNorm_comp_le_of_map_le_smul {C : ℝ≥0∞} (hf : AEMeasurable f μ) (hmap : μ.map f ≤ C • ν)
    (p : ℝ≥0∞) :
    eLpNorm (g ∘ f) p μ ≤ C ^ (1 / p).toReal * eLpNorm g p ν := by
  by_cases hC : C = 0
  · have hμ : μ = 0 := (Measure.map_eq_zero_iff hf).1
      (le_antisymm (by simpa [hC] using hmap) bot_le)
    simp [hμ]
  by_cases hg : AEStronglyMeasurable g ν
  · rw [← eLpNorm_map_measure (hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)) hf]
    exact eLpNorm_le_of_measure_le_smul hmap
  rw [eLpNorm_of_not_aestronglyMeasurable hg,
    ENNReal.mul_top (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hC)
      ENNReal.toReal_nonneg).ne']
  exact le_top

/-- **Precomposition preserves `L^∞`.** If `g ∈ L^∞(ν)` and `f` is quasi-measure-preserving
from `μ` to `ν`, then `g ∘ f ∈ L^∞(μ)`. -/
theorem MemLp.comp_quasiMeasurePreserving_top (hg : MemLp g ∞ ν)
    (hf : QuasiMeasurePreserving f μ ν) : MemLp (g ∘ f) ∞ μ := by
  have hgm := hg.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_exponent_top hgm] at hg
  rw [memLp_iff, eLpNorm_exponent_top (hgm.comp_quasiMeasurePreserving hf)]
  exact (eLpNormEssSup_le_of_ae_enorm_bound (hf.ae ae_le_eLpNormEssSup)).trans_lt hg

/-- **`ℓᵖ` norms under reindexing.** On countable types with counting measures, if `f a ≤ g (e a)`
for every `a`, and `e` is injective on the support of `f`, then the `ℓᵖ` norm of `f` is at most that
of `g`, for every `p`. For instance, shifting a sequence on `ℕ` to the left or to the right, padding
it with zeros, does not increase its `ℓᵖ` norm. -/
theorem eLpNorm_count_le_of_injOn {α' β' : Type*} [MeasurableSpace α'] [MeasurableSingletonClass α']
    [Countable α'] [MeasurableSpace β'] [MeasurableSingletonClass β'] [Countable β']
    {f : α' → ℝ≥0∞} {g : β' → ℝ≥0∞} {e : α' → β'} (he : Set.InjOn e (Function.support f))
    (hfg : ∀ a, f a ≤ g (e a)) (p : ℝ≥0∞) : eLpNorm f p .count ≤ eLpNorm g p .count := by
  have hf : AEStronglyMeasurable f .count := (measurable_of_countable f).aestronglyMeasurable
  have hg : AEStronglyMeasurable g .count := (measurable_of_countable g).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm_exponent_zero hf]
  rcases eq_or_ne p ∞ with rfl | hp
  · simp only [eLpNorm_exponent_top hf, eLpNorm_exponent_top hg, eLpNormEssSup_count,
      enorm_eq_self]
    exact iSup_le fun a ↦ (hfg a).trans (le_iSup g (e a))
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hg, lintegral_count, enorm_eq_self]
  gcongr
  calc ∑' a, f a ^ p.toReal = ∑' a : Function.support f, f a ^ p.toReal :=
        (tsum_subtype_eq_of_support_subset fun a ha ↦ by
          contrapose ha
          simp [Function.notMem_support.1 ha, ENNReal.zero_rpow_of_pos hr]).symm
    _ ≤ ∑' a : Function.support f, g (e a) ^ p.toReal :=
        tsum_le_tsum fun a ↦ by gcongr; exact hfg a
    _ ≤ ∑' b, g b ^ p.toReal :=
        tsum_comp_le_tsum_of_injective he.injective fun b ↦ g b ^ p.toReal

/-- **A term of a sequence is at most its `ℓᵖ` norm.** On a countable type with counting measure,
`f a ≤ ‖f‖_p` for every `a` and every `p ≠ 0`. -/
theorem le_eLpNorm_count {α' : Type*} [MeasurableSpace α'] [MeasurableSingletonClass α']
    [Countable α'] (f : α' → ℝ≥0∞) {p : ℝ≥0∞} (hp0 : p ≠ 0) (a : α') :
    f a ≤ eLpNorm f p .count := by
  have hf : AEStronglyMeasurable f .count := (measurable_of_countable f).aestronglyMeasurable
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLpNorm_exponent_top hf, eLpNormEssSup_count]
    exact le_iSup (fun a ↦ ‖f a‖ₑ) a
  have hr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf, lintegral_count, one_div]
  calc f a = (f a ^ p.toReal) ^ p.toReal⁻¹ := (ENNReal.rpow_rpow_inv hr _).symm
    _ ≤ (∑' b, ‖f b‖ₑ ^ p.toReal) ^ p.toReal⁻¹ := by
        gcongr
        exact le_tsum (fun b ↦ ‖f b‖ₑ ^ p.toReal) a

end MeasureTheory
