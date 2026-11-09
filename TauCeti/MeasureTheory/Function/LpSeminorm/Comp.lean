/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Precomposition by a map with dominated pushforward

Let `f : α → β` be almost everywhere measurable for `μ`. If `μ.map f ≤ C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν` for every `p`
(`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). The codomain only needs a continuous
extended norm. For a normed vector space codomain, `C < ⊤`, and `1 ≤ p`, this estimate gives
boundedness of precomposition from `Lᵖ(ν)` to `Lᵖ(μ)`, with norm at most `C ^ (1/p)`.

For a measure-preserving measurable embedding the bound is an equality, also after restricting to
the preimage of an arbitrary set (`MeasureTheory.MeasurePreserving.eLpNorm_comp_restrict_preimage`).

For `p = ∞` no bound on the pushforward is needed: precomposition with a quasi-measure-preserving
map, such as the projection `Prod.fst` from a product of σ-finite measures, preserves `L^∞`
(`MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`).

## Main declarations

* `MeasureTheory.eLpNorm_comp_le_of_map_le_smul`: the `eLpNorm` bound for precomposition.
* `MeasureTheory.MeasurePreserving.eLpNorm_comp_restrict_preimage`,
  `MeasureTheory.MeasurePreserving.memLp_comp_restrict_preimage_iff`: a measure-preserving
  measurable embedding `f` identifies the `Lᵖ` seminorm of `g ∘ f` on `f ⁻¹' s` with that of `g`
  on `s`.
* `MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`: precomposition with a
  quasi-measure-preserving map preserves `L^∞`.
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

/-- **Measure-preserving change of variables on a preimage.** If `f` is a measurable embedding
carrying `μ` to `ν`, then the `Lᵖ` seminorm of `g ∘ f` on `f ⁻¹' s` is that of `g` on `s`. Neither
`g` nor `s` needs to be measurable. -/
theorem MeasurePreserving.eLpNorm_comp_restrict_preimage (hf : MeasurePreserving f μ ν)
    (he : MeasurableEmbedding f) (g : β → ε) (p : ℝ≥0∞) (s : Set β) :
    eLpNorm (g ∘ f) p (μ.restrict (f ⁻¹' s)) = eLpNorm g p (ν.restrict s) := by
  rw [← he.eLpNorm_map_measure, (hf.restrict_preimage_emb he s).map_eq]

/-- **Measure-preserving change of variables in `Lᵖ` on a preimage.** If `f` is a measurable
embedding carrying `μ` to `ν`, then `g ∘ f` is `Lᵖ` on `f ⁻¹' s` exactly when `g` is `Lᵖ` on
`s`. -/
theorem MeasurePreserving.memLp_comp_restrict_preimage_iff (hf : MeasurePreserving f μ ν)
    (he : MeasurableEmbedding f) {g : β → ε} {p : ℝ≥0∞} {s : Set β} :
    MemLp (g ∘ f) p (μ.restrict (f ⁻¹' s)) ↔ MemLp g p (ν.restrict s) := by
  rw [← he.memLp_map_measure_iff, (hf.restrict_preimage_emb he s).map_eq]

/-- **Precomposition preserves `L^∞`.** If `g ∈ L^∞(ν)` and `f` is quasi-measure-preserving
from `μ` to `ν`, then `g ∘ f ∈ L^∞(μ)`. -/
theorem MemLp.comp_quasiMeasurePreserving_top (hg : MemLp g ∞ ν)
    (hf : QuasiMeasurePreserving f μ ν) : MemLp (g ∘ f) ∞ μ := by
  have hgm := hg.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_exponent_top hgm] at hg
  rw [memLp_iff, eLpNorm_exponent_top (hgm.comp_quasiMeasurePreserving hf)]
  exact (eLpNormEssSup_le_of_ae_enorm_bound (hf.ae ae_le_eLpNormEssSup)).trans_lt hg

end MeasureTheory
