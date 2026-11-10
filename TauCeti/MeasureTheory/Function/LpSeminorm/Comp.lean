/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

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

## Main declarations

* `MeasureTheory.eLpNorm_comp_le_of_map_le_smul`: the `eLpNorm` bound for precomposition.
* `MeasureTheory.MemLp.comp_quasiMeasurePreserving_top`: precomposition with a
  quasi-measure-preserving map preserves `L^∞`.
* `MeasureTheory.eLpNorm_clm_comp_le`: postcomposition with a continuous linear map scales
  `eLpNorm` by at most its operator norm, with no measurability assumption.
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

/-- **`eLpNorm` bound for postcomposition.** A continuous linear map of the codomain scales
`eLpNorm` by at most its operator norm. No measurability assumption is needed: a function that
is not almost everywhere strongly measurable has infinite `eLpNorm`. -/
theorem eLpNorm_clm_comp_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {u : α → F} {p : ℝ≥0∞} (A : F →L[ℝ] G) :
    eLpNorm (fun x => A (u x)) p μ ≤ ‖A‖ₑ * eLpNorm u p μ := by
  by_cases hu : AEStronglyMeasurable u μ
  · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (A.continuous.comp_aestronglyMeasurable hu)
      (Filter.Eventually.of_forall fun x => by
        simpa only [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using
          A.le_opNNNorm (u x)) p
  · by_cases hA : A = 0
    · simp [hA]
    · rw [eLpNorm_of_not_aestronglyMeasurable hu, ENNReal.mul_top (by
        rw [enorm_eq_nnnorm]; exact ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hA))]
      exact le_top

end MeasureTheory
