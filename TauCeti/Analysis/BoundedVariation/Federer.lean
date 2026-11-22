/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.EssentialBoundary
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Federer's `0`–`1/2`–`1` density theorem

Let `E` be a finite-dimensional real inner product space of dimension `n` carrying an additive Haar
measure `μ`, and let `s` be a set of locally finite perimeter in an open set `Ω ⊆ E`. Here `n - 1`
denotes truncated natural subtraction (so `0 - 1 = 0` when `n = 0`, where `μHE[0]` is
zero-dimensional Hausdorff / counting measure). By
`TauCeti.essentialBoundary_inter_ae_eq_reducedBoundary`, the essential boundary `∂ᵉs ∩ Ω` agrees
`μHE[n - 1]`-almost everywhere with the reduced boundary `∂*s`, where `s` has density `1 / 2`
(`TauCeti.hasDensityAt_of_mem_reducedBoundary`). This file deduces:

* `TauCeti.ae_hasDensityAt_of_mem_essentialBoundary`: `μHE[n - 1]`-almost every point of
  `∂ᵉs ∩ Ω` has density `1 / 2`;
* `TauCeti.ae_hasDensityAt_zero_or_one_half_or_one` (and its finite-perimeter specializations):
  **Federer's `0`–`1/2`–`1` density theorem**, stating that at `μHE[n - 1]`-almost every point of
  `Ω`, `s` has density `0`, `1 / 2`, or `1`.

## References

* H. Federer, *Geometric Measure Theory*, §4.5.6.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 16.2.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.8, Theorem 5.17.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.61.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric Module
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E}

/-- **Density one half almost everywhere on the essential boundary.** For a set `s` of locally
finite perimeter in `Ω` against an additive Haar measure `μ`, `s` has density `1 / 2` at
`μHE[n - 1]`-almost every point of `∂ᵉs ∩ Ω`, where `n = dim E` and `n - 1` is truncated natural
subtraction (so `0 - 1 = 0` when `n = 0`). -/
theorem ae_hasDensityAt_of_mem_essentialBoundary
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω → x ∈ essentialBoundary μ s → HasDensityAt μ s x (1 / 2) := by
  filter_upwards [eventuallyEqSet_iff.1
    (essentialBoundary_inter_ae_eq_reducedBoundary hu hfin)] with x hx hxΩ hxeb
  exact hasDensityAt_of_mem_reducedBoundary (hx.1 ⟨hxeb, hxΩ⟩)

/-- **Federer's `0`–`1/2`–`1` density theorem.** For a set `s` of locally finite perimeter in an
open set `Ω` against an additive Haar measure `μ`, at `μHE[n - 1]`-almost every point of `Ω` the set
`s` has density `0`, `1 / 2`, or `1`, where `n = dim E` and `n - 1` is truncated natural subtraction
(so `0 - 1 = 0` when `n = 0`). -/
theorem ae_hasDensityAt_zero_or_one_half_or_one
    (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U (s.indicator 1) ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω →
      HasDensityAt μ s x 0 ∨ HasDensityAt μ s x (1 / 2) ∨ HasDensityAt μ s x 1 := by
  filter_upwards [ae_hasDensityAt_of_mem_essentialBoundary hu hfin] with x hx hxΩ
  by_cases h0 : HasDensityAt μ s x 0
  · exact .inl h0
  · by_cases h1 : HasDensityAt μ s x 1
    · exact .inr (.inr h1)
    · exact .inr (.inl (hx hxΩ
        (mem_essentialBoundary.2 ⟨mt mem_essentialInterior.1 h1, mt mem_essentialExterior.1 h0⟩)))

/-- **Federer's `0`–`1/2`–`1` density theorem** for a set of finite perimeter in `Ω`: if `s` is
null-measurable on `Ω` and `P(s; Ω) ≠ ∞`, then at `μHE[n - 1]`-almost every `x ∈ Ω` the set `s`
has density `0`, `1 / 2`, or `1`, where `n = dim E` and `n - 1` is truncated natural subtraction (so
`0 - 1 = 0` when `n = 0`). -/
theorem ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_ne_top
    (hs : NullMeasurableSet s (μ.restrict Ω)) (hP : perimeter μ Ω s ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1], x ∈ Ω →
      HasDensityAt μ s x 0 ∨ HasDensityAt μ s x (1 / 2) ∨ HasDensityAt μ s x 1 :=
  ae_hasDensityAt_zero_or_one_half_or_one (locallyIntegrableOn_indicator_const hs 1)
    fun _ _ hKΩ => ⟨Ω, hKΩ, by rwa [← perimeter_def]⟩

/-- **Federer's `0`–`1/2`–`1` density theorem** for a set of finite perimeter in the whole space:
if `s` is null-measurable and `P(s; ⊤) ≠ ∞`, then at `μHE[n - 1]`-almost every `x : E` the set `s`
has density `0`, `1 / 2`, or `1`, where `n = dim E` and `n - 1` is truncated natural subtraction (so
`0 - 1 = 0` when `n = 0`). -/
theorem ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_top_ne_top
    (hs : NullMeasurableSet s μ) (hP : perimeter μ ⊤ s ≠ ∞) :
    ∀ᵐ x ∂μHE[finrank ℝ E - 1],
      HasDensityAt μ s x 0 ∨ HasDensityAt μ s x (1 / 2) ∨ HasDensityAt μ s x 1 := by
  filter_upwards [ae_hasDensityAt_zero_or_one_half_or_one_of_perimeter_ne_top (Ω := ⊤)
    (hs.mono Measure.restrict_le_self) hP] with x hx
  exact hx (Opens.mem_top x)

end TauCeti

end
