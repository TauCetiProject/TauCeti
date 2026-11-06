/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Filter operations for convergence in distribution

Mathlib defines `MeasureTheory.TendstoInDistribution X l Z μ μ'` along an arbitrary filter `l`,
packaging pointwise almost-everywhere measurability together with weak convergence of the laws in
`MeasureTheory.ProbabilityMeasure`. This file supplies basic filter operations for
`TendstoInDistribution`: precomposition along a `Filter.Tendsto` map of indices, monotonicity in the
index filter, eventual almost-everywhere congruence along the filter, and the sequential
characterization for countably generated index filters.

## Main statements

* `MeasureTheory.TendstoInDistribution.comp_tendsto` — precompose the index along a filter limit.
* `MeasureTheory.TendstoInDistribution.mono_left` — weaken the index filter.
* `MeasureTheory.TendstoInDistribution.congr'` — replace random variables eventually almost
  everywhere along the index filter.
* `MeasureTheory.tendstoInDistribution_iff_forall_seq_tendsto` — along a countably generated filter,
  convergence in distribution is equivalent to convergence in distribution along every sequence
  tending to the filter.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory

variable {ι κ E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Precomposing the index of a family of random variables with a function tending to `l` preserves
convergence in distribution. -/
protected theorem TendstoInDistribution.comp_tendsto {l : Filter ι} {l' : Filter κ}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {f : κ → ι}
    (h : TendstoInDistribution X l Z μ μ') (hf : Tendsto f l' l) :
    TendstoInDistribution (fun k ↦ X (f k)) l' Z (fun k ↦ μ (f k)) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (f k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hf

/-- Convergence in distribution is monotone in the index filter. -/
protected theorem TendstoInDistribution.mono_left {l₁ l₂ : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l₂ Z μ μ') (hl : l₁ ≤ l₂) :
    TendstoInDistribution X l₁ Z μ μ' :=
  h.comp_tendsto (tendsto_id'.2 hl)

/-- Convergence in distribution is preserved when the random variables are modified on null sets
eventually along the index filter and at the limit. Pointwise almost-everywhere measurability of
the replacement family is required at all indices because `TendstoInDistribution` records it
globally. -/
protected theorem TendstoInDistribution.congr' {l : Filter ι}
    {X Y : (i : ι) → Ω i → E} {Z T : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ') (hY : ∀ i, AEMeasurable (Y i) (μ i))
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) :
    TendstoInDistribution Y l T μ μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit.congr hZT
  tendsto := by
    have hlim : (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) = ⟨μ'.map T, inferInstance⟩ :=
      Subtype.ext (Measure.map_congr hZT)
    rw [← hlim]
    refine h.tendsto.congr' ?_
    filter_upwards [hXY] with i hi
    exact Subtype.ext (Measure.map_congr hi)

/-- Along a countably generated filter, convergence in distribution is equivalent to convergence in
distribution along every sequence tending to that filter. -/
theorem tendstoInDistribution_iff_forall_seq_tendsto {l : Filter ι} [l.IsCountablyGenerated]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ u : ℕ → ι, Tendsto u atTop l →
        TendstoInDistribution (fun n ↦ X (u n)) atTop Z (fun n ↦ μ (u n)) μ' where
  mp h _ hu := h.comp_tendsto hu
  mpr h :=
    { forall_aemeasurable := hX
      aemeasurable_limit := hZ
      tendsto := tendsto_iff_seq_tendsto.2 fun u hu ↦ (h u hu).tendsto }

end MeasureTheory
