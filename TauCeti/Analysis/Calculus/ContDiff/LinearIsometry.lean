/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Smoothness through a closed linear isometric inclusion

For finite orders and `∞`, smoothness can be checked after composing with a linear
isometry whose range is closed. Derivatives remain in the closed range and hence lift,
with their norms and continuity preserved. This gives the smooth alternating-map
pullback needed for differential-form coordinate changes without a characteristic
restriction. The analytic order `ω` is not covered by this criterion.
-/

public section

open Filter Set
open scoped Topology ContDiff
noncomputable section
variable {𝕜 D E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For finite orders and `∞`, a closed linear isometric inclusion reflects smoothness.
No completeness assumption is needed. -/
theorem LinearIsometry.comp_contDiff_iff (i : E →ₗᵢ[𝕜] F)
    (hi : IsClosed (range i)) {f : D → E} {n : ℕ∞} :
    ContDiff 𝕜 n (i ∘ f) ↔ ContDiff 𝕜 n f := by
  constructor
  · rintro ⟨q, hq⟩
    -- Closedness keeps all Taylor derivatives in the range; the lifting lemma
    -- reconstructs a Taylor derivative series for f.
    apply i.exists_hasFTaylorSeriesUpTo_of_comp hq
    intro m hm x v
    exact hq.apply_mem_of_range_subset (S := i.toLinearMap.range) hi
      (by rintro _ ⟨y, rfl⟩; exact ⟨f y, rfl⟩) m hm x v
  · intro h
    exact i.contDiff.comp h
