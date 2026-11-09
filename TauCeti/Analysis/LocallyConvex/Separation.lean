/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Convex.Topology

/-!
# Separating two directions by a functional

Two vectors `d₁` and `d₂` of a real locally convex Hausdorff space with `0 ∉ [-d₁, d₂]`, that is,
both nonzero and not on a common ray from `0`, are separated by a continuous functional `ℓ` with
`ℓ d₁ < 0 < ℓ d₂`. This is the geometric Hahn--Banach theorem
`geometric_hahn_banach_point_closed` applied to the point `0` and the segment `[-d₁, d₂]`. Both
strict inequalities are open conditions, so `ℓ` can moreover be perturbed to be nonzero at any
prescribed nonzero vector, along a functional not vanishing there.

## Main results

* `TauCeti.exists_strongDual_neg_pos_ne_zero`: a functional negative on `d₁`, positive on `d₂`,
  and nonzero at a prescribed vector `u`.
-/

public section

open Set Topology

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- Two vectors with `0 ∉ [-d₁, d₂]`, that is nonzero and not on a common ray from `0`, are
separated by a continuous functional which is negative on `d₁` and positive on `d₂`; it can be
chosen nonzero at any prescribed nonzero vector `u`. -/
theorem exists_strongDual_neg_pos_ne_zero {d₁ d₂ : E} (h : (0 : E) ∉ segment ℝ (-d₁) d₂)
    {u : E} (hu : u ≠ 0) :
    ∃ ℓ : StrongDual ℝ E, ℓ d₁ < 0 ∧ 0 < ℓ d₂ ∧ ℓ u ≠ 0 := by
  obtain ⟨f, c, hf0, hfc⟩ := geometric_hahn_banach_point_closed (convex_segment _ _)
    (isCompact_segment ℝ _ _).isClosed h
  have h₁ : f d₁ < 0 := by linarith [map_zero f, map_neg f d₁, hfc _ (left_mem_segment ℝ _ _)]
  have h₂ : 0 < f d₂ := by linarith [map_zero f, hfc _ (right_mem_segment ℝ _ _)]
  by_cases hfu : f u = 0
  · -- Perturb `f` by a small nonzero multiple of a functional `ℓ₀` with `ℓ₀ u ≠ 0`.
    obtain ⟨ℓ₀, hℓ₀⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hu
    have hc (x : E) : ContinuousAt (fun ε : ℝ => (f + ε • ℓ₀) x) 0 := by fun_prop
    have hev : ∀ᶠ ε : ℝ in 𝓝 0, (f + ε • ℓ₀) d₁ < 0 ∧ 0 < (f + ε • ℓ₀) d₂ :=
      ((hc d₁).eventually_lt continuousAt_const (by simpa using h₁)).and
        (continuousAt_const.eventually_lt (hc d₂) (by simpa using h₂))
    obtain ⟨ε, ⟨hε₁, hε₂⟩, hε⟩ :=
      ((hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists (f := 𝓝[≠] 0)
    exact ⟨f + ε • ℓ₀, hε₁, hε₂, by simpa [hfu, hℓ₀] using hε⟩
  · exact ⟨f, h₁, h₂, hfu⟩

end TauCeti
