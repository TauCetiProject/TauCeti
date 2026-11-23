/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.KreinMilman

/-!
# Extreme points maximizing a continuous linear functional

In a Hausdorff locally convex real space, a continuous linear functional `l` attains its maximum
on a nonempty compact set `s` at an extreme point of `s`
(`IsCompact.exists_mem_extremePoints_isMaxOn`), and likewise its minimum
(`IsCompact.exists_mem_extremePoints_isMinOn`). The maximizers of `l` form a compact exposed
subset of `s`, which has an extreme point by the Krein–Milman lemma
(`IsCompact.extremePoints_nonempty`), and extreme points of an extreme subset are extreme points
of `s`.

For a polytope this says that a linear functional is minimized at a vertex. This is what makes the
normal cones at the vertices of a polytope cover the whole space.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Section 32 (maxima of
  convex functions at extreme points, in finite dimension).
-/

public section

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}

/-- A continuous linear functional attains its maximum on a nonempty compact set at an extreme
point of the set. -/
theorem IsCompact.exists_mem_extremePoints_isMaxOn (hs : IsCompact s) (hne : s.Nonempty)
    (l : StrongDual ℝ E) : ∃ x ∈ s.extremePoints ℝ, IsMaxOn l s x := by
  obtain ⟨x₀, hx₀, hmax⟩ := hs.exists_isMaxOn hne l.continuous.continuousOn
  -- The maximizers of `l` form a nonempty compact exposed subset of `s`.
  have hexp : IsExposed ℝ s (l.toExposed s) := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨x, hx⟩ := (hexp.isCompact hs).extremePoints_nonempty ⟨x₀, hx₀, fun w hw ↦ hmax hw⟩
  exact ⟨x, hexp.isExtreme.extremePoints_subset_extremePoints hx,
    fun w hw ↦ (extremePoints_subset hx).2 w hw⟩

/-- A continuous linear functional attains its minimum on a nonempty compact set at an extreme
point of the set. -/
theorem IsCompact.exists_mem_extremePoints_isMinOn (hs : IsCompact s) (hne : s.Nonempty)
    (l : StrongDual ℝ E) : ∃ x ∈ s.extremePoints ℝ, IsMinOn l s x := by
  obtain ⟨x, hx, hmax⟩ := hs.exists_mem_extremePoints_isMaxOn hne (-l)
  exact ⟨x, hx, fun w hw ↦ by simpa using hmax hw⟩
