/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Sets with `C^{2,α}` boundary

A set `Ω` in a real inner product space has `C^{2,α}` boundary (`Set.HasC2HolderBoundary Ω α`) if
near every point of `frontier Ω`, in some ball, `Ω` is the region `{x | γ x < ⟪x, ν⟫}` above the
graph of a `C^{2,α}` function `γ` over the hyperplane `ν^⊥`. These are the domains of the global
Schauder theory (Gilbarg–Trudinger, Section 6.2). Such a set is open
(`Set.HasC2HolderBoundary.isOpen`). The geometry of the region above a graph near the boundary is
in `TauCeti/Analysis/InnerProductSpace/GraphPatch.lean`, and the global Schauder estimate on such a
domain is in `TauCeti/Analysis/PDE/Regularity/Hessian/Schauder/BoundedDomain.lean`.
-/

public section

open Metric
open scoped InnerProductSpace NNReal

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A set `Ω` has **`C^{2,α}` boundary** if near every point `z` of its frontier, in some ball
`B(z, r)`, it is the region `{x | γ x < ⟪x, ν⟫}` above the graph of a `C^{2,α}` function over the
hyperplane `ν^⊥`: `ν` is a unit vector and `γ` is a `C²` function invariant along `ν` whose first
and second derivatives are bounded by `G` and whose second derivative is `α`-Hölder with
constant `G`. -/
def HasC2HolderBoundary (Ω : Set E) (α : ℝ≥0) : Prop :=
  ∀ z ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
    ContDiff ℝ 2 γ ∧ (∀ x (t : ℝ), γ (x + t • ν) = γ x) ∧ (∀ x, ‖fderiv ℝ γ x‖ ≤ G) ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
    Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r

/-- A set has `C^{2,α}` boundary exactly when every frontier point has a ball in which the set is
the region above the graph of a `C^{2,α}` function. -/
theorem hasC2HolderBoundary_iff {Ω : Set E} {α : ℝ≥0} :
    Ω.HasC2HolderBoundary α ↔ ∀ z ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ),
      ‖ν‖ = 1 ∧ ContDiff ℝ 2 γ ∧ (∀ x (t : ℝ), γ (x + t • ν) = γ x) ∧
      (∀ x, ‖fderiv ℝ γ x‖ ≤ G) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G) ∧
      HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧ 0 < r ∧
      Ω ∩ ball z r = {x | γ x < ⟪x, ν⟫_ℝ} ∩ ball z r :=
  Iff.rfl

/-- A set with `C^{2,α}` boundary is open: near each frontier point it agrees with the open region
above the graph of a continuous function, so none of its frontier points belongs to it. -/
theorem HasC2HolderBoundary.isOpen {Ω : Set E} {α : ℝ≥0} (h : Ω.HasC2HolderBoundary α) :
    IsOpen Ω := by
  refine disjoint_frontier_iff_isOpen.1 (disjoint_left.2 fun z hz hzΩ => hz.2 ?_)
  obtain ⟨ν, γ, -, r, -, hγ, -, -, -, -, hr, hΩr⟩ := h z hz
  have hopen : IsOpen (Ω ∩ ball z r) := by
    rw [hΩr]
    exact (isOpen_lt hγ.continuous (continuous_id.inner continuous_const)).inter isOpen_ball
  exact interior_maximal inter_subset_left hopen ⟨hzΩ, mem_ball_self hr⟩

end Set
