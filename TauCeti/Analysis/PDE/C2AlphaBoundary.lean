/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Domains with `C^{2,α}` boundary

A set `Ω ⊆ ℝ^{n+1}` has `C^{2,α}` boundary (`TauCeti.PDE.HasC2AlphaBoundary`) if near each point
`x` of its frontier it is the region above the graph of a `C^{2,α}` function: there are a radius
`r > 0`, a unit vector `ν` and a `C²` function `γ`, invariant under translation along `ν`, with
`‖Dγ‖`, `‖D²γ‖` and the `α`-Hölder constant of `D²γ` bounded by some `G`, such that

`Ω ∩ B(x, r) = {y | γ y < ⟪y, ν⟫} ∩ B(x, r)`.

Such a chart also describes the closure and the frontier of `Ω` near `x`: inside `B(x, r)` they are
the region `{y | γ y ≤ ⟪y, ν⟫}` on or above the graph and the graph `{y | γ y = ⟪y, ν⟫}`
(`TauCeti.closure_inter_eq_setOf_le_real_inner_inter`,
`TauCeti.frontier_inter_eq_setOf_eq_real_inner_inter`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (domains with `C^{k,α}` boundary).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal InnerProductSpace

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- A set `Ω ⊆ ℝ^{n+1}` has **`C^{2,α}` boundary** if near each point `x` of its frontier it is the
region `{y | γ y < ⟪y, ν⟫}` above the graph of a function `γ` over the hyperplane `ν^⊥`: there are a
radius `r > 0`, a unit vector `ν` and a `C²` function `γ`, invariant under translation along `ν`,
with `‖Dγ‖`, `‖D²γ‖` and the `α`-Hölder constant of `D²γ` bounded by some `G`, such that
`Ω ∩ B(x, r) = {y | γ y < ⟪y, ν⟫} ∩ B(x, r)`. -/
@[expose] def HasC2AlphaBoundary (α : ℝ≥0) (Ω : Set E) : Prop :=
  ∀ x ∈ frontier Ω, ∃ r > 0, ∃ ν : E, ‖ν‖ = 1 ∧ ∃ γ : E → ℝ, ∃ G : ℝ≥0,
    ContDiff ℝ 2 γ ∧ (∀ y (t : ℝ), γ (y + t • ν) = γ y) ∧ (∀ y, ‖fderiv ℝ γ y‖ ≤ G) ∧
    (∀ y, ‖fderiv ℝ (fderiv ℝ γ) y‖ ≤ G) ∧ HolderWith G α (fderiv ℝ (fderiv ℝ γ)) ∧
    Ω ∩ ball x r = {y | γ y < ⟪y, ν⟫_ℝ} ∩ ball x r

end TauCeti.PDE
