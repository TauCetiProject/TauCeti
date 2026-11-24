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
import TauCeti.Analysis.Calculus.GraphFlattening.Direction

/-!
# Domains with `C^{2,α}` boundary

A set `Ω ⊆ ℝ^{n+1}` has `C^{2,α}` boundary (`TauCeti.PDE.HasC2AlphaBoundary`) if near each point
`x` of its frontier it is the region above the graph of a `C^{2,α}` function: there are a radius
`r > 0`, a unit vector `ν` and a `C²` function `γ`, invariant under translation along `ν`, with
`‖Dγ‖`, `‖D²γ‖` and the `α`-Hölder constant of `D²γ` bounded by some `G`, such that

`Ω ∩ B(x, r) = {y | γ y < ⟪y, ν⟫} ∩ B(x, r)`.

Such a chart also describes the closure and the frontier of `Ω` near `x`. If a set `Ω` agrees on
an open set `W` with the region `{y | γ y < ⟪y, ν⟫}` above the graph of a continuous `γ` invariant
along a unit vector `ν`, then on `W` the closure of `Ω` is the region `{y | γ y ≤ ⟪y, ν⟫}` on or
above the graph (`TauCeti.closure_inter_eq_setOf_le_real_inner_inter`), and, for open `Ω`, the
frontier of `Ω` is the graph `{y | γ y = ⟪y, ν⟫}`
(`TauCeti.frontier_inter_eq_setOf_eq_real_inner_inter`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (domains with `C^{k,α}` boundary).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal InnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {Ω W : Set F} {ν : F}
  {γ : F → ℝ}

/-- If `Ω` agrees on an open set `W` with the region `{y | γ y < ⟪y, ν⟫}` above the graph of a
continuous function `γ` invariant along a unit vector `ν`, then on `W` the closure of `Ω` is the
region `{y | γ y ≤ ⟪y, ν⟫}` on or above the graph. -/
theorem closure_inter_eq_setOf_le_real_inner_inter (hW : IsOpen W) (hν : ‖ν‖ = 1)
    (hγ : Continuous γ) (hγν : ∀ y (t : ℝ), γ (y + t • ν) = γ y)
    (hΩW : Ω ∩ W = {y | γ y < ⟪y, ν⟫_ℝ} ∩ W) :
    closure Ω ∩ W = {y | γ y ≤ ⟪y, ν⟫_ℝ} ∩ W := by
  rw [← closure_setOf_lt_real_inner hν hγ hγν]
  refine Subset.antisymm (fun y hy => ⟨?_, hy.2⟩) fun y hy => ⟨?_, hy.2⟩
  · -- `closure Ω ∩ W ⊆ closure (Ω ∩ W)`, the closure of a part of the region above the graph.
    have hy' := hW.closure_inter hy
    rw [hΩW] at hy'
    exact closure_mono inter_subset_left hy'
  · -- `closure {γ < ⟪·, ν⟫} ∩ W ⊆ closure ({γ < ⟪·, ν⟫} ∩ W) = closure (Ω ∩ W)`.
    have hy' := hW.inter_closure ⟨hy.2, hy.1⟩
    rw [inter_comm, ← hΩW] at hy'
    exact closure_mono inter_subset_left hy'

/-- If an open set `Ω` agrees on an open set `W` with the region `{y | γ y < ⟪y, ν⟫}` above the
graph of a continuous function `γ` invariant along a unit vector `ν`, then on `W` the frontier of
`Ω` is the graph `{y | γ y = ⟪y, ν⟫}`. -/
theorem frontier_inter_eq_setOf_eq_real_inner_inter (hΩ : IsOpen Ω) (hW : IsOpen W)
    (hν : ‖ν‖ = 1) (hγ : Continuous γ) (hγν : ∀ y (t : ℝ), γ (y + t • ν) = γ y)
    (hΩW : Ω ∩ W = {y | γ y < ⟪y, ν⟫_ℝ} ∩ W) :
    frontier Ω ∩ W = {y | γ y = ⟪y, ν⟫_ℝ} ∩ W := by
  have hcl := closure_inter_eq_setOf_le_real_inner_inter hW hν hγ hγν hΩW
  ext y
  rw [hΩ.frontier_eq, sdiff_eq, inter_right_comm, mem_inter_iff, hcl]
  constructor
  · rintro ⟨⟨hle, hyW⟩, hyΩ⟩
    exact ⟨hle.antisymm (not_lt.1 fun hlt => hyΩ (hΩW.superset ⟨hlt, hyW⟩).1), hyW⟩
  · rintro ⟨heq, hyW⟩
    exact ⟨⟨(heq : γ y = ⟪y, ν⟫_ℝ).le, hyW⟩, fun hyΩ => (hΩW.subset ⟨hyΩ, hyW⟩).1.ne heq⟩

end TauCeti

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
