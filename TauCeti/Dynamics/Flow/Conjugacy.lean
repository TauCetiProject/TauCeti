/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow

/-!
# Conjugacies of flows

This file collects general consequences of a homeomorphism that semiconjugates two flows.

## Main declarations

* `Homeomorph.tendsto_flow_iff`: a homeomorphic semiconjugacy transports convergence of flow
  trajectories in either direction.
* `Homeomorph.map_flow_symm`: the inverse of a homeomorphic semiconjugacy satisfies the
  conjugacy equation in the reverse direction.
-/

public section

open Filter Topology

namespace Homeomorph

variable {τ α β : Type*} [TopologicalSpace τ] [TopologicalSpace α] [TopologicalSpace β]
  [AddMonoid τ] {φ : _root_.Flow τ α} {ψ : _root_.Flow τ β} (e : α ≃ₜ β)

/-- A homeomorphic semiconjugacy transports convergence of flow trajectories in either direction. -/
theorem tendsto_flow_iff (hconj : _root_.Flow.IsSemiconjugacy e φ ψ) {l : Filter τ}
    {x y : α} :
    Tendsto (fun t ↦ ψ t (e y)) l (𝓝 (e x)) ↔ Tendsto (fun t ↦ φ t y) l (𝓝 x) := by
  constructor
  · intro h
    apply e.isInducing.tendsto_nhds_iff.mpr
    refine Filter.Tendsto.congr' (f₂ := e ∘ fun t ↦ φ t y)
      (Eventually.of_forall fun t ↦ by
        simpa only [Function.comp_apply] using (hconj.semiconj t y).symm) h
  · intro h
    have h' : Tendsto (e ∘ fun t ↦ φ t y) l (𝓝 (e x)) :=
      e.isInducing.tendsto_nhds_iff.mp h
    refine Filter.Tendsto.congr' (f₂ := fun t ↦ ψ t (e y))
      (Eventually.of_forall fun t ↦ by
        simpa only [Function.comp_apply] using hconj.semiconj t y) h'

/-- The inverse of a homeomorphic semiconjugacy is a semiconjugacy in the reverse direction. -/
theorem map_flow_symm (hconj : _root_.Flow.IsSemiconjugacy e φ ψ) (t : τ) (y : β) :
    e.symm (ψ t y) = φ t (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply, hconj.semiconj t, e.apply_symm_apply]

end Homeomorph
