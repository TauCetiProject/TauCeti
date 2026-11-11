/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow

/-!
# Conjugacies of flows

This file transports flows along homeomorphisms and collects general consequences of an inducing
map that intertwines two flows. These lemmas transport asymptotic trajectory behavior, enabling
stable and unstable sets to be transferred through coordinate conjugacies.

## Main declarations

* `Homeomorph.conjFlow`: the flow `e ∘ φ t ∘ e.symm` transported along a homeomorphism `e`.
* `Homeomorph.isSemiconjugacy_conjFlow`: `e` semiconjugates a flow to its transport.
* `Topology.IsInducing.tendsto_flow_iff`: an inducing map intertwining two flows transports
  convergence of flow trajectories in either direction.
* `Homeomorph.tendsto_flow_iff`: a homeomorphic semiconjugacy transports convergence of flow
  trajectories in either direction.
* `Homeomorph.map_flow_symm`: the inverse of a homeomorphic semiconjugacy satisfies the
  conjugacy equation in the reverse direction.
-/

public section

open Filter Topology

variable {τ α β : Type*} [TopologicalSpace τ] [TopologicalSpace α] [TopologicalSpace β]

section AddZero

variable [AddZero τ]

/-- An inducing map `f` intertwining two flows, `f (φ t y) = ψ t (f y)`, transports convergence of
flow trajectories in either direction. The map need not be surjective, so this also applies to the
inclusion of an invariant subset. -/
theorem Topology.IsInducing.tendsto_flow_iff {φ : _root_.Flow τ α} {ψ : _root_.Flow τ β}
    {f : α → β} (hf : IsInducing f) (hconj : ∀ t, Function.Semiconj f (φ t) (ψ t))
    {l : Filter τ} {x y : α} :
    Tendsto (fun t ↦ ψ t (f y)) l (𝓝 (f x)) ↔ Tendsto (fun t ↦ φ t y) l (𝓝 x) := by
  -- The trajectory of `f y` under `ψ` is the image under `f` of the trajectory of `y` under `φ`.
  have h : (fun t ↦ ψ t (f y)) = f ∘ fun t ↦ φ t y := funext fun t ↦ (hconj t y).symm
  rw [h, ← hf.tendsto_nhds_iff]

end AddZero

namespace Homeomorph

variable (e : α ≃ₜ β)

section AddZero

variable [AddZero τ]

/-- The flow `e ∘ φ t ∘ e.symm` obtained by transporting a flow `φ` along a homeomorphism `e`. -/
def conjFlow (φ : _root_.Flow τ α) : _root_.Flow τ β where
  toFun t y := e (φ t (e.symm y))
  cont' := e.continuous.comp (φ.continuous continuous_fst (e.symm.continuous.comp continuous_snd))
  map_add' t₁ t₂ y := by simp [φ.map_add]
  map_zero' y := by simp

@[simp]
theorem conjFlow_apply (φ : _root_.Flow τ α) (t : τ) (y : β) :
    e.conjFlow φ t y = e (φ t (e.symm y)) :=
  (rfl)

end AddZero

variable [AddMonoid τ] {φ : _root_.Flow τ α} {ψ : _root_.Flow τ β}

/-- A homeomorphism `e` semiconjugates a flow `φ` to its transport `e.conjFlow φ`. -/
theorem isSemiconjugacy_conjFlow (φ : _root_.Flow τ α) :
    _root_.Flow.IsSemiconjugacy e φ (e.conjFlow φ) :=
  ⟨e.continuous, e.surjective, fun t x ↦ by simp⟩

/-- A homeomorphic semiconjugacy transports convergence of flow trajectories in either direction. -/
theorem tendsto_flow_iff (hconj : _root_.Flow.IsSemiconjugacy e φ ψ) {l : Filter τ}
    {x y : α} :
    Tendsto (fun t ↦ ψ t (e y)) l (𝓝 (e x)) ↔ Tendsto (fun t ↦ φ t y) l (𝓝 x) :=
  e.isInducing.tendsto_flow_iff hconj.semiconj

/-- The inverse of a homeomorphic semiconjugacy satisfies the semiconjugacy equation in the
reverse direction. -/
theorem map_flow_symm (hconj : _root_.Flow.IsSemiconjugacy e φ ψ) (t : τ) (y : β) :
    e.symm (ψ t y) = φ t (e.symm y) :=
  (hconj.semiconj t).inverse_left e.symm_apply_apply e.apply_symm_apply y

end Homeomorph
