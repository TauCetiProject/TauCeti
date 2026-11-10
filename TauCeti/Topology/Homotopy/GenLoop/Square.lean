/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
import TauCeti.Topology.Homotopy.Cube.Basic
import TauCeti.Topology.Homotopy.GenLoop.Homotopic

/-!
# Generalized loops of the square given by maps of the plane

An element of `π₂(X, x)` is a homotopy class, relative to the boundary, of maps of the square
`I² = [0, 1]²` sending the boundary to `x` (Mathlib's `GenLoop`). This file reads a map
`u : ℝ × ℝ → X` of the plane which sends the boundary of the unit square to `x` as such a
generalized loop, by restriction to the square, so that maps of the plane built with real
analysis (reparametrizations, smooth approximations) can be compared in `π₂(X, x)`.

## Main declarations

* `TauCeti.squareGenLoop`: the generalized loop `I² → X` at `x` given by a map of the plane
  sending the boundary of the unit square to `x`.
* `TauCeti.squareGenLoop_homotopic`: a homotopy of maps of the plane keeping the boundary of the
  square at `x` is a homotopy of the corresponding generalized loops.
-/

public section

open Set
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- A point of the boundary of the cube `I²`, read as a point of the unit square of the plane, has a
coordinate equal to `0` or `1`. -/
private theorem coe_eq_zero_or_eq_one_of_mem_boundary {y : Fin 2 → I}
    (hy : y ∈ Cube.boundary (Fin 2)) :
    (y 0 : ℝ) = 0 ∨ (y 0 : ℝ) = 1 ∨ (y 1 : ℝ) = 0 ∨ (y 1 : ℝ) = 1 := by
  rcases Cube.boundary_fin_two_iff.1 hy with h | h | h | h <;> simp [h]

/-- The generalized loop `I² → X` at `x` given by a continuous map `u` of the plane sending the
boundary of the unit square to `x`, restricted to the square. Its class is an element of
`π₂(X, x)`. -/
def squareGenLoop (u : ℝ × ℝ → X) (hu : Continuous u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) : Ω^ (Fin 2) X x :=
  ⟨⟨fun y ↦ u ((y 0 : ℝ), (y 1 : ℝ)), by fun_prop⟩, fun _ hy ↦
    hx _ (Subtype.prop _) _ (Subtype.prop _) (coe_eq_zero_or_eq_one_of_mem_boundary hy)⟩

@[simp]
theorem squareGenLoop_apply (u : ℝ × ℝ → X) (hu : Continuous u)
    (hx : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u (s, t) = x) (y : Fin 2 → I) :
    squareGenLoop u hu hx y = u ((y 0 : ℝ), (y 1 : ℝ)) :=
  (rfl)

/-- Two maps of the plane sending the boundary of the unit square to `x` are homotopic as
generalized loops when they are joined by a homotopy which sends the boundary of the square to `x`
at all times. -/
theorem squareGenLoop_homotopic {u₀ u₁ : ℝ × ℝ → X} {hu₀ : Continuous u₀} {hu₁ : Continuous u₁}
    {hx₀ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₀ (s, t) = x}
    {hx₁ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      u₁ (s, t) = x}
    {Φ : I × (ℝ × ℝ) → X} (hΦ : Continuous Φ) (h₀ : ∀ z, Φ (0, z) = u₀ z)
    (h₁ : ∀ z, Φ (1, z) = u₁ z)
    (hΦx : ∀ c, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) →
      Φ (c, (s, t)) = x) :
    GenLoop.Homotopic (squareGenLoop u₀ hu₀ hx₀) (squareGenLoop u₁ hu₁ hx₁) :=
  GenLoop.homotopic_of_continuousMap ⟨fun p ↦ Φ (p.1, ((p.2 0 : ℝ), (p.2 1 : ℝ))), by fun_prop⟩
    (fun _ ↦ h₀ _) (fun _ ↦ h₁ _) fun c _ hy ↦
      hΦx c _ (Subtype.prop _) _ (Subtype.prop _) (coe_eq_zero_or_eq_one_of_mem_boundary hy)

end TauCeti
