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

* `TauCeti.MapsSquareBoundaryTo u x`: the map `u` of the plane sends the boundary of the unit
  square to `x`. `TauCeti.MapsSquareBoundaryTo.edges` restates this as the constancy of `u` along
  the edges of the square.
* `TauCeti.squareGenLoop`: the generalized loop `I² → X` at `x` given by a map of the plane
  sending the boundary of the unit square to `x`.
* `TauCeti.exists_squareGenLoop_eq`: every generalized loop of the square is of this form.
* `TauCeti.squareGenLoop_homotopic`: a homotopy of maps of the plane keeping the boundary of the
  square at `x` is a homotopy of the corresponding generalized loops.
-/

public section

open Set
open scoped unitInterval Topology.Homotopy

namespace TauCeti

variable {X : Type*} {x : X}

/-- A map `u` of the plane sends the boundary of the unit square `[0, 1]²` to `x`. -/
@[expose] def MapsSquareBoundaryTo (u : ℝ × ℝ → X) (x : X) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) → u (s, t) = x

/-- A map sending the boundary of the unit square to a point is constant along the left, the right
and, from bottom to top, the horizontal edges of the square. -/
theorem MapsSquareBoundaryTo.edges {u : ℝ × ℝ → X} (hx : MapsSquareBoundaryTo u x) :
    (∀ t ∈ Icc (0 : ℝ) 1, u (0, t) = u (0, 0)) ∧ (∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (1, 0)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun s hs ↦ ?_⟩ <;>
    rw [hx _ (by assumption) _ (by assumption) (by simp), hx _ (by assumption) _ h0 (by simp)]

variable [TopologicalSpace X]

/-- A point of the boundary of the cube `I²`, read as a point of the unit square of the plane, has a
coordinate equal to `0` or `1`. -/
private theorem coe_eq_zero_or_eq_one_of_mem_boundary {y : Fin 2 → I}
    (hy : y ∈ Cube.boundary (Fin 2)) :
    (y 0 : ℝ) = 0 ∨ (y 0 : ℝ) = 1 ∨ (y 1 : ℝ) = 0 ∨ (y 1 : ℝ) = 1 := by
  rcases Cube.boundary_fin_two_iff.1 hy with h | h | h | h <;> simp [h]

/-- The generalized loop `I² → X` at `x` given by a continuous map `u` of the plane sending the
boundary of the unit square to `x`, restricted to the square. Its class is an element of
`π₂(X, x)`. -/
def squareGenLoop (u : ℝ × ℝ → X) (hu : Continuous u) (hx : MapsSquareBoundaryTo u x) :
    Ω^ (Fin 2) X x :=
  ⟨⟨fun y ↦ u ((y 0 : ℝ), (y 1 : ℝ)), by fun_prop⟩, fun _ hy ↦
    hx _ (Subtype.prop _) _ (Subtype.prop _) (coe_eq_zero_or_eq_one_of_mem_boundary hy)⟩

@[simp]
theorem squareGenLoop_apply (u : ℝ × ℝ → X) (hu : Continuous u) (hx : MapsSquareBoundaryTo u x)
    (y : Fin 2 → I) :
    squareGenLoop u hu hx y = u ((y 0 : ℝ), (y 1 : ℝ)) :=
  (rfl)

/-- Every generalized loop of the square is `squareGenLoop` of a map of the plane, its extension
clamping both coordinates to `[0, 1]`. -/
theorem exists_squareGenLoop_eq (p : Ω^ (Fin 2) X x) :
    ∃ (u : ℝ × ℝ → X) (hu : Continuous u) (hx : MapsSquareBoundaryTo u x),
      squareGenLoop u hu hx = p := by
  refine ⟨fun z ↦ p ![projIcc 0 1 zero_le_one z.1, projIcc 0 1 zero_le_one z.2],
    p.1.continuous.comp (continuous_pi fun i ↦ ?_), fun s _ t _ h ↦
      p.2 _ (Cube.boundary_fin_two_iff.2 (by rcases h with rfl | rfl | rfl | rfl <;> simp)), ?_⟩
  · fin_cases i
    · exact (continuous_projIcc (h := zero_le_one)).comp continuous_fst
    · exact (continuous_projIcc (h := zero_le_one)).comp continuous_snd
  · exact GenLoop.ext _ _ fun y ↦ congrArg p (funext fun i ↦ by fin_cases i <;> simp)

/-- Two maps of the plane sending the boundary of the unit square to `x` are homotopic as
generalized loops when they are joined by a homotopy which sends the boundary of the square to `x`
at all times. -/
theorem squareGenLoop_homotopic {u₀ u₁ : ℝ × ℝ → X} {hu₀ : Continuous u₀} {hu₁ : Continuous u₁}
    {hx₀ : MapsSquareBoundaryTo u₀ x} {hx₁ : MapsSquareBoundaryTo u₁ x}
    {Φ : I × (ℝ × ℝ) → X} (hΦ : Continuous Φ) (h₀ : ∀ z, Φ (0, z) = u₀ z)
    (h₁ : ∀ z, Φ (1, z) = u₁ z) (hΦx : ∀ c, MapsSquareBoundaryTo (fun z ↦ Φ (c, z)) x) :
    GenLoop.Homotopic (squareGenLoop u₀ hu₀ hx₀) (squareGenLoop u₁ hu₁ hx₁) :=
  GenLoop.homotopic_of_continuousMap ⟨fun p ↦ Φ (p.1, ((p.2 0 : ℝ), (p.2 1 : ℝ))), by fun_prop⟩
    (fun _ ↦ h₀ _) (fun _ ↦ h₁ _) fun c _ hy ↦
      hΦx c _ (Subtype.prop _) _ (Subtype.prop _) (coe_eq_zero_or_eq_one_of_mem_boundary hy)

end TauCeti
