/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeomorphism.Discrete
public import TauCeti.Geometry.Diffeomorphism.LieGroup

/-!
# Evaluation on diffeomorphism groups: the circle and two points

Two examples of evaluation `Diff(M) → M`, `g ↦ g x₀`, at a point of a closed manifold.

* `M = S¹`, the unit circle in `ℂ`. Evaluation at `1` is the trivial bundle with fibre the
  stabilizer `Diff(S¹, 1)`: `Diff(S¹) ≃ₜ S¹ × Diff(S¹, 1)`. Its section sends `z` to the rotation
  `x ↦ z * x` by the angle of `z`, the left translation of the Lie group `S¹`
  (`TauCeti.Lie.diffeomorphHomeomorphProdStabilizer`).
* `M` two points, a manifold modelled on the zero-dimensional space. The swap of the two points is
  a diffeomorphism, so the orbit of each point is all of `M`, and only the identity fixes a point
  (`Diffeomorph.orbit_eq_univ_of_discreteTopology`,
  `Diffeomorph.stabilizer_eq_bot_of_natCard_eq_two`).
-/

open MulAction Set
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

noncomputable section

/-- Evaluation `Diff(S¹) → S¹` at `1` is a trivial bundle with fibre `Diff(S¹, 1)`. -/
example : (Circle ≃ₘ^∞⟮𝓡 1, 𝓡 1⟯ Circle) ≃ₜ
    Circle × stabilizer (Circle ≃ₘ^∞⟮𝓡 1, 𝓡 1⟯ Circle) (1 : Circle) :=
  TauCeti.Lie.diffeomorphHomeomorphProdStabilizer (𝓡 1) ∞ 1

/-- The trivialization of `Diff(S¹)` evaluates at `1`. -/
example (g : Circle ≃ₘ^∞⟮𝓡 1, 𝓡 1⟯ Circle) :
    (TauCeti.Lie.diffeomorphHomeomorphProdStabilizer (𝓡 1) ∞ 1 g).1 = g 1 := by
  simp

/-- The section of evaluation at `1` on the circle sends `z` to the rotation by the angle of `z`. -/
example (z x : Circle) : TauCeti.Lie.leftTranslationSection (𝓡 1) (∞ : ℕ∞ω) (1 : Circle) z x =
    z * x := by
  simp

attribute [local instance] ChartedSpace.ofDiscreteTopology

/-- On two points every point has the whole manifold as orbit under diffeomorphisms. -/
example : orbit (Fin 2 ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 0)), 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))⟯ Fin 2)
    (0 : Fin 2) = univ :=
  Diffeomorph.orbit_eq_univ_of_discreteTopology _ _ 0

/-- On two points only the identity fixes a point. -/
example : stabilizer
    (Fin 2 ≃ₘ^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 0)), 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))⟯ Fin 2)
      (0 : Fin 2) = ⊥ :=
  Diffeomorph.stabilizer_eq_bot_of_natCard_eq_two _ _ (by simp) 0

end
