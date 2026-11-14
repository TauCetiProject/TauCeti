/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.NormalizedDeterminant

/-!
# Normalized determinants of loops of operators

A continuous loop `P` of invertible complex-linear endomorphisms of a complex normed space has a
loop `δ` in the circle of normalized determinants, `det (P t) = ‖det (P t)‖ δ t`
(`TauCeti.exists_path_det_eq_norm_mul`). Its degree is the winding number of the loop of
determinants, the quantity that enters the product axiom of the Maslov index
(`TauCeti.TotallyRealLoop.maslovIndex_map`).

The loop `δ` is the loop of determinant phases `ContinuousLinearMap.detPhase` of `P`.
-/

public section

open scoped unitInterval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every continuous loop `P` of invertible complex-linear endomorphisms has a circle loop `δ` of
normalized determinants, `det (P t) = ‖det (P t)‖ δ t`, as required by
`TauCeti.TotallyRealLoop.maslovIndex_map`. -/
theorem exists_path_det_eq_norm_mul {P : I → E →L[ℂ] E} (hP : Continuous P)
    (hP01 : P 0 = P 1) (hdet : ∀ t, LinearMap.det (P t : E →ₗ[ℂ] E) ≠ 0) :
    ∃ (x : Circle) (δ : Path x x), ∀ t,
      LinearMap.det (P t : E →ₗ[ℂ] E) = ‖LinearMap.det (P t : E →ₗ[ℂ] E)‖ * δ t := by
  refine ⟨(P 0).detPhase, ⟨⟨fun t ↦ (P t).detPhase,
    ContinuousLinearMap.continuous_detPhase hP hdet⟩, rfl, by simp only [hP01]⟩, fun t => ?_⟩
  rw [Path.coe_mk_mk]
  exact (P t).det_eq_norm_mul_detPhase

end TauCeti
