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
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Normalized determinants of loops of operators

A continuous loop `P` of invertible complex-linear endomorphisms of a complex normed space has a
loop `δ` in the circle of normalized determinants, `det (P t) = ‖det (P t)‖ δ t`
(`TauCeti.exists_path_det_eq_norm_mul`). Its degree is the winding number of the loop of
determinants, the quantity that enters the product axiom of the Maslov index
(`TauCeti.TotallyRealLoop.maslovIndex_map`).
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
  set d : I → ℂ := fun t => LinearMap.det (P t : E →ₗ[ℂ] E)
  have hd : Continuous d := ContinuousLinearMap.continuous_det.comp hP
  let c : I → Circle := fun t =>
    ⟨d t / ‖d t‖, mem_sphere_zero_iff_norm.2 (by simp [show d t ≠ 0 from hdet t])⟩
  have hc : Continuous c :=
    (hd.div (Complex.continuous_ofReal.comp hd.norm) fun t => by simpa using hdet t).subtype_mk _
  refine ⟨c 0, ⟨⟨c, hc⟩, rfl, ?_⟩, fun t => ?_⟩
  · exact Circle.ext (by simp [c, d, hP01])
  · exact (mul_div_cancel₀ (d t) (by simpa using hdet t)).symm

end TauCeti
