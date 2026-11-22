/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# Spatial derivatives of symbols in a direction

The coordinate spatial derivatives `∂_{x_j}` of a symbol (`TauCeti.Symbol.spatialDeriv`) combine
into the spatial derivative in an arbitrary direction `v`,
`∂_{x, v} a = ∑ⱼ vⱼ ∂_{x_j} a` (`TauCeti.Symbol.lineSpatialDeriv`). It is a symbol of the same
order, whose coefficient at `(x, ξ)` is the derivative of `y ↦ a(y, ξ)` at `x` in the direction
`v` (`TauCeti.Symbol.coefficient_lineSpatialDeriv`), and it preserves estimates uniform in the
position (`TauCeti.Symbol.IsUniform.lineSpatialDeriv`).
-/

public section

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The spatial derivative `∂_{x, v} a = ∑ⱼ vⱼ ∂_{x_j} a` of a symbol in the direction `v`, again
a symbol of order `m`. -/
def lineSpatialDeriv (v : CoordinateSpace n) : Symbol n V W m →ₗ[ℂ] Symbol n V W m :=
  ∑ j, ((v j : ℝ) : ℂ) • spatialDeriv j

theorem lineSpatialDeriv_apply (v : CoordinateSpace n) (a : Symbol n V W m) :
    lineSpatialDeriv v a = ∑ j, ((v j : ℝ) : ℂ) • spatialDeriv j a := by
  simp only [lineSpatialDeriv, LinearMap.sum_apply, LinearMap.smul_apply]

/-- `∂_{x, v} a (x, ξ)` is the derivative of `y ↦ a(y, ξ)` at `x` in the direction `v`. -/
@[simp]
theorem coefficient_lineSpatialDeriv (v : CoordinateSpace n) (a : Symbol n V W m)
    (x ξ : CoordinateSpace n) :
    (lineSpatialDeriv v a).coefficient (x, ξ) = fderiv ℝ (fun y ↦ a.coefficient (y, ξ)) x v := by
  simp only [lineSpatialDeriv_apply, coefficient_sum, Finset.sum_apply, coefficient_smul,
    Pi.smul_apply]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    fderiv_coefficient_single, Complex.coe_smul]

theorem IsUniform.lineSpatialDeriv {a : Symbol n V W m} (ha : a.IsUniform)
    (v : CoordinateSpace n) : (lineSpatialDeriv v a).IsUniform := by
  rw [lineSpatialDeriv_apply]
  exact IsUniform.sum fun j _ ↦ (ha.spatialDeriv j).smul _

end Symbol

end TauCeti
