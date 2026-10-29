/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Topology.Circle.Loop

/-!
# Integral matrices acting on the torus

An invertible integral `2 × 2` matrix `A` acts on the torus `S¹ × S¹` by the monomial
homeomorphism `(a, b) ↦ (a ^ A₀₀ * b ^ A₀₁, a ^ A₁₀ * b ^ A₁₁)`. These are the linear
homeomorphisms of the torus `ℝ² / ℤ²` read in the coordinates `S¹ = ℝ / ℤ`: the map carries the
`(p, q)` curve `TauCeti.torusCurve p q` to the `A (p, q)` curve, so it acts on the first homology
of the torus by `A`. Every homeomorphism of the torus is isotopic to exactly one of them, which is
why gluings of solid tori along their boundary tori, as in Dehn filling, are normally given by such
a matrix.

## Main definitions

* `Matrix.GeneralLinearGroup.torusHomeomorph A`: the homeomorphism of `S¹ × S¹` induced by `A`.

## Main results

* `Matrix.GeneralLinearGroup.torusHomeomorph_one`,
  `Matrix.GeneralLinearGroup.torusHomeomorph_mul`,
  `Matrix.GeneralLinearGroup.symm_torusHomeomorph`: the matrices act through a group action.
* `Matrix.GeneralLinearGroup.torusHomeomorph_torusCurve`: the `(p, q)` curve goes to the
  `A (p, q)` curve.
-/

public section

noncomputable section

open TauCeti

namespace Matrix.GeneralLinearGroup

/-- The monomial self-map of `S¹ × S¹` defined by an integral matrix, invertible or not. -/
private def torusMap (M : Matrix (Fin 2) (Fin 2) ℤ) (q : Circle × Circle) : Circle × Circle :=
  (q.1 ^ M 0 0 * q.2 ^ M 0 1, q.1 ^ M 1 0 * q.2 ^ M 1 1)

private theorem torusMap_torusMap (M N : Matrix (Fin 2) (Fin 2) ℤ) (q : Circle × Circle) :
    torusMap M (torusMap N q) = torusMap (M * N) q := by
  simp only [torusMap, Matrix.mul_apply, Fin.sum_univ_two, mul_zpow, ← zpow_mul', zpow_add]
  exact Prod.ext (mul_mul_mul_comm _ _ _ _) (mul_mul_mul_comm _ _ _ _)

private theorem torusMap_one (q : Circle × Circle) : torusMap 1 q = q := by
  simp [torusMap]

private theorem continuous_torusMap (M : Matrix (Fin 2) (Fin 2) ℤ) : Continuous (torusMap M) := by
  unfold torusMap
  fun_prop

/-- The **homeomorphism of the torus** `S¹ × S¹` induced by an invertible integral `2 × 2` matrix
`A`, `(a, b) ↦ (a ^ A₀₀ * b ^ A₀₁, a ^ A₁₀ * b ^ A₁₁)`
(`Matrix.GeneralLinearGroup.torusHomeomorph_apply`). It carries the `(p, q)` curve to the
`A (p, q)` curve (`Matrix.GeneralLinearGroup.torusHomeomorph_torusCurve`). -/
def torusHomeomorph (A : GL (Fin 2) ℤ) : Circle × Circle ≃ₜ Circle × Circle where
  toFun := torusMap A
  invFun := torusMap ↑A⁻¹
  left_inv q := by rw [torusMap_torusMap, Units.inv_mul, torusMap_one]
  right_inv q := by rw [torusMap_torusMap, Units.mul_inv, torusMap_one]
  continuous_toFun := continuous_torusMap _
  continuous_invFun := continuous_torusMap _

/-- The formula for the homeomorphism of the torus induced by a matrix. -/
@[simp]
theorem torusHomeomorph_apply (A : GL (Fin 2) ℤ) (q : Circle × Circle) :
    A.torusHomeomorph q = (q.1 ^ A 0 0 * q.2 ^ A 0 1, q.1 ^ A 1 0 * q.2 ^ A 1 1) :=
  (rfl)

/-- The identity matrix acts on the torus by the identity. -/
@[simp]
theorem torusHomeomorph_one : (1 : GL (Fin 2) ℤ).torusHomeomorph = Homeomorph.refl _ :=
  Homeomorph.ext torusMap_one

/-- The action of a product of matrices is the composite of their actions. -/
theorem torusHomeomorph_mul (A B : GL (Fin 2) ℤ) :
    (A * B).torusHomeomorph = B.torusHomeomorph.trans A.torusHomeomorph :=
  Homeomorph.ext fun q ↦ (torusMap_torusMap A B q).symm

/-- The inverse of the action of a matrix is the action of the inverse matrix. -/
@[simp]
theorem symm_torusHomeomorph (A : GL (Fin 2) ℤ) : A.torusHomeomorph.symm = A⁻¹.torusHomeomorph :=
  (rfl)

/-- **The action on curves.** The homeomorphism of the torus induced by `A` carries the `(p, q)`
curve `t ↦ (exp (2πipt), exp (2πiqt))` to the `(A₀₀ p + A₀₁ q, A₁₀ p + A₁₁ q)` curve. -/
theorem torusHomeomorph_torusCurve (A : GL (Fin 2) ℤ) (p q : ℤ) (t : unitInterval) :
    A.torusHomeomorph (torusCurve p q t) =
      torusCurve (A 0 0 * p + A 0 1 * q) (A 1 0 * p + A 1 1 * q) t := by
  simp only [torusHomeomorph_apply, torusCurve_apply, ← Circle.exp_zsmul, ← Circle.exp_add,
    zsmul_eq_mul]
  push_cast
  exact Prod.ext (congrArg Circle.exp (by ring)) (congrArg Circle.exp (by ring))

end Matrix.GeneralLinearGroup
