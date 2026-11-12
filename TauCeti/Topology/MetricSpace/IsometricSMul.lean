/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Isometric subgroup actions and displacement estimates

A submonoid or subgroup of a monoid acting by isometries acts by isometries through the
restricted action. Mathlib registers the restricted action itself, but not this property of it;
these instances let theorems about isometric actions apply directly to a subgroup, for example to
a discrete subgroup of `PSL(2, ℝ)` acting on the upper half-plane.

For a group acting by isometries, `TauCeti.dist_conj_smul` computes the displacement of a point
`y` by a conjugate `σ g σ⁻¹`: it is the displacement of `σ⁻¹ • y` by `g`.
The product and commutator displacement bounds control short elements of isometric actions.
-/

public section

variable {M X : Type*} [PseudoEMetricSpace X]

/-- A submonoid of a monoid acting by isometries acts by isometries. -/
@[to_additive /-- An additive submonoid of an additive monoid acting by isometries acts by
isometries. -/]
instance Submonoid.isIsometricSMul [MulOneClass M] [SMul M X] [IsIsometricSMul M X]
    (S : Submonoid M) : IsIsometricSMul S X :=
  ⟨fun s ↦ isometry_smul X (s : M)⟩

/-- A subgroup of a group acting by isometries acts by isometries. -/
@[to_additive /-- An additive subgroup of an additive group acting by isometries acts by
isometries. -/]
instance Subgroup.isIsometricSMul [Group M] [SMul M X] [IsIsometricSMul M X]
    (S : Subgroup M) : IsIsometricSMul S X :=
  ⟨fun s ↦ isometry_smul X (s : M)⟩

namespace TauCeti

open scoped commutatorElement

/-- In a group acting by isometries, a conjugate `σ g σ⁻¹` moves `y` as far as `g` moves
`σ⁻¹ • y`. -/
theorem dist_conj_smul {G Y : Type*} [Group G] [PseudoMetricSpace Y] [MulAction G Y]
    [IsIsometricSMul G Y] (σ g : G) (y : Y) :
    dist ((σ * g * σ⁻¹) • y) y = dist (g • σ⁻¹ • y) (σ⁻¹ • y) := by
  rw [← dist_smul σ⁻¹, mul_smul, mul_smul, inv_smul_smul]

/-- The displacement by a product is at most the sum of the two displacements. -/
theorem dist_mul_smul_le {G Y : Type*} [Monoid G] [PseudoMetricSpace Y] [MulAction G Y]
    [IsIsometricSMul G Y] (g h : G) (y : Y) :
    dist ((g * h) • y) y ≤ dist (g • y) y + dist (h • y) y := by
  simpa only [mul_smul, dist_smul, add_comm] using
    dist_triangle (g • h • y) (g • y) y

/-- A commutator moves a point by at most twice the sum of the factor displacements. -/
theorem dist_commutatorElement_smul_le {G Y : Type*} [Group G] [PseudoMetricSpace Y]
    [MulAction G Y] [IsIsometricSMul G Y] (g h : G) (y : Y) :
    dist (⁅g, h⁆ • y) y ≤ 2 * (dist (g • y) y + dist (h • y) y) := by
  have hg : dist (g⁻¹ • y) y = dist (g • y) y := by
    rw [← dist_smul g, smul_inv_smul, dist_comm]
  have hh : dist (h⁻¹ • y) y = dist (h • y) y := by
    rw [← dist_smul h, smul_inv_smul, dist_comm]
  have h₁ := dist_mul_smul_le (g * h * g⁻¹) h⁻¹ y
  have h₂ := dist_mul_smul_le (g * h) g⁻¹ y
  have h₃ := dist_mul_smul_le g h y
  rw [hg] at h₂
  rw [hh] at h₁
  rw [commutatorElement_def]
  linarith

end TauCeti
