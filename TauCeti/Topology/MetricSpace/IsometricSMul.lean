/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Isometric actions: subgroups, completions, continuity and displacement estimates

A submonoid or subgroup of a monoid acting by isometries acts by isometries through the
restricted action. Mathlib registers the restricted action itself, but not this property of it;
these instances let theorems about isometric actions apply directly to a subgroup, for example to
a discrete subgroup of `PSL(2, ℝ)` acting on the upper half-plane.

An isometric action fixing `0` of a seminormed group preserves the norm. An isometric action is
uniformly continuous in the point, so it extends to the completion
(`UniformSpace.Completion`), where it is again isometric. If the action of a topological monoid
on the original space is jointly continuous, so is the extended action: the orbit maps
`c ↦ c • x` of the dense set of points of the original space are continuous, and each `c • ·` is
`1`-Lipschitz, which is the criterion `continuous_prod_of_dense_continuous_lipschitzWith'`. This
is how a Galois group acting isometrically on a valued field acts continuously on its completion,
as for `ℂ_p`.

For a group acting by isometries, `TauCeti.dist_conj_smul` computes the displacement of a point
`y` by a conjugate `σ g σ⁻¹`: it is the displacement of `σ⁻¹ • y` by `g`.
The product and commutator displacement bounds control short elements of isometric actions.

A group acting by isometries maps to the isometry group `X ≃ᵢ X` by the monoid homomorphism
`IsometryEquiv.constSMulHom`, sending `c` to `IsometryEquiv.constSMul c`; it is injective when
the action is faithful (`IsometryEquiv.constSMulHom_injective`).
-/

public section

variable {M X : Type*} [PseudoEMetricSpace X]

/-- An isometric action is uniformly continuous in the point. -/
@[to_additive /-- An isometric additive action is uniformly continuous in the point. -/]
instance (priority := 100) IsIsometricSMul.to_uniformContinuousConstSMul [SMul M X]
    [IsIsometricSMul M X] : UniformContinuousConstSMul M X :=
  ⟨fun c ↦ (isometry_smul X c).uniformContinuous⟩

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

/-- An isometric action fixing `0` preserves the norm. -/
@[simp]
theorem IsIsometricSMul.norm_smul {E : Type*} [SeminormedAddGroup E] [SMulZeroClass M E]
    [IsIsometricSMul M E] (c : M) (x : E) : ‖c • x‖ = ‖x‖ := by
  simpa using dist_smul c x 0

namespace UniformSpace.Completion

/-- The extension of an isometric action to the completion is isometric. -/
@[to_additive /-- The extension of an isometric additive action to the completion is
isometric. -/]
instance instIsIsometricSMul {X : Type*} [PseudoMetricSpace X] [SMul M X] [IsIsometricSMul M X] :
    IsIsometricSMul M (Completion X) :=
  ⟨fun c ↦ (isometry_smul X c).completion_map⟩

/-- **The completion of a jointly continuous isometric action is jointly continuous.** -/
@[to_additive /-- **The completion of a jointly continuous isometric additive action is jointly
continuous.** -/]
instance continuousSMul_of_isIsometricSMul {X : Type*} [TopologicalSpace M] [PseudoMetricSpace X]
    [SMul M X] [IsIsometricSMul M X] [ContinuousSMul M X] : ContinuousSMul M (Completion X) := by
  -- the orbit maps of the dense set of points of `X` are continuous, and each `c • ·` is
  -- `1`-Lipschitz
  refine ⟨continuous_prod_of_dense_continuous_lipschitzWith' _ 1 (denseRange_coe (α := X))
    (fun c ↦ (isometry_smul (Completion X) c).lipschitzWith) ?_⟩
  rintro _ ⟨y, rfl⟩
  simp_rw [← coe_smul]
  exact (continuous_coe X).comp (continuous_id.smul continuous_const)

end UniformSpace.Completion

namespace IsometryEquiv

variable (G Y : Type*) [PseudoEMetricSpace Y] [Group G] [MulAction G Y] [IsIsometricSMul G Y]

/-- A group acting on `Y` by isometries acts through the monoid homomorphism `G →* (Y ≃ᵢ Y)`
sending `c` to the isometry `IsometryEquiv.constSMul c : y ↦ c • y`. -/
def constSMulHom : G →* (Y ≃ᵢ Y) where
  toFun := constSMul
  map_one' := ext (one_smul G)
  map_mul' c c' := ext (mul_smul c c')

/-- `IsometryEquiv.constSMulHom G Y c` is the isometry `IsometryEquiv.constSMul c`. -/
@[simp]
theorem constSMulHom_apply (c : G) : constSMulHom G Y c = constSMul c :=
  (rfl)

/-- For a faithful action, `IsometryEquiv.constSMulHom` is injective: distinct elements of `G`
act by distinct isometries. -/
theorem constSMulHom_injective [FaithfulSMul G Y] : Function.Injective (constSMulHom G Y) :=
  fun _ _ h ↦ eq_of_smul_eq_smul fun y ↦ DFunLike.congr_fun h y

end IsometryEquiv

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
