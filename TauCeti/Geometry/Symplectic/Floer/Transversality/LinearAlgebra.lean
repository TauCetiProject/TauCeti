/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.SymmetricInterpolation
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Linear algebra for localized Floer transversality

For `L = SJ - JS - a - bJ` and `L z = 0`, rotating `z` gives
`L(J z) = 2b z - 2a Jz`. Consequently the correction
`(α, β, ξ) ↦ (α - 2tb, β + 2ta, ξ - tJz)` preserves the expression
`L ξ - (α + βJ)z`. When `J` preserves a symmetric bilinear form and `z` is
nonisotropic, choose `t` to make the corrected vector orthogonal to `Jz`.
It is then the value at `z` of a symmetric complex-linear map.

These are the pointwise algebraic steps in Floer--Hofer--Salamon,
*Transversality in elliptic Morse theory for the symplectic action*,
Duke Math. J. 80 (1995), 251--292. They do not assert an analytic range
or generic-regularity theorem. Symmetry of `S` is not needed for these identities.
-/

public section

namespace TauCeti.Floer

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The scalar-shifted commutator occurring in the pointwise Floer transversality argument. -/
def transversalityLinearMap (J : AlmostComplexStructure V) (S : V →ₗ[ℝ] V) (a b : ℝ) :
    V →ₗ[ℝ] V :=
  S.comp J.toLinearMap - J.toLinearMap.comp S - a • LinearMap.id - b • J.toLinearMap

@[simp]
theorem transversalityLinearMap_apply (J : AlmostComplexStructure V) (S : V →ₗ[ℝ] V)
    (a b : ℝ) (v : V) :
    transversalityLinearMap J S a b v = S (J v) - J (S v) - a • v - b • J v := (rfl)

/-- The value of the shifted commutator on the complex rotation of a kernel vector. -/
theorem transversalityLinearMap_apply_apply_of_apply_eq_zero (J : AlmostComplexStructure V)
    (S : V →ₗ[ℝ] V) (a b : ℝ) {z : V}
    (hz : transversalityLinearMap J S a b z = 0) :
    transversalityLinearMap J S a b (J z) = (2 * b) • z - (2 * a) • J z := by
  have hJ := congrArg J hz
  simp only [transversalityLinearMap_apply, J.apply_sub,
    J.apply_smul, J.apply_apply, J.apply_zero] at hJ
  simp only [transversalityLinearMap_apply, J.apply_apply, map_neg, smul_neg]
  linear_combination (norm := module) -hJ

/-- Moving a vector along the complex rotation of a kernel vector can be compensated by
changing the two scalar variables, leaving the transversality expression unchanged. -/
theorem transversalityLinearMap_sub_smul_apply_sub_eq (J : AlmostComplexStructure V)
    (S : V →ₗ[ℝ] V) (a b : ℝ) {z : V}
    (hz : transversalityLinearMap J S a b z = 0) (α β t : ℝ) (ξ : V) :
    transversalityLinearMap J S a b (ξ - t • J z) -
        ((α - 2 * t * b) • z + (β + 2 * t * a) • J z) =
      transversalityLinearMap J S a b ξ - (α • z + β • J z) := by
  rw [map_sub, map_smul, transversalityLinearMap_apply_apply_of_apply_eq_zero J S a b hz]
  module

/-- A transversality expression at a nonisotropic kernel vector can always be represented
using the value of a self-adjoint complex-linear endomorphism. The scalar variables are
corrected at the same time; no orthogonality assumption on the original vector is needed. -/
theorem exists_isAdjointPair_isComplexLinearMap_transversalityLinearMap_sub_eq
    (J : AlmostComplexStructure V) (S : V →ₗ[ℝ] V) (a b : ℝ)
    {g : LinearMap.BilinForm ℝ V} (hg : g.IsSymm)
    (hgJ : ∀ v w, g (J v) (J w) = g v w) {z : V} (hzz : g z z ≠ 0)
    (hz : transversalityLinearMap J S a b z = 0) (α β : ℝ) (ξ : V) :
    ∃ (α' β' : ℝ) (A : V →ₗ[ℝ] V), LinearMap.IsAdjointPair g g A A ∧
      IsComplexLinearMap J J A ∧
      transversalityLinearMap J S a b (A z) - (α' • z + β' • J z) =
        transversalityLinearMap J S a b ξ - (α • z + β • J z) := by
  let t := g ξ (J z) / g z z
  have horth : g (ξ - t • J z) (J z) = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hgJ]
    dsimp [t]
    field_simp
    ring
  obtain ⟨A, hA, hAJ, hAz⟩ :=
    J.exists_isAdjointPair_isComplexLinearMap_apply_eq hg hgJ hzz horth
  refine ⟨α - 2 * t * b, β + 2 * t * a, A, hA, hAJ, ?_⟩
  rw [hAz]
  exact transversalityLinearMap_sub_smul_apply_sub_eq J S a b hz α β t ξ

end TauCeti.Floer
