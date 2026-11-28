/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Exponential.Block
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Exponential.OneParameter
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary

/-!
# The block inclusion of special unitary Lie groups and its differential

For finite index types `n` and `m`, the block inclusion `g ↦ diag(g, 1)` of the special unitary
group of `n × n` matrices into that of `(n ⊕ m) × (n ⊕ m)` matrices
(`TauCeti.GLSpecialUnitary.fromBlocksInl`) is a continuous homomorphism of Lie groups, hence
smooth by automatic smoothness (`TauCeti.GLSpecialUnitary.fromBlocksInlSmoothHom`). Its
differential is the block inclusion of Lie algebras: in the matrix coordinates of the two general
linear Lie algebras it sends `X` to `diag(X, 0)`
(`TauCeti.GLSpecialUnitary.unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom`).
Both sides are read off the one-parameter subgroups: `diag(exp(t X), 1) = exp(t diag(X, 0))`. In
particular the differential is injective
(`TauCeti.GLSpecialUnitary.injective_lieMap_fromBlocksInlSmoothHom`).

The Lie groups are the closed subgroups `TauCeti.GLSpecialUnitary` of the general linear groups,
with the operator-norm topology on matrices
(`TauCeti.GLSpecialUnitary.embeddedLieSubgroupData`), where the exponential is the matrix
exponential (`TauCeti.Lie.EmbeddedLieSubgroupData.coe_lieExp_smul`).

## Main definitions

* `TauCeti.GLSpecialUnitary.fromBlocksInlSmoothHom`: the block inclusion `g ↦ diag(g, 1)`, as a
  smooth homomorphism of Lie groups.

## Main results

* `TauCeti.GLSpecialUnitary.unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom`:
  its differential is `X ↦ diag(X, 0)` in matrix coordinates.
* `TauCeti.GLSpecialUnitary.injective_lieMap_fromBlocksInlSmoothHom`: its differential is
  injective.
-/

public section

noncomputable section

open Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace TauCeti.GLSpecialUnitary

attribute [local instance 100] LieRing.ofAssociativeRing
-- Use the operator-norm topology under which `GL n 𝕜` is a Lie group, and the rational algebra
-- structure under which its Lie exponential is the matrix exponential.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable (n 𝕜 m : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜] [Fintype m] [DecidableEq m]

/-- **The block inclusion `g ↦ diag(g, 1)` of special unitary groups is smooth**, by automatic
smoothness of the continuous homomorphism `TauCeti.GLSpecialUnitary.fromBlocksInl` of Lie
groups. -/
def fromBlocksInlSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, (lieAlgebra n 𝕜).toSubmodule)
      𝓘(ℝ, (lieAlgebra (n ⊕ m) 𝕜).toSubmodule) ∞ (GLSpecialUnitary n 𝕜)
      (GLSpecialUnitary (n ⊕ m) 𝕜) :=
  -- `TauCeti.GLSpecialUnitary.fromBlocksInl` is continuous for the entrywise topology of
  -- matrices, which is the operator-norm topology used here by definition but not syntactically.
  ContinuousMonoidHom.toContMDiffMonoidMorphism _ _
    { toMonoidHom := (fromBlocksInl n 𝕜 m).toMonoidHom
      continuous_toFun := (fromBlocksInl n 𝕜 m).continuous }

variable {n 𝕜 m}

/-- The smooth block inclusion is the continuous one. -/
@[simp]
theorem coe_fromBlocksInlSmoothHom : ⇑(fromBlocksInlSmoothHom n 𝕜 m) = fromBlocksInl n 𝕜 m :=
  ContinuousMonoidHom.coe_toContMDiffMonoidMorphism _

/-- **The differential of the block inclusion `g ↦ diag(g, 1)` is the block inclusion of Lie
algebras**: in the matrix coordinates of the Lie algebras of the general linear groups, it sends
`X` to `diag(X, 0)`. Both sides generate the one-parameter subgroup
`t ↦ diag(exp(t X), 1) = exp(t diag(X, 0))`. -/
theorem unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom
    (X : LeftInvariantDerivation 𝓘(ℝ, (lieAlgebra n 𝕜).toSubmodule) (GLSpecialUnitary n 𝕜)) :
    unitsLieAlgebraEquiv ((embeddedLieSubgroupData (n ⊕ m) 𝕜).lieMapSubtypeVal
        (lieMap (fromBlocksInlSmoothHom n 𝕜 m) X)) =
      fromBlocks (unitsLieAlgebraEquiv ((embeddedLieSubgroupData n 𝕜).lieMapSubtypeVal X))
        0 0 0 := by
  apply TauCeti.eq_of_forall_exp_smul_eq
  intro t
  have h₁ := (embeddedLieSubgroupData (n ⊕ m) 𝕜).coe_lieExp_smul
    (lieMap (fromBlocksInlSmoothHom n 𝕜 m) X) t
  have h₀ := (embeddedLieSubgroupData n 𝕜).coe_lieExp_smul X t
  dsimp only at h₁ h₀
  rw [← h₁, ← map_smul, ← map_lieExp, Lie.EmbeddedLieSubgroupData.subtypeVal_apply,
    coe_fromBlocksInlSmoothHom, coe_fromBlocksInl_apply]
  rw [Lie.EmbeddedLieSubgroupData.subtypeVal_apply] at h₀
  rw [h₀, fromBlocks_smul, smul_zero, smul_zero, smul_zero]
  -- `Matrix.exp_fromBlocks_diagonal` is stated for the entrywise topology of matrices, which is the
  -- operator-norm topology used here by definition but not syntactically, so it is applied up to
  -- definitional unfolding.
  have hexp := exp_fromBlocks_diagonal
    (t • unitsLieAlgebraEquiv ((embeddedLieSubgroupData n 𝕜).lieMapSubtypeVal X))
    (0 : Matrix m m 𝕜)
  rw [NormedSpace.exp_zero] at hexp
  exact hexp.symm

/-- **The differential of the block inclusion `g ↦ diag(g, 1)` is injective**, since
`X ↦ diag(X, 0)` is. -/
theorem injective_lieMap_fromBlocksInlSmoothHom :
    Function.Injective (lieMap (fromBlocksInlSmoothHom n 𝕜 m)) := by
  intro X Y h
  have h' := congrArg
    (fun Z ↦ unitsLieAlgebraEquiv ((embeddedLieSubgroupData (n ⊕ m) 𝕜).lieMapSubtypeVal Z)) h
  simp only [unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom] at h'
  exact (embeddedLieSubgroupData n 𝕜).injective_lieMapSubtypeVal
    (unitsLieAlgebraEquiv.injective (fromBlocks_inj.mp h').1)

end TauCeti.GLSpecialUnitary
