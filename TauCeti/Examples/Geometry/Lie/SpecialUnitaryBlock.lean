/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Unitary.Special
public import TauCeti.Analysis.Matrix.Exponential.Block
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.CartanThreeForm
public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary
public import TauCeti.RepresentationTheory.SU2.LieGroup

/-!
# Checks: the root homomorphism `SU(2) → SU(3)` of the root `ε₁ - ε₂`

For a compact simply connected semisimple group `K`, a root `α` of a maximal torus has a rank-one
representative `f : SU(2) → K` whose differential sends `diag(i, -i)` to the coroot `α^∨`, and the
Cartan three-form detects `f` on `π₃`. For `K = SU(3)`, with matrices indexed by `Fin 2 ⊕ Fin 1`,
its diagonal torus and the root `α = ε₁ - ε₂`, the representative is the block inclusion
`f(g) = diag(g, 1)` of `SU(2)` onto the upper-left `2 × 2` block. The Lie-algebra side of this
check, the block inclusion `𝔰𝔲(2) → 𝔰𝔲(3)` (`TauCeti.specialUnitaryBlockInclusion`) and the value
`-3` of the pulled-back Cartan three-form, is in `TauCeti.Examples.Algebra.Lie.Unitary.Special`.
This file checks the group side.

* `SU(3)` is a compact Lie group: the special unitary subgroup of `GL(3, ℂ)` is closed, so the
  closed-subgroup theorem makes it a Lie group modelled on its Lie algebra
  (`TauCeti.SU3.embeddedLieSubgroupData`), as for `SU(2)`
  (`TauCeti.SU2.embeddedLieSubgroupData`).
* The block inclusion `g ↦ diag(g, 1)` is a continuous homomorphism `SU(2) → SU(3)`
  (`TauCeti.suTwoBlockHom`), hence smooth by automatic smoothness
  (`TauCeti.suTwoBlockSmoothHom`).
* **Its differential is the block inclusion of Lie algebras**: in the matrix coordinates of the
  two general linear Lie algebras, `df(X) = diag(X, 0)`
  (`TauCeti.unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_suTwoBlockSmoothHom`), which is
  `TauCeti.specialUnitaryBlockInclusion` on `𝔰𝔲(2)`. Both sides are read off the one-parameter
  subgroups: `diag(exp(t X), 1) = exp(t diag(X, 0))`.
* So `df(diag(i, -i)) = diag(i, -i, 0) = α^∨`, the differential is injective, and since `𝔰𝔲(2)` is
  not abelian the Cartan three-form of `𝔰𝔲(3)` pulls back to a nonzero form on `𝔰𝔲(2)`. Hence `f`
  is not null-homotopic (`ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap`): it
  represents a nonzero element of `π₃(SU(3))`.

## Implementation notes

`SU(3)` is given the Lie group structure of the closed subgroup `TauCeti.GLSpecialUnitary` of
`GL(3, ℂ)`, with the operator-norm topology on matrices, exactly as `SU(2)` is in
`TauCeti.RepresentationTheory.SU2.LieGroup`. Both groups then sit in the Lie groups of units of
matrix algebras, where the exponential is the matrix exponential
(`TauCeti.Lie.EmbeddedLieSubgroupData.coe_lieExp_smul`), and differentials are computed on
one-parameter subgroups. The smooth structure `Matrix.specialUnitaryGroup.instLieGroup` lives on
Mathlib's matrix carrier with the `ℓ²` operator norm instead, so it is not used here.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, Theorem 12.4, Proposition 12.5
  and Remark 12.6.
-/

public section

noncomputable section

open Matrix Complex
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing
-- Use the operator-norm topology under which `GL(n, ℂ)` is a Lie group, as in
-- `TauCeti.RepresentationTheory.SU2.LieGroup`.
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar
  TauCeti.normedAlgebraRatOfReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

open scoped Matrix.Norms.Operator

/-! ### `SU(3)` as a compact Lie group -/

namespace SU3

/-- The Lie algebra `𝔰𝔲(3)` of `SU(3)`: the Lie algebra of the special unitary subgroup of the real
Lie group `GL(3, ℂ)`, with matrices indexed by `Fin 2 ⊕ Fin 1`. -/
abbrev lieAlgebra :
    LieSubalgebra ℝ (LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ)
      (Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ)ˣ) :=
  Lie.lieSubalgebraOfSubgroup
    (GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ : Subgroup (Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ)ˣ)

/-- **`SU(3)` is a Lie group.** The structure of embedded Lie subgroup of `GL(3, ℂ)` that the
closed-subgroup theorem gives the closed subgroup `SU(3)`, with model space its Lie algebra
`𝔰𝔲(3)`. -/
def embeddedLieSubgroupData :
    Lie.EmbeddedLieSubgroupData 𝓘(ℝ, Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ)
      (GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ) lieAlgebra.toSubmodule :=
  Lie.EmbeddedLieSubgroupData.ofIsClosed (isClosed_GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ)

/-- The charts of `SU(3)` from its embedded Lie subgroup structure. -/
instance : ChartedSpace lieAlgebra.toSubmodule (GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ) :=
  embeddedLieSubgroupData.chartedSpace

/-- `SU(3)` is a Lie group, modelled on `𝔰𝔲(3)`. -/
instance : LieGroup 𝓘(ℝ, lieAlgebra.toSubmodule) ∞ (GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ) :=
  embeddedLieSubgroupData.lieGroup

/-- `SU(3)` is compact, for the operator-norm topology. -/
instance instCompactSpaceOperatorNorm : CompactSpace (GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ) :=
  GLSpecialUnitary.instCompactSpace

end SU3

/-! ### The block inclusion `SU(2) → SU(3)` -/

/-- The block inclusion `A ↦ diag(A, 1)` of `2 × 2` matrices into `3 × 3` matrices, a monoid
homomorphism. -/
private def blockOneMonoidHom :
    Matrix (Fin 2) (Fin 2) ℂ →* Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ where
  toFun A := fromBlocks A 0 0 1
  map_one' := fromBlocks_one
  map_mul' A B := by simp [fromBlocks_multiply]

@[simp]
private theorem blockOneMonoidHom_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    blockOneMonoidHom A = fromBlocks A 0 0 1 :=
  (rfl)

/-- The block inclusion of matrices is continuous: it is `fromBlocks A 0 0 0` plus a constant,
and `A ↦ fromBlocks A 0 0 0` is linear on a finite-dimensional space. -/
private theorem continuous_blockOneMonoidHom : Continuous blockOneMonoidHom := by
  have h : (blockOneMonoidHom : Matrix (Fin 2) (Fin 2) ℂ → _) = fun A ↦
      fromBlocks₁₁NonUnitalStarAlgHom ℝ ℂ (Fin 2) (Fin 1) A + fromBlocks 0 0 0 1 := by
    ext A : 1
    simp [fromBlocks_add]
  rw [h]
  exact (LinearMap.continuous_of_finiteDimensional
    (fromBlocks₁₁NonUnitalStarAlgHom ℝ ℂ (Fin 2) (Fin 1) :
      Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ)).add
    continuous_const

/-- The block inclusion `diag(g, 1)` of a special unitary matrix is special unitary. -/
private theorem units_map_blockOneMonoidHom_mem (g : GLSpecialUnitary (Fin 2) ℂ) :
    Units.map blockOneMonoidHom (g : GL (Fin 2) ℂ) ∈ GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ := by
  have hg := GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup.mp g.property
  rw [GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup, Units.coe_map,
    blockOneMonoidHom_apply]
  exact ⟨fromBlocks_zero_zero_mem_unitary_iff.2 ⟨hg.1, one_mem _⟩,
    by simpa [det_fromBlocks_zero₂₁] using hg.2⟩

/-- **The block inclusion `SU(2) → SU(3)`**, `g ↦ diag(g, 1)`, as a continuous homomorphism. It is
the rank-one homomorphism of the root `ε₁ - ε₂` of the diagonal torus of `SU(3)`. -/
def suTwoBlockHom : GLSpecialUnitary (Fin 2) ℂ →ₜ* GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ where
  toMonoidHom :=
    ((Units.map blockOneMonoidHom).comp (GLSpecialUnitary (Fin 2) ℂ).subtype).codRestrict _
      units_map_blockOneMonoidHom_mem
  continuous_toFun :=
    ((continuous_blockOneMonoidHom.units_map blockOneMonoidHom).comp
      continuous_subtypeVal).subtype_mk _

/-- The matrix of `TauCeti.suTwoBlockHom g` is `diag(g, 1)`. -/
@[simp]
theorem coe_suTwoBlockHom_apply (g : GLSpecialUnitary (Fin 2) ℂ) :
    (((suTwoBlockHom g : GL (Fin 2 ⊕ Fin 1) ℂ)) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ) =
      fromBlocks ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 1 :=
  (rfl)

/-- **The block inclusion `SU(2) → SU(3)` is smooth**, by automatic smoothness of continuous
homomorphisms of Lie groups. -/
def suTwoBlockSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) 𝓘(ℝ, SU3.lieAlgebra.toSubmodule) ∞
      (GLSpecialUnitary (Fin 2) ℂ) (GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ) :=
  suTwoBlockHom.toContMDiffMonoidMorphism _ _

/-- The smooth block inclusion is the continuous one. -/
@[simp]
theorem coe_suTwoBlockSmoothHom : ⇑suTwoBlockSmoothHom = suTwoBlockHom :=
  ContinuousMonoidHom.coe_toContMDiffMonoidMorphism _

/-! ### The differential of the block inclusion -/

/-- **The differential of the block inclusion `SU(2) → SU(3)` is the block inclusion of Lie
algebras**: in the matrix coordinates of the Lie algebras of `GL(2, ℂ)` and `GL(3, ℂ)`, it sends
`X` to `diag(X, 0)`. Both sides generate the one-parameter subgroup
`t ↦ diag(exp(t X), 1) = exp(t diag(X, 0))` of `SU(3)`. -/
theorem unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_suTwoBlockSmoothHom
    (X : LeftInvariantDerivation 𝓘(ℝ, SU2.lieAlgebra.toSubmodule) (GLSpecialUnitary (Fin 2) ℂ)) :
    unitsLieAlgebraEquiv
        (SU3.embeddedLieSubgroupData.lieMapSubtypeVal (lieMap suTwoBlockSmoothHom X)) =
      fromBlocks (unitsLieAlgebraEquiv (SU2.embeddedLieSubgroupData.lieMapSubtypeVal X)) 0 0 0 := by
  apply TauCeti.eq_of_forall_exp_smul_eq
  intro t
  have h3 := SU3.embeddedLieSubgroupData.coe_lieExp_smul (lieMap suTwoBlockSmoothHom X) t
  have h2 := SU2.embeddedLieSubgroupData.coe_lieExp_smul X t
  dsimp only at h3 h2
  rw [← h3, ← map_smul, ← map_lieExp, Lie.EmbeddedLieSubgroupData.subtypeVal_apply,
    coe_suTwoBlockSmoothHom, coe_suTwoBlockHom_apply]
  rw [Lie.EmbeddedLieSubgroupData.subtypeVal_apply] at h2
  rw [h2, fromBlocks_smul, smul_zero, smul_zero, smul_zero]
  -- `Matrix.exp_fromBlocks_diagonal` is stated for the entrywise topology of matrices, which is the
  -- operator-norm topology used here by definition but not syntactically, so it is applied up to
  -- definitional unfolding.
  have hexp := exp_fromBlocks_diagonal
    (t • unitsLieAlgebraEquiv (SU2.embeddedLieSubgroupData.lieMapSubtypeVal X))
    (0 : Matrix (Fin 1) (Fin 1) ℂ)
  rw [NormedSpace.exp_zero] at hexp
  exact hexp.symm

/-- **The differential sends `diag(i, -i)` to the coroot** `α^∨ = diag(i, -i, 0)` of the root
`α = ε₁ - ε₂` of the diagonal torus of `SU(3)`: the rank-one homomorphism of `α` is normalized by
`df(diag(i, -i)) = α^∨`. -/
theorem unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_suTwoBlockSmoothHom_torusGenerator :
    unitsLieAlgebraEquiv (SU3.embeddedLieSubgroupData.lieMapSubtypeVal
        (lieMap suTwoBlockSmoothHom SU2.torusGenerator)) =
      diagonal (Sum.elim ![I, -I] 0) := by
  rw [unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_suTwoBlockSmoothHom,
    ← SU2.coe_nativeLieEquiv_apply, ← SU2.toMatrix_apply,
    SU2.toMatrix_nativeLieEquiv_torusGenerator, ← diagonal_zero, fromBlocks_diagonal, Pi.zero_def]

/-- **The differential of the block inclusion `SU(2) → SU(3)` is injective**, since
`X ↦ diag(X, 0)` is. -/
theorem injective_lieMap_suTwoBlockSmoothHom : Function.Injective (lieMap suTwoBlockSmoothHom) := by
  intro X Y h
  have h' := congrArg
    (fun Z ↦ unitsLieAlgebraEquiv (SU3.embeddedLieSubgroupData.lieMapSubtypeVal Z)) h
  simp only [unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_suTwoBlockSmoothHom] at h'
  exact SU2.embeddedLieSubgroupData.injective_lieMapSubtypeVal
    (unitsLieAlgebraEquiv.injective (fromBlocks_inj.mp h').1)

/-- **The root homomorphism `SU(2) → SU(3)` is not null-homotopic.** Its differential is
injective and `𝔰𝔲(2)` is not abelian, so the Cartan three-form of an invariant inner product on
`𝔰𝔲(3)` pulls back to a nonzero left-invariant volume form on `SU(2) ≅ S³`, whose integral is
nonzero. So `g ↦ diag(g, 1)` represents a nonzero element of `π₃(SU(3))`. -/
theorem not_nullhomotopic_suTwoBlockSmoothHom :
    ¬(suTwoBlockSmoothHom :
      C(GLSpecialUnitary (Fin 2) ℂ, GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ)).Nullhomotopic :=
  suTwoBlockSmoothHom.not_nullhomotopic_of_injective_lieMap SU2.finrank_lieAlgebra
    SU2.not_isLieAbelian_leftInvariantDerivation injective_lieMap_suTwoBlockSmoothHom

end TauCeti
