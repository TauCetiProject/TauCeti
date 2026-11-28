/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CartanThreeForm
public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary.Block
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

* `SU(2)` and `SU(3)` are compact Lie groups, modelled on their Lie algebras, as closed subgroups of
  `GL(2, ℂ)` and `GL(3, ℂ)` (`TauCeti.GLSpecialUnitary.embeddedLieSubgroupData`).
* The block inclusion `g ↦ diag(g, 1)` is a smooth homomorphism `SU(2) → SU(3)`
  (`TauCeti.GLSpecialUnitary.fromBlocksInlSmoothHom`), whose differential is, in the matrix
  coordinates of the two general linear Lie algebras, `X ↦ diag(X, 0)`
  (`TauCeti.GLSpecialUnitary.unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom`):
  the same formula as `TauCeti.specialUnitaryBlockInclusion`.
* So `df(diag(i, -i)) = diag(i, -i, 0) = α^∨`
  (`TauCeti.unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom_torusGenerator`).
* `f` is not null-homotopic (`TauCeti.not_nullhomotopic_fromBlocksInlSmoothHom`).
  Its differential is injective and `𝔰𝔲(2)` is not abelian, so the Cartan three-form of an
  invariant inner product on `𝔰𝔲(3)` pulls back to a nonzero left-invariant volume form on
  `SU(2) ≅ S³`, whose integral is nonzero
  (`ContMDiffMonoidMorphism.not_nullhomotopic_of_injective_lieMap`). This is how the Cartan
  three-form detects `f` on `π₃`; the class of `f` in `π₃(SU(3))` itself is not formalized here.

## Implementation notes

`SU(2)` and `SU(3)` are given the Lie group structure of the closed subgroups
`TauCeti.GLSpecialUnitary` of the general linear groups, with the operator-norm topology on
matrices, as in `TauCeti.RepresentationTheory.SU2.LieGroup`. The smooth structure
`Matrix.specialUnitaryGroup.instLieGroup` lives on Mathlib's matrix carrier with the `ℓ²` operator
norm instead, so it is not used here.

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

/-- **The differential of the block inclusion `SU(2) → SU(3)` sends `diag(i, -i)` to the coroot**
`α^∨ = diag(i, -i, 0)` of the root `α = ε₁ - ε₂` of the diagonal torus of `SU(3)`: the rank-one
homomorphism of `α` is normalized by `df(diag(i, -i)) = α^∨`. -/
theorem unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom_torusGenerator :
    unitsLieAlgebraEquiv
        ((GLSpecialUnitary.embeddedLieSubgroupData (Fin 2 ⊕ Fin 1) ℂ).lieMapSubtypeVal
          (lieMap (GLSpecialUnitary.fromBlocksInlSmoothHom (Fin 2) ℂ (Fin 1)) SU2.torusGenerator)) =
      diagonal (Sum.elim ![I, -I] 0) := by
  rw [GLSpecialUnitary.unitsLieAlgebraEquiv_lieMapSubtypeVal_lieMap_fromBlocksInlSmoothHom,
    ← SU2.coe_nativeLieEquiv_apply, ← SU2.toMatrix_apply,
    SU2.toMatrix_nativeLieEquiv_torusGenerator, ← diagonal_zero, fromBlocks_diagonal, Pi.zero_def]

/-- **The root homomorphism `SU(2) → SU(3)`, the block inclusion `g ↦ diag(g, 1)`, is not
null-homotopic.** -/
theorem not_nullhomotopic_fromBlocksInlSmoothHom :
    ¬(GLSpecialUnitary.fromBlocksInlSmoothHom (Fin 2) ℂ (Fin 1) :
      C(GLSpecialUnitary (Fin 2) ℂ, GLSpecialUnitary (Fin 2 ⊕ Fin 1) ℂ)).Nullhomotopic :=
  (GLSpecialUnitary.fromBlocksInlSmoothHom (Fin 2) ℂ (Fin 1)).not_nullhomotopic_of_injective_lieMap
    SU2.finrank_lieAlgebra SU2.not_isLieAbelian_leftInvariantDerivation
    GLSpecialUnitary.injective_lieMap_fromBlocksInlSmoothHom

end TauCeti
