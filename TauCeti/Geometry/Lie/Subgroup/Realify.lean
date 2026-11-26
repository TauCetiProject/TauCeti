/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Basic
public import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# The realified `GL(n, ℂ)` and `U(n)` as Lie subgroups of `GL(2n, ℝ)`

Realification `Matrix.GeneralLinearGroup.realify n ℂ` embeds `GL(n, ℂ)` in the real Lie group
`GL(2n, ℝ) = GL (n ⊕ n) ℝ` as the closed subgroup `C_ℝ = (realify n ℂ).range` of invertible real
matrices commuting with `J` (`Matrix.GeneralLinearGroup.mem_range_realify_iff`), and `U(n)` as
the orthogonal symplectic matrices `Sp(2n, ℝ) ∩ O(2n)`. By the closed-subgroup theorem `C_ℝ` is an
embedded Lie subgroup of `GL(2n, ℝ)` (`TauCeti.Lie.isEmbeddedLieSubgroup_range_realify`), as are
`Sp(2n, ℝ)` (`TauCeti.Lie.isEmbeddedLieSubgroup_GLSymplectic`) and `Sp(2n, ℝ) ∩ O(2n)`
(`TauCeti.Lie.isEmbeddedLieSubgroup_GLSymplectic_inf_unitarySubgroup`). This file computes the Lie
algebra of `C_ℝ` and identifies `C_ℝ` and `Sp(2n, ℝ) ∩ O(2n)` with `GL(n, ℂ)` and `U(n)` as Lie
groups.

The Lie algebra of `C_ℝ` consists of the real matrices commuting with `J`, which are exactly the
realified complex matrices: an exponential line `t ↦ exp (t A)` commutes with `J` exactly when
its generator `A` does (`TauCeti.forall_commute_exp_smul_iff`).

Realification is an isomorphism of topological groups from `GL(n, ℂ)` onto `C_ℝ`
(`Matrix.GeneralLinearGroup.realifyEquivRange`) and from `U(n)` onto `Sp(2n, ℝ) ∩ O(2n)`
(`Matrix.unitaryGroupEquivSymplecticInfOrthogonal`). A continuous homomorphism of
finite-dimensional real Lie groups is smooth (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`), so
for every Lie group structure on the target, such as the one given by the closed-subgroup theorem,
both isomorphisms are diffeomorphisms. Here `GL(n, ℂ)` carries its structure as the group of units
of the real normed algebra of complex matrices, and `U(n)` its structure as an embedded Lie
subgroup of `GL(n, ℂ)` (`TauCeti.Lie.matrixUnitaryLieGroup`).

## Main results

* `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff`:
  **the Lie algebra of the realified `GL(n, ℂ)` is the matrices commuting with `J`**, and
  `TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff_exists`:
  it is the realified complex matrices.
* `TauCeti.Lie.isEmbeddedLieSubgroup_range_realify`: the realified `GL(n, ℂ)` is an embedded Lie
  subgroup of `GL(2n, ℝ)`.
* `Matrix.GeneralLinearGroup.realifyDiffeomorphRange`: realification is a diffeomorphism from
  `GL(n, ℂ)` onto its image.
* `Matrix.unitarySubgroupDiffeomorphSymplecticInfOrthogonal`: realification is a diffeomorphism
  from `U(n)` onto `Sp(2n, ℝ) ∩ O(2n)`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  Graduate Texts in Mathematics 27, Oxford University Press, 2017, Section 2.2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator

-- Select the matrix topology underlying the operator norm used for the general linear Lie group,
-- together with continuity of the conjugate transpose for it, as for the unitary Lie group.
-- Use the normed scalar instance's seminormed parent consistently in native matrix models.
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

namespace TauCeti.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Lie algebra of the realified `GL(n, ℂ)` is the matrices commuting with `J`.** In the
canonical matrix coordinates of the general linear Lie algebra, a real matrix belongs to the Lie
algebra of the image of `GL(n, ℂ)` under realification exactly when it commutes with `J`. -/
-- Normalize membership before the Lie equivalence simplifies to its linear equivalence.
@[simp↓]
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (n ⊕ n) (n ⊕ n) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ))
          (Matrix.GeneralLinearGroup.realify n ℂ).range ↔
      Commute (Matrix.J n ℝ) A := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    (Matrix.GeneralLinearGroup.isClosedEmbedding_realify n ℂ).isClosed_range]
  simp only [Matrix.GeneralLinearGroup.mem_range_realify_iff, TauCeti.expUnit_coe]
  exact forall_commute_exp_smul_iff

/-- The Lie algebra of the realified `GL(n, ℂ)` consists of the realified complex matrices. -/
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff_exists
    (A : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (unitsLieAlgebraLieEquiv (R := Matrix (n ⊕ n) (n ⊕ n) ℝ)).symm A ∈
        lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ))
          (Matrix.GeneralLinearGroup.realify n ℂ).range ↔
      ∃ B : Matrix n n ℂ, B.realify = A := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_range_realify_iff,
    Matrix.commute_J_iff_exists_realify_eq]

/-- **The realified `GL(n, ℂ)` is an embedded Lie subgroup of `GL(2n, ℝ)`**, by the
closed-subgroup theorem. -/
theorem isEmbeddedLieSubgroup_range_realify :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ))
      (Matrix.GeneralLinearGroup.realify n ℂ).range :=
  isEmbeddedLieSubgroup_of_isClosed
    (Matrix.GeneralLinearGroup.isClosedEmbedding_realify n ℂ).isClosed_range

end TauCeti.Lie

namespace Matrix

open TauCeti TauCeti.Lie

variable {n : Type*} [Fintype n] [DecidableEq n]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace GeneralLinearGroup

variable [ChartedSpace H (realify n ℂ).range] [LieGroup I ∞ (realify n ℂ).range]

variable (n I) in
/-- **Realification is a diffeomorphism from `GL(n, ℂ)` onto its image**, for every Lie group
structure on the realified `GL(n, ℂ)`, such as the closed-subgroup structure of
`TauCeti.Lie.isEmbeddedLieSubgroup_range_realify`. It is the topological group isomorphism
`Matrix.GeneralLinearGroup.realifyEquivRange`, which is smooth in both directions. -/
def realifyDiffeomorphRange : GL n ℂ ≃ₘ⟮𝓘(ℝ, Matrix n n ℂ), I⟯ (realify n ℂ).range :=
  -- The ascription reads the topology of `GL n ℂ` as the one of the operator norm.
  ContinuousMulEquiv.toDiffeomorph _ _ (realifyEquivRange n ℂ : GL n ℂ ≃ₜ* (realify n ℂ).range)

/-- The diffeomorphism `GL(n, ℂ) ≃ C_ℝ` is realification. -/
@[simp]
theorem coe_realifyDiffeomorphRange : ⇑(realifyDiffeomorphRange n I) = realifyEquivRange n ℂ :=
  ContinuousMulEquiv.coe_toDiffeomorph _

/-- The inverse of the diffeomorphism `GL(n, ℂ) ≃ C_ℝ` is the inverse of realification. -/
@[simp]
theorem coe_realifyDiffeomorphRange_symm :
    ⇑(realifyDiffeomorphRange n I).symm = (realifyEquivRange n ℂ).symm :=
  (congrArg DFunLike.coe (ContinuousMulEquiv.toDiffeomorph_symm _)).trans
    (ContinuousMulEquiv.coe_toDiffeomorph _)

end GeneralLinearGroup

/-- Realification, as an isomorphism of topological groups from the unitary subgroup of `GL(n, ℂ)`
onto the orthogonal symplectic matrices. -/
private def unitarySubgroupEquivSymplecticInfOrthogonal :
    unitarySubgroup (GL n ℂ) ≃ₜ* ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) :=
  (ContinuousMulEquiv.mk' (unitarySubgroupUnitsHomeomorph (Matrix n n ℂ)) fun U V ↦ by
    simp only [unitarySubgroupUnitsHomeomorph_apply, map_mul]).trans
    unitaryGroupEquivSymplecticInfOrthogonal

private theorem coe_unitarySubgroupEquivSymplecticInfOrthogonal_apply
    (U : unitarySubgroup (GL n ℂ)) :
    (unitarySubgroupEquivSymplecticInfOrthogonal U : GL (n ⊕ n) ℝ) =
      GeneralLinearGroup.realify n ℂ U := by
  -- The unitary element underlying `U` is sent back to `U` by the canonical unitary inclusion.
  have hU : Unitary.toUnits (unitarySubgroupUnitsEquiv U) = (U : GL n ℂ) := by
    rw [← coe_unitarySubgroupUnitsEquiv_symm_apply, MulEquiv.symm_apply_apply]
  have h : unitarySubgroupEquivSymplecticInfOrthogonal U =
      unitaryGroupEquivSymplecticInfOrthogonal (unitarySubgroupUnitsHomeomorph (Matrix n n ℂ) U) :=
    ContinuousMulEquiv.trans_apply _ _ U
  rw [h, unitaryGroupEquivSymplecticInfOrthogonal_apply, unitarySubgroupUnitsHomeomorph_apply, hU]

variable [ChartedSpace H ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))]
  [LieGroup I ∞ ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))]

variable (n I) in
/-- **Realification is a diffeomorphism from `U(n)` onto `Sp(2n, ℝ) ∩ O(2n)`**, for the
structure of `U(n)` as an embedded Lie subgroup of `GL(n, ℂ)` and every Lie group structure on the
orthogonal symplectic matrices. It is the topological group isomorphism
`Matrix.unitaryGroupEquivSymplecticInfOrthogonal`, read on the unitary subgroup of `GL(n, ℂ)`. -/
def unitarySubgroupDiffeomorphSymplecticInfOrthogonal :
    unitarySubgroup (GL n ℂ) ≃ₘ⟮𝓘(ℝ, (lieSubalgebraOfSubgroup
      (I := 𝓘(ℝ, Matrix n n ℂ)) (unitarySubgroup (GL n ℂ))).toSubmodule), I⟯
      ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ)) :=
  unitarySubgroupEquivSymplecticInfOrthogonal.toDiffeomorph _ _

/-- The diffeomorphism `U(n) ≃ Sp(2n, ℝ) ∩ O(2n)` is realification. -/
@[simp]
theorem coe_unitarySubgroupDiffeomorphSymplecticInfOrthogonal_apply
    (U : unitarySubgroup (GL n ℂ)) :
    (unitarySubgroupDiffeomorphSymplecticInfOrthogonal n I U : GL (n ⊕ n) ℝ) =
      GeneralLinearGroup.realify n ℂ U := by
  have h : ⇑(unitarySubgroupDiffeomorphSymplecticInfOrthogonal n I) =
      unitarySubgroupEquivSymplecticInfOrthogonal :=
    ContinuousMulEquiv.coe_toDiffeomorph _
  rw [h, coe_unitarySubgroupEquivSymplecticInfOrthogonal_apply]

/-- The inverse of the diffeomorphism `U(n) ≃ Sp(2n, ℝ) ∩ O(2n)` is inverse to realification. -/
@[simp]
theorem realify_unitarySubgroupDiffeomorphSymplecticInfOrthogonal_symm_apply
    (M : ↥(GLSymplectic n ℝ ⊓ unitarySubgroup (GL (n ⊕ n) ℝ))) :
    GeneralLinearGroup.realify n ℂ
      ((unitarySubgroupDiffeomorphSymplecticInfOrthogonal n I).symm M : GL n ℂ) = M := by
  rw [← coe_unitarySubgroupDiffeomorphSymplecticInfOrthogonal_apply (I := I),
    Diffeomorph.apply_symm_apply]

end Matrix
